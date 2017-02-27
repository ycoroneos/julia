// This file is a part of Julia. License is MIT: http://julialang.org/license

/*
  precompile.c
  Generating compiler output artifacts (object files, etc.)
*/

#include <stdlib.h>
#include <assert.h>

#include "julia.h"
#include "julia_internal.h"

#ifdef __cplusplus
extern "C" {
#endif

JL_DLLEXPORT int jl_generating_output(void)
{
    return jl_options.outputo || jl_options.outputbc || jl_options.outputji;
}

void jl_precompile(int all);

void jl_write_compiler_output(void)
{
    if (!jl_generating_output())
        return;

    if (!jl_options.incremental)
        jl_precompile(jl_options.compile_enabled == JL_OPTIONS_COMPILE_ALL);

    if (!jl_module_init_order) {
        jl_printf(JL_STDERR, "WARNING: --output requested, but no modules defined during run\n");
        return;
    }

    jl_array_t *worklist = jl_module_init_order;
    JL_GC_PUSH1(&worklist);
    jl_module_init_order = jl_alloc_vec_any(0);
    int i, l = jl_array_len(worklist);
    for (i = 0; i < l; i++) {
        jl_value_t *m = jl_arrayref(worklist, i);
        if (jl_get_global((jl_module_t*)m, jl_symbol("__init__"))) {
            jl_array_ptr_1d_push(jl_module_init_order, m);
        }
    }

    if (jl_options.incremental) {
        if (jl_options.outputji)
            if (jl_save_incremental(jl_options.outputji, worklist))
                jl_exit(1);
        if (jl_options.outputbc)
            jl_printf(JL_STDERR, "WARNING: incremental output to a .bc file is not implemented\n");
        if (jl_options.outputo)
            jl_printf(JL_STDERR, "WARNING: incremental output to a .o file is not implemented\n");
    }
    else {
        ios_t *s = NULL;
        if (jl_options.outputo || jl_options.outputbc)
            s = jl_create_system_image();

        if (jl_options.outputji) {
            if (s == NULL) {
                jl_save_system_image(jl_options.outputji);
            }
            else {
                ios_t f;
                if (ios_file(&f, jl_options.outputji, 1, 1, 1, 1) == NULL)
                    jl_errorf("cannot open system image file \"%s\" for writing", jl_options.outputji);
                ios_write(&f, (const char*)s->buf, (size_t)s->size);
                ios_close(&f);
            }
        }

        if (jl_options.outputo || jl_options.outputbc)
            jl_dump_native(jl_options.outputbc,
                           jl_options.outputo,
                           (const char*)s->buf, (size_t)s->size);
    }
    JL_GC_POP();
}

static int tupletype_any_bottom(jl_value_t *sig)
{
    sig = jl_unwrap_unionall(sig);
    assert(jl_is_tuple_type(sig));
    jl_svec_t *types = ((jl_tupletype_t*)sig)->types;
    size_t i, l = jl_svec_len(types);
    for (i = 0; i < l; i++) {
        if (jl_svecref(types, i) == jl_bottom_type)
            return 1;
    }
    return 0;
}

// f{<:Union{...}}(...) is a common pattern
// and expanding the Union may give a leaf function
static int _compile_all_tvar_union(jl_value_t *methsig)
{
    if (!jl_is_unionall(methsig) && jl_is_leaf_type(methsig)) {
        // usually can create a specialized version of the function,
        // if the signature is already a leaftype
        if (jl_compile_hint((jl_tupletype_t*)methsig))
            return 1;
    }

    int tvarslen = jl_subtype_env_size(methsig);
    int complete = 1;
    jl_value_t *sigbody = methsig;
    jl_value_t **env;
    JL_GC_PUSHARGS(env, 2 * tvarslen);
    int *idx = (int*)alloca(sizeof(int) * tvarslen);
    int i;
    for (i = 0; i < tvarslen; i++) {
        assert(jl_is_unionall(sigbody));
        idx[i] = 0;
        env[2 * i] = (jl_value_t*)((jl_unionall_t*)sigbody)->var;
        env[2 * i + 1] = jl_bottom_type; // initialize the list with Union{}, since T<:Union{} is always a valid option
        sigbody = ((jl_unionall_t*)sigbody)->body;
    }

    for (i = 0; i < tvarslen; /* incremented by inner loop */) {
        jl_value_t *sig;
        JL_TRY {
            // TODO: wrap in UnionAll for each tvar in env[2*i + 1] ?
            // currently doesn't matter much, since jl_compile_hint doesn't work on abstract types
            sig = (jl_value_t*)jl_instantiate_type_with(sigbody, env, tvarslen);
        }
        JL_CATCH {
            goto getnext; // sigh, we found an invalid type signature. should we warn the user?
        }
        assert(jl_is_tuple_type(sig));
        if (sig == jl_bottom_type || tupletype_any_bottom(sig))
            goto getnext; // signature wouldn't be callable / is invalid -- skip it
        if (jl_is_leaf_type(sig)) {
            if (jl_compile_hint((jl_tupletype_t*)sig))
                goto getnext; // success
        }
        complete = 0;

    getnext:
        for (i = 0; i < tvarslen; i++) {
            jl_tvar_t *tv = (jl_tvar_t*)env[2 * i];
            if (jl_is_uniontype(tv->ub)) {
                size_t l = jl_count_union_components(tv->ub);
                size_t j = idx[i];
                if (j == l) {
                    env[2 * i + 1] = jl_bottom_type;
                    idx[i] = 0;
                }
                else {
                    jl_value_t *ty = jl_nth_union_component(tv->ub, j);
                    if (!jl_is_leaf_type(ty))
                        ty = (jl_value_t*)jl_new_typevar(tv->name, tv->lb, ty);
                    env[2 * i + 1] = ty;
                    idx[i] = j + 1;
                    break;
                }
            }
            else {
                env[2 * i + 1] = (jl_value_t*)tv;
                complete = 0;
            }
        }
    }
    JL_GC_POP();
    return complete;
}

// f(::Union{...}, ...) is a common pattern
// and expanding the Union may give a leaf function
static int _compile_all_union(jl_value_t *sig)
{
    jl_tupletype_t *sigbody = (jl_tupletype_t*)jl_unwrap_unionall(sig);
    int complete = 1;
    size_t count_unions = 0;
    size_t i, l = jl_svec_len(sigbody->parameters);
    jl_svec_t *p = NULL;
    jl_value_t *methsig = NULL;

    for (i = 0; i < l; i++) {
        jl_value_t *ty = jl_svecref(sigbody->parameters, i);
        if (jl_is_uniontype(ty))
            ++count_unions;
        else if (ty == jl_bottom_type)
            return 1; // why does this method exist?
    }

    if (count_unions == 0)
        return _compile_all_tvar_union(sig);

    int *idx = (int*)alloca(sizeof(int) * count_unions);
    for (i = 0; i < count_unions; i++) {
        idx[i] = 0;
    }

    JL_GC_PUSH2(&p, &methsig);
    int idx_ctr = 0, incr = 0;
    while (!incr) {
        jl_svec_t *p = jl_alloc_svec_uninit(l);
        for (i = 0, idx_ctr = 0, incr = 1; i < l; i++) {
            jl_value_t *ty = jl_svecref(sigbody->parameters, i);
            if (jl_is_uniontype(ty)) {
                size_t l = jl_count_union_components(ty);
                size_t j = idx[idx_ctr];
                jl_svecset(p, i, jl_nth_union_component(ty, j));
                ++j;
                if (incr) {
                    if (j == l) {
                        idx[idx_ctr] = 0;
                    }
                    else {
                        idx[idx_ctr] = j;
                        incr = 0;
                    }
                }
                ++idx_ctr;
            }
            else {
                jl_svecset(p, i, ty);
            }
        }
        methsig = (jl_value_t*)jl_apply_tuple_type(p);
        methsig = jl_rewrap_unionall(methsig, sig);
        if (!_compile_all_tvar_union(methsig))
            complete = 0;
    }

    JL_GC_POP();
    return complete;
}

static void _compile_all_deq(jl_array_t *found)
{
    int found_i, found_l = jl_array_len(found);
    jl_printf(JL_STDERR, "found %d uncompiled methods for compile-all\n", (int)found_l);
    jl_method_instance_t *linfo = NULL;
    jl_code_info_t *src = NULL;
    JL_GC_PUSH2(&linfo, &src);
    for (found_i = 0; found_i < found_l; found_i++) {
        if (found_i % (1 + found_l / 300) == 0 || found_i == found_l - 1) // show 300 progress steps, to show progress without overwhelming log files
            jl_printf(JL_STDERR, " %d / %d\r", found_i + 1, found_l);
        jl_typemap_entry_t *ml = (jl_typemap_entry_t*)jl_array_ptr_ref(found, found_i);
        jl_method_t *m = ml->func.method;
        if (m->isstaged)  // TODO: generic implementations of generated functions
            continue;
        linfo = m->unspecialized;
        if (!linfo) {
            linfo = jl_get_specialized(m, (jl_value_t*)m->sig, jl_emptysvec);
            m->unspecialized = linfo;
            jl_gc_wb(m, linfo);
        }

        if (linfo->jlcall_api == 2)
            continue;
        src = m->source;
        // TODO: the `unspecialized` field is not yet world-aware, so we can't store
        // an inference result there.
        //src = jl_type_infer(&linfo, jl_world_counter, 1);
        //m->unspecialized = linfo;
        //jl_gc_wb(m, linfo);
        //if (linfo->jlcall_api == 2)
        //    continue;

        int complete = _compile_all_union((jl_value_t*)ml->sig);
        // if _compile_all_union returns 1, all possible signatures have been covered, so we don't
        // need to compile an unspecialized version.
        if (complete) {
            if (linfo->fptr == NULL && linfo->functionObjectsDecls.functionObject == NULL)
                // indicate that this method doesn't need to be compiled, because it was fully covered above
                // TODO: do this some other way
                linfo->fptr = (jl_fptr_t)(uintptr_t)-1;
        }
        else {
            jl_compile_linfo(&linfo, src, jl_world_counter, &jl_default_cgparams);
            assert(linfo->functionObjectsDecls.functionObject != NULL);
        }
    }
    JL_GC_POP();
    jl_printf(JL_STDERR, "\n");
}

static void foreach_def_in_module(jl_module_t *m, jl_typemap_visitor_fptr visit, jl_array_t *out)
{
    size_t i;
    void **table = m->bindings.table;
    for (i = 1; i < m->bindings.size; i += 2) {
        if (table[i] != HT_NOTFOUND) {
            jl_binding_t *b = (jl_binding_t*)table[i];
            if (b->owner == m && b->value && b->constp) {
                jl_value_t *v = b->value;
                if (jl_is_datatype(v)) {
                    jl_typename_t *tn = ((jl_datatype_t*)v)->name;
                    if (tn->module == m && tn->name == b->name) {
                        jl_methtable_t *mt = tn->mt;
                        if (mt != NULL && (jl_value_t*)mt != jl_nothing) {
                            jl_typemap_visitor(mt->defs, visit, (void*)out);
                        }
                    }
                }
                else if (jl_is_module(v)) {
                    jl_module_t *child = (jl_module_t*)v;
                    if (child != m && child->parent == m && child->name == b->name) {
                        // this is the original/primary binding for the submodule
                        foreach_def_in_module(child, visit, out);
                    }
                }
            }
        }
    }
}

static int _compile_all_enq(jl_typemap_entry_t *ml, void *env)
{
    jl_array_t *found = (jl_array_t*)env;
    // method definition -- compile template field
    jl_method_t *m = ml->func.method;
    if (!m->isstaged &&
        (!m->unspecialized ||
         (m->unspecialized->functionObjectsDecls.functionObject == NULL &&
          m->unspecialized->jlcall_api != 2 &&
          m->unspecialized->fptr == NULL))) {
        // found a lambda that still needs to be compiled
        jl_array_ptr_1d_push(found, (jl_value_t*)ml);
    }
    return 1;
}

static void jl_compile_all_defs(void)
{
    // this "found" array will contain
    // TypeMapEntries for Methods and MethodInstances that need to be compiled
    jl_array_t *m = jl_alloc_vec_any(0);
    JL_GC_PUSH1(&m);
    while (1) {
        foreach_def_in_module(jl_main_module, _compile_all_enq, m);
        size_t changes = jl_array_len(m);
        if (!changes)
            break;
        _compile_all_deq(m);
        jl_array_del_end(m, changes);
    }
    JL_GC_POP();
}

static int _precompile_enq_specialization(jl_typemap_entry_t *l, void *closure)
{
    if (jl_is_method_instance(l->func.value) &&
            l->func.linfo->functionObjectsDecls.functionObject == NULL &&
            l->func.linfo->jlcall_api != 2)
        jl_array_ptr_1d_push((jl_array_t*)closure, (jl_value_t*)l->sig);
    return 1;
}

static int _precompile_enq_all_specializations(jl_typemap_entry_t *def, void *closure)
{
    jl_typemap_visitor(def->func.method->specializations, _precompile_enq_specialization, closure);
    return 1;
}

static void jl_compile_specializations(void)
{
    // this "found" array will contain function
    // type signatures that were inferred but haven't been compiled
    jl_array_t *m = jl_alloc_vec_any(0);
    JL_GC_PUSH1(&m);
    foreach_def_in_module(jl_main_module, _precompile_enq_all_specializations, m);
    size_t i, l;
    for (i = 0, l = jl_array_len(m); i < l; i++) {
        jl_compile_hint((jl_tupletype_t*)jl_array_ptr_ref(m, i));
    }
    JL_GC_POP();
}

void jl_precompile(int all)
{
    if (all)
        jl_compile_all_defs();
    jl_compile_specializations();
}

#ifdef __cplusplus
}
#endif
