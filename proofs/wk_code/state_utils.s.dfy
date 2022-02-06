include "state.dfy"
include "state_properties_OpsSaneStateSubset.s.dfy"

predicate state_equal_except_mstate(s1:state, s2:state)
{
    s1.subjects == s2.subjects &&
    s1.objects == s2.objects &&
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&
    s1.os_mem_active_map == s2.os_mem_active_map &&
    (true)
}

predicate state_equal_except_mstate_objs(s1:state, s2:state)
{
    s1.subjects == s2.subjects &&
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&
    s1.os_mem_active_map == s2.os_mem_active_map &&
    (true)
}

predicate state_equal_except_mstate_subjs_objs(s1:state, s2:state)
{
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&
    s1.os_mem_active_map == s2.os_mem_active_map &&
    (true)
}

predicate state_equal_except_mstate_subjs_objs_memactivemap(s1:state, s2:state)
{
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&
    (true)
}

predicate state_equal_except_tempgvar_regs_stack(s1:state, s2:state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s1.wk_mstate))
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s2.wk_mstate))
{
    var globals1 := wkm_get_globals(s1.wk_mstate);
    var globals2 := wkm_get_globals(s2.wk_mstate);

    (s1.subjects == s2.subjects) &&
    (s1.objects == s2.objects) &&
    (s1.id_mappings == s2.id_mappings) &&
    (s1.objs_addrs == s2.objs_addrs) &&
    (s1.activate_conds == s2.activate_conds) &&
    (s1.ok == s2.ok) &&
    (s1.os_mem_active_map == s2.os_mem_active_map) &&

    global_non_scratchpad_vars_are_unchanged(globals1, globals2)
}

predicate state_equal_except_tempgvar_regs_stack_counters(s1:state, s2:state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s1.wk_mstate))
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s2.wk_mstate))
{
    var globals1 := wkm_get_globals(s1.wk_mstate);
    var globals2 := wkm_get_globals(s2.wk_mstate);

    (s1.subjects == s2.subjects) &&
    (s1.objects == s2.objects) &&
    (s1.id_mappings == s2.id_mappings) &&
    (s1.objs_addrs == s2.objs_addrs) &&
    (s1.activate_conds == s2.activate_conds) &&
    (s1.ok == s2.ok) &&
    (s1.os_mem_active_map == s2.os_mem_active_map) &&

    global_non_scratchpad_vars_except_counters_are_unchanged(globals1, globals2)
}

predicate WS_SubjRead_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(s:state, s_id:Subject_ID, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires s_id in WSM_AllSubjsIDs(s.subjects)
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall td_id :: td_id in td_ids ==> td_id in WSM_AllTDIDs(s.objects)) &&
    (forall fd_id :: fd_id in fd_ids ==> fd_id in WSM_AllFDIDs(s.objects)) &&
    (forall do_id :: do_id in do_ids ==> do_id in WSM_AllDOIDs(s.objects)) &&

    (forall id :: id in td_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in fd_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in do_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid))
}

predicate WS_SubjWrite_ObjsToReadAndCopiedToMustBeInSamePartitionWithSubj(
    s:state, s_id:Subject_ID, td_id_val_map:set<TD_ID>, fd_id_val_map:set<FD_ID>, do_id_val_map:set<DO_ID>
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires s_id in WSM_AllSubjsIDs(s.subjects)
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall td_id :: td_id in td_id_val_map ==> td_id in WSM_AllTDIDs(s.objects)) &&
    (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in WSM_AllFDIDs(s.objects)) &&
    (forall do_id :: do_id in do_id_val_map ==> do_id in WSM_AllDOIDs(s.objects)) &&

    (forall id :: id in td_id_val_map
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in fd_id_val_map
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in do_id_val_map
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id) == WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid))
}