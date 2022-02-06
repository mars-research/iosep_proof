include "../../state_properties_OpsSaneStateSubset.s.dfy" 

// Lemma: If <g_wimpdrvs_info> and <g_existing_pids> are unchanged, and 
// WK_WimpDrvs_ValidGlobalVarValues(globals1), Then WK_WimpDrvs_ValidGlobalVarValues(globals2)
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires WK_WimpDrvs_ValidGlobalVarValues(globals1)

    ensures WK_WimpDrvs_ValidGlobalVarValues(globals2)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures wimpdrv_get_pid(globals1, i) == wimpdrv_get_pid(globals2, i)
        ensures wimpdrv_do_get_paddr_base(globals1, i) == wimpdrv_do_get_paddr_base(globals2, i)
        ensures wimpdrv_do_get_paddr_end(globals1, i) == wimpdrv_do_get_paddr_end(globals2, i)
    {
        // Dafny can automatically prove this lemma
    }
}

// Lemma: If <g_wimpdrvs_info> is unchanged, and WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals1),
// Then WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals2)
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals1)

    ensures WK_WimpDrvs_ValidGlobalVarValues_IDWords(globals2)
{
    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            wimpdrv_get_id_word(globals2, i) != WimpDrv_ID_RESERVED_EMPTY && wimpdrv_get_id_word(globals2, j) != WimpDrv_ID_RESERVED_EMPTY
        ensures wimpdrv_get_id_word(globals2, i) == wimpdrv_get_id_word(globals2, j) <==> i == j
    {
        assert wimpdrv_get_id_word(globals2, i) == wimpdrv_get_id_word(globals1, i);
        assert wimpdrv_get_id_word(globals2, j) == wimpdrv_get_id_word(globals1, j);
    }
}

// Lemma: If <g_existing_pids> and <g_wimpdrvs_info> is unchanged, and WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals1),
// Then WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals2)
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals1)

    ensures WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals2)
{
    assert pids_parse_g_wimp_pids(globals1) == pids_parse_g_wimp_pids(globals2);

    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures (wimpdrv_get_pid(globals2, i) == WS_PartitionID(PID_INVALID) || 
            wimpdrv_get_pid(globals2, i) in pids_parse_g_wimp_pids(globals2))
    {
        assert wimpdrv_get_pid(globals2, i) == wimpdrv_get_pid(globals1, i);
    }
}

// Lemma: If gvar_read_fullval(globals1, G_WimpDrvs_Info()) == gvar_read_fullval(globals2, G_WimpDrvs_Info()), and 
// WK_WimpDrvs_ValidGlobalVarValues(globals1), Then WK_WimpDrvs_ValidGlobalVarValues(globals2)
lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(globals1)

    ensures WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs(globals2)
{
    forall i | 0 <= i < WimpDrv_Info_ENTRIES
        ensures wimpdrv_do_get_paddr_base(globals1, i) == wimpdrv_do_get_paddr_base(globals2, i)
        ensures wimpdrv_do_get_paddr_end(globals1, i) == wimpdrv_do_get_paddr_end(globals2, i)
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_WK_WimpDrvs_ValidGlobalVarValues_HoldForUnchangedGlobals(old_wkm:WK_MState, new_wkm:WK_MState)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(old_wkm))
    requires WK_WimpDrvs_ValidGlobalVarValues(wkm_get_globals(old_wkm))

    requires wkm_get_globals(old_wkm) == wkm_get_globals(new_wkm)

    ensures WK_ValidGlobalVars_Decls(wkm_get_globals(new_wkm))
    ensures WK_WimpDrvs_ValidGlobalVarValues(wkm_get_globals(new_wkm)) 
{
    // Dafny can automatically prove this lemma
}

// Lemma: Registered and active wimp drivers must exist in the system
lemma Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, wimpdrv_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
    requires WK_ValidObjAddrs_WimpDrv_DOPAddrs(subjs, objs, id_mappings, objs_addrs, globals)
    
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(globals, wimpdrv_slot) in pids_parse_g_wimp_pids(globals)
        // Requirement: The wimp driver must be registered and is active

    ensures var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_idword);
            WSM_IsWimpDrvID(subjs, wimpdrv_id) 
{
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_idword);

    assert wimpdrv_idword in id_mappings.wimpdrv_ids;
    assert wimpdrv_get_pid(globals, wimpdrv_slot) != WS_PartitionID(PID_INVALID);

    // Apply WK_ValidObjAddrs_WimpDrv_DOPAddrs
    assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(subjs, objs, id_mappings, objs_addrs, globals);
    assert WSM_IsWimpDrvID(subjs, wimpdrv_id);
}