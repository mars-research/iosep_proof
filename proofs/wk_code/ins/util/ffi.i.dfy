include "ffi.s.dfy"
include "../../state_properties_OpsSaneStateSubset.s.dfy"
include "../../state_utils.s.dfy"
include "../../utils/model/utils_subjs_objs.i.dfy"
include "../../utils/model/utils_subjs_any_state.i.dfy"
include "../../state_properties_validity.i.dfy"

lemma Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(old_wkm:WK_MState, new_wkm:WK_MState, ret_params_words_num:nat)
	requires WK_ValidMState(old_wkm)
	requires WK_ValidMState(new_wkm)
    requires ret_params_words_num < 1000
        // We never require a large space for return parameters. 1000 is a magic number
	requires IsAddrInStack(x86_get_reg(old_wkm, ESP) + ret_params_words_num * ARCH_WORD_BYTES); 

	requires var new_stack := wkm_stack_get_all(new_wkm);
            ffi_preserve_old_stack(old_wkm, new_stack, ret_params_words_num)
	requires x86_get_reg(old_wkm, ESP) == x86_get_reg(new_wkm, ESP)

	ensures stack_under_sp_is_unchanged(old_wkm.m, new_wkm.m, x86_get_reg(new_wkm, ESP) + ret_params_words_num * ARCH_WORD_BYTES)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();

	var new_stack := wkm_stack_get_all(new_wkm);

	forall addr:vaddr | is_vaddr_in_stack(addr) && addr >= x86_get_reg(new_wkm, ESP) + ret_params_words_num * ARCH_WORD_BYTES
	ensures old_wkm.m[addr] == new_wkm.m[addr]
	{
		assert old_wkm.m[addr] == wkm_stack_get_val(old_wkm, addr);
		assert new_wkm.m[addr] == stack_get_val(new_stack, addr);
	}
}

// Lemma: On <s.wk_mstate> modification, If <g_wimpdrvs_info> is unchanged, and OS objects have unchanged PID, then 
// WK_SecureObjsAddrs_MemSeparation holds
lemma Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpDrvs_Info())
        // Requirement: <g_wimpdrvs_info> is unchanged
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall id | WSM_IsWimpDrvDO(s.objects, id)
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id) == WSM_ObjPID(subjs', objs', id_mappings', globals', id)
    {
        assert WSM_IsWimpDrvDO(s'.objects, id);
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, id);

        assert WSM_SubjPID(subjs, objs, id_mappings, globals, drv_id.sid) == WSM_SubjPID(subjs', objs', id_mappings', globals', drv_id.sid);
        
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, id);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, id);
        assert WSM_ObjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs, objs, id_mappings, globals, drv_id.sid);
        assert WSM_ObjPID(subjs', objs', id_mappings', globals', id) == WSM_SubjPID(subjs', objs', id_mappings', globals', drv_id.sid);
    }

    Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID_inner(s, s');
}

// Lemma: Any instructions that do not modify global variables ends up at a result state fulfilling ValidState
lemma Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)

    requires WK_ValidMState(r.wk_mstate)
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects) 

    requires wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate)
    requires state_equal_except_mstate(s, r)

    ensures ValidState(r)
{
    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
}

// Lemma: On OS subjects and objects modification, If OS devices are unchanged, OS drivers' and object' IDs are 
// unchanged, and all subjects except OS drivers have unchanged PIDs, then WK_ValidObjsAddrs_PEHCIs holds
lemma Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    requires WK_ValidState_DevsActivateCond(s'.subjects, s'.objects, s'.id_mappings, s'.activate_conds, wkm_get_globals(s'.wk_mstate))

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(s'.subjects.os_drvs)
    requires s.subjects.os_devs == s'.subjects.os_devs
    requires MapGetKeys(s.subjects.wimp_drvs) == MapGetKeys(s'.subjects.wimp_drvs)
    requires MapGetKeys(s.subjects.eehcis) == MapGetKeys(s'.subjects.eehcis)
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(s'.subjects.usbpdevs)

    requires forall id :: id in s.subjects.wimp_drvs
                ==> s.subjects.wimp_drvs[id].do_id == s'.subjects.wimp_drvs[id].do_id

    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires s.activate_conds == s'.activate_conds
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    
    ensures WK_ValidObjsAddrs_PEHCIs(s'.subjects, s'.objects, s'.objs_addrs, s'.id_mappings, s'.activate_conds, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidState_DevsActivateCond();
    reveal WK_ValidObjsAddrs_PEHCIs();

    Lemma_WSM_AllDevIDs_pEHCIs_ProveEqual(s, s');
}




/*********************** Private Lemmas ********************/
// Lemma: On <s.wk_mstate> modification, If <g_wimpdrvs_info> is unchanged, and OS objects and wimp drivers' DOs have 
// unchanged PID, then WK_SecureObjsAddrs_MemSeparation holds for OS TDs
lemma Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID_inner(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpDrvs_Info())
        // Requirement: <g_wimpdrvs_info> is unchanged
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
    requires forall id :: WSM_IsWimpDrvDO(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects and wimp drivers' DOs have unchanged PID

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSTDID(objs, os_obj_id) == WSM_IsOSTDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
    }

    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSFDID(objs, os_obj_id) == WSM_IsOSFDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
    }

    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS DO
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSDOID(objs, os_obj_id) == WSM_IsOSDOID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
    }
}

// Lemma: On <s.wk_mstate> modification, If <g_wimpdrvs_info> is unchanged, and OS objects have unchanged PID, then 
// WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition holds
// [NOTE] Needs 50s to verify
lemma {:timeLimitMultiplier 7} Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpDrvs_Info())
        // Requirement: <g_wimpdrvs_info> is unchanged
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID

    ensures WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition();
}

// Lemma: On <s.wk_mstate> modification, If <g_wimpdrvs_info> and <g_eehci_mem_pbase> are unchanged, and OS objects have 
// unchanged PID, then WK_ValidObjsAddrs holds
lemma Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpDrvs_Info())
    requires eehci_mem_pbase(wkm_get_globals(s.wk_mstate)) == eehci_mem_pbase(wkm_get_globals(s'.wk_mstate))
        // Requirement: <g_wimpdrvs_info> and <g_eehci_mem_pbase> are unchanged
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID

    ensures WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
}

// Lemma: On <s.wk_mstate> modification, If <g_wimpdrvs_info> and <g_eehci_mem_pbase> are unchanged, and OS objects have 
// unchanged PID, then WK_ValidState_DevsActivateCond holds
lemma Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpDrvs_Info())
    requires eehci_mem_pbase(wkm_get_globals(s.wk_mstate)) == eehci_mem_pbase(wkm_get_globals(s'.wk_mstate))
        // Requirement: <g_wimpdrvs_info> and <g_eehci_mem_pbase> are unchanged
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires s.activate_conds == s'.activate_conds
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsSubjID(s.subjects, id)
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: Subjects have unchanged PID
    
    ensures WK_ValidState_DevsActivateCond(s'.subjects, s'.objects, s'.id_mappings, s'.activate_conds, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidState_DevsActivateCond();
}

// Lemma: If <ffi_eehci_activate> returns true, then the newly activated eEHCI does not reference any USB TDs
/*lemma Lemma_ffi_eehci_activate_IfReturnTrue_ThenNewlyActivatedEEHCIDoesNotRefAnyUSBTDs(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
            IsAddrInStack(old_esp + 3 * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 3)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s, new_stack, new_globals)

    ensures x86wk_valid_memstate(new_stack)
    ensures var old_esp := x86_get_reg(s, ESP);
            var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
            var ret:word := stack_get_val(new_stack, old_esp);
            (ret == TRUE) ==> (eehci_valid_slot_id(new_eehci_slot) &&
                                EECHI_DoNotRefAnyUSBTD(new_globals, new_eehci_slot))
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    var old_esp := x86_get_reg(s, ESP);
    var old_globals := wkm_get_globals(s);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);

    if(ret == TRUE)
    {
        assert eehci_valid_slot_id(new_eehci_slot);
        assert EECHI_DoNotRefAnyUSBTD(new_globals, new_eehci_slot);
    }
}*/