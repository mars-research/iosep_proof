include "mhv.ffi.s.dfy"
include "../ins/util/ffi.i.dfy"

// Lemma: CALL_PMem_AssignToWimps ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_pmem_assign_main_mem_to_wimps_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_PMem_AssignToWimps_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_PMem_AssignToWimps ends up at a result state fulfilling ValidState
lemma Lemma_ffi_pmem_assign_main_mem_to_wimps_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_PMem_AssignToWimps_ReturnWords)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
}

// Lemma: CALL_PMem_ReleaseFromWimps ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_pmem_release_main_mem_from_wimps_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_PMem_ReleaseFromWimps_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_PMem_ReleaseFromWimps ends up at a result state fulfilling ValidState
lemma Lemma_ffi_pmem_release_main_mem_from_wimps_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_PMem_ReleaseFromWimps_ReturnWords)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
}

// Lemma: CALL_PMem_ActivateInOS ends up at a result state fulfilling ValidState
lemma Lemma_ffi_pmem_activate_main_mem_in_os_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_activate_main_mem_in_os(s, old_esp)

    requires var result := ffi_pmem_activate_main_mem_in_os(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_subjs := result.2;
            var new_objs := result.3;
            var new_os_mem_active_map := result.4;
            r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack), subjects := new_subjs, objects := new_objs, 
                        os_mem_active_map := new_os_mem_active_map)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var result1 := ffi_pmem_activate_main_mem_in_os(s);
    var new_stack := result1.0;

    var paddr_end:uint := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var paddr_start:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);

    // Prove validity of <wk_mstate>
    assert wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s.wk_mstate, r.wk_mstate);

    if(ret == TRUE)
    {
        var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
        var os_drvs := result.0;
        var os_tds := result.1;
        var os_fds := result.2;
        var os_dos := result.3;

        // Prove validity of other state variables
        reveal ffi_pmem_activate_main_mem_in_os_stack_and_statevars();

        Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
        Lemma_ValidState_ProveWK_ValidObjs_ObjIDs(s);
        Lemma_OSObjs_ExternalObjs_ExcludeOSDevObjs(s.subjects, s.objects, os_tds, os_fds, os_dos);
        Lemma_OSObjs_IfSetExcludeOSDevObjs_ThenAlsoExcludeOSHCodedTDs(s.subjects, os_tds);
        Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s, r);

        Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, r);
        Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnOSSubjsObjsModification_IfIDsAreUnchanged(s, r);

        Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s, r);
        Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s, r);

        Lemma_WK_ValidState_DevsActivateCond_OnOSSubjsObjsModification_IfIDsAreUnchangedAndAllSubjectsExceptOSDrvsHaveUnchangedPIDs(s, r);
        Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
        assert ValidState(r);
    }
    else
    {
        reveal ffi_pmem_activate_main_mem_in_os_stack_and_statevars();

        // Prove WSM_SubjPID of subjects are unchanged
        Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

        Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
        Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
        Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
        
        Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s, r);
        Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s, r);

        Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
        assert ValidState(r);
    }
}

// Lemma: CALL_PMem_DeactivateFromOS ends up at a result state fulfilling ValidState
lemma Lemma_ffi_pmem_deactivate_main_mem_from_os_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_activate_main_mem_in_os(s, old_esp)

    requires var result := ffi_pmem_deactivate_main_mem_from_os(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_subjs := result.2;
            var new_objs := result.3;
            var new_os_mem_active_map := result.4;
            r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack), subjects := new_subjs, objects := new_objs, 
                        os_mem_active_map := new_os_mem_active_map)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var result1 := ffi_pmem_deactivate_main_mem_from_os(s);
    var new_stack := result1.0;

    var paddr_end:uint := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var paddr_start:word := stack_get_val(old_stack, old_esp);

    // Prove validity of <wk_mstate>
    assert wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s.wk_mstate, r.wk_mstate);

    var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var os_drvs := result.0;
    var os_tds := result.1;
    var os_fds := result.2;
    var os_dos := result.3;

    // Prove validity of other state variables
    reveal ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars();

    Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
    Lemma_ValidState_ProveWK_ValidObjs_ObjIDs(s);
    Lemma_OSObjs_ExternalObjs_ExcludeOSDevObjs(s.subjects, s.objects, os_tds, os_fds, os_dos);
    Lemma_OSObjs_IfSetExcludeOSDevObjs_ThenAlsoExcludeOSHCodedTDs(s.subjects, os_tds);
    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s, r);

    Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s, r);
    Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnOSSubjsObjsModification_IfIDsAreUnchanged(s, r);

    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s, r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s, r);

    Lemma_WK_ValidState_DevsActivateCond_OnOSSubjsObjsModification_IfIDsAreUnchangedAndAllSubjectsExceptOSDrvsHaveUnchangedPIDs(s, r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
    assert ValidState(r);
}

lemma Lemma_pmem_deactivate_main_mem_from_os_Prove_WK_SecureObjsAddrs_MemSeparation(s:state, s':state)
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

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(s'.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(s'.subjects.os_devs)
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires s.subjects.usbpdevs == s'.subjects.usbpdevs

    requires wkm_get_globals(s.wk_mstate) == wkm_get_globals(s'.wk_mstate)
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsSubjID(s.subjects, id) && !WSM_IsOSDrvID(s.subjects, Drv_ID(id))  
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: Except OS drivers, other subjects have unchanged PIDs
    requires forall id :: WSM_IsOSObj(s.objects, id) &&
                    WSM_IsActiveObj(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
                ==> WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id)
        // Requirement: OS objects after pmem deactivation must be active beforehand

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars();
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

    // Prove Wimp drivers' DOs have unchanged PIDs
    forall id | WSM_IsWimpDrvDOID(s.objects, id)
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.oid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();

        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    ObjPID_WimpDrvObj(subjs, objs, id_mappings, globals, id.oid);
        assert WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.oid) ==
                    ObjPID_WimpDrvObj(subjs', objs', id_mappings', globals', id.oid);
        
        // Prove WimpDrvDO_FindOwner(subjs, objs, id.oid) == WimpDrvDO_FindOwner(subjs', objs', id.oid)
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, id.oid);
        var drv_id' := WimpDrvDO_FindOwner(subjs', objs', id.oid);

        if(drv_id != drv_id')
        {
            assert id == subjs.wimp_drvs[drv_id].do_id;
            assert id == subjs'.wimp_drvs[drv_id'].do_id;

            assert subjs.wimp_drvs[drv_id].do_id == subjs.wimp_drvs[drv_id'].do_id;
            assert WSM_DoOwnObj(subjs, drv_id.sid, id.oid);
            assert WSM_DoOwnObj(subjs, drv_id'.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                        s_id1 in WSM_AllSubjsIDs(subjs) && s_id2 in WSM_AllSubjsIDs(subjs) && 
                        WSM_DoOwnObj(subjs, s_id1, o_id) && WSM_DoOwnObj(subjs, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert drv_id == drv_id';
        
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, id.oid);

        assert SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, drv_id) == SubjPID_WimpDrv_ByDrvID(subjs', objs', id_mappings', globals', drv_id);
    }

    // Prove WK_SecureObjsAddrs_MemSeparation
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSTDID(objs, os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid);
    }

    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSFDID(objs, os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid);
    }

    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSDOID(objs, os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid);
    }

    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ensures WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j)
    {
        // Dafny can automatically prove it
    }
}

lemma Lemma_pmem_activate_main_mem_in_os_Prove_WK_SecureObjsAddrs_MemSeparation(s:state, s':state, paddr_start:word, paddr_end:uint)
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

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(s'.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(s'.subjects.os_devs)
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires s.subjects.usbpdevs == s'.subjects.usbpdevs

    requires wkm_get_globals(s.wk_mstate) == wkm_get_globals(s'.wk_mstate)
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsSubjID(s.subjects, id) && !WSM_IsOSDrvID(s.subjects, Drv_ID(id))  
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: Except OS drivers, other subjects have unchanged PIDs
    requires forall wimpdrv_do_id:DO_ID, pmem2 :: 
                WSM_IsWimpDrvDOID(s'.objects, wimpdrv_do_id) && WSM_IsActiveObj(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), wimpdrv_do_id.oid) && // Active WimpDrv's DO
                pmem2 in s'.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
            ==> (pmem2.paddr_start <= pmem2.paddr_end &&
                 WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(s'.objects, s'.objs_addrs, pmem2.paddr_start, pmem2.paddr_end))
        // Requirement: After OS drivers and objects activation, No active wimp driver's DO overlaps with active OS objects

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
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

    // Prove Wimp drivers' DOs have unchanged PIDs
    forall id | WSM_IsWimpDrvDOID(s.objects, id)
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.oid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();

        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    ObjPID_WimpDrvObj(subjs, objs, id_mappings, globals, id.oid);
        assert WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.oid) ==
                    ObjPID_WimpDrvObj(subjs', objs', id_mappings', globals', id.oid);
        
        // Prove WimpDrvDO_FindOwner(subjs, objs, id.oid) == WimpDrvDO_FindOwner(subjs', objs', id.oid)
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, id.oid);
        var drv_id' := WimpDrvDO_FindOwner(subjs', objs', id.oid);

        if(drv_id != drv_id')
        {
            assert id == subjs.wimp_drvs[drv_id].do_id;
            assert id == subjs'.wimp_drvs[drv_id'].do_id;

            assert subjs.wimp_drvs[drv_id].do_id == subjs.wimp_drvs[drv_id'].do_id;
            assert WSM_DoOwnObj(subjs, drv_id.sid, id.oid);
            assert WSM_DoOwnObj(subjs, drv_id'.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                        s_id1 in WSM_AllSubjsIDs(subjs) && s_id2 in WSM_AllSubjsIDs(subjs) && 
                        WSM_DoOwnObj(subjs, s_id1, o_id) && WSM_DoOwnObj(subjs, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert drv_id == drv_id';
        
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, id.oid);

        assert SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, drv_id) == SubjPID_WimpDrv_ByDrvID(subjs', objs', id_mappings', globals', drv_id);
    }

    // Prove WK_SecureObjsAddrs_MemSeparation
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(s'.objects, s'.objs_addrs, pmem2.paddr_start, pmem2.paddr_end);
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();
    }

    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(s'.objects, s'.objs_addrs, pmem2.paddr_start, pmem2.paddr_end);
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();
    }

    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(s'.objects, s'.objs_addrs, pmem2.paddr_start, pmem2.paddr_end);
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();
    }

    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ensures WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j)
    {
        // Dafny can automatically prove it
    }
}




/*********************** Private Lemmas ********************/
// Lemma: On OS subjects and objects modification, if IDs are unchanged, then WK_ValidObjAddrs_WimpDrv_DOPAddrs holds
lemma Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnOSSubjsObjsModification_IfIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s.wk_mstate))
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires (MapGetKeys(s.objs_addrs.tds_addrs) == MapGetKeys(s.objects.os_tds) + MapGetKeys(s.objects.eehci_hcoded_tds) + 
                                         s.objects.eehci_other_tds + MapGetKeys(s.objects.usbpdev_tds) + (s.objects.usbtd_tds)
            ) &&
            (MapGetKeys(s.objs_addrs.fds_addrs) == MapGetKeys(s.objects.os_fds) + 
                                                s.objects.eehci_fds + MapGetKeys(s.objects.usbpdev_fds) + (s.objects.usbtd_fds)
            ) &&
            (MapGetKeys(s.objs_addrs.dos_addrs) == MapGetKeys(s.objects.os_dos) + s.objects.eehci_dos + 
                                                MapGetKeys(s.objects.usbpdev_dos) + MapGetKeys(s.objects.wimpdrv_dos) + (s.objects.usbtd_dos)
            )

    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s'.wk_mstate))
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs_SubjIDs(s'.subjects)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires (MapGetKeys(s'.objs_addrs.tds_addrs) == MapGetKeys(s'.objects.os_tds) + MapGetKeys(s'.objects.eehci_hcoded_tds) + 
                                         s'.objects.eehci_other_tds + MapGetKeys(s'.objects.usbpdev_tds) + (s'.objects.usbtd_tds)
            ) &&
            (MapGetKeys(s'.objs_addrs.fds_addrs) == MapGetKeys(s'.objects.os_fds) + 
                                                s'.objects.eehci_fds + MapGetKeys(s'.objects.usbpdev_fds) + (s'.objects.usbtd_fds)
            ) &&
            (MapGetKeys(s'.objs_addrs.dos_addrs) == MapGetKeys(s'.objects.os_dos) + s'.objects.eehci_dos + 
                                                MapGetKeys(s'.objects.usbpdev_dos) + MapGetKeys(s'.objects.wimpdrv_dos) + (s'.objects.usbtd_dos)
            )

    requires WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(s'.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(s'.subjects.os_devs)
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires s.subjects.usbpdevs == s'.subjects.usbpdevs

    requires wkm_get_globals(s.wk_mstate) == wkm_get_globals(s'.wk_mstate)
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();
    // Dafny can automatically prove this lemma
}

// Lemma: On OS subjects and objects modification, If OS subject and object IDs are unchanged, and all subjects except 
// OS drivers have unchanged PIDs, then WK_ValidState_DevsActivateCond holds
lemma Lemma_WK_ValidState_DevsActivateCond_OnOSSubjsObjsModification_IfIDsAreUnchangedAndAllSubjectsExceptOSDrvsHaveUnchangedPIDs(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(s'.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(s'.subjects.os_devs)
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires s.subjects.usbpdevs == s'.subjects.usbpdevs

    requires wkm_get_globals(s.wk_mstate) == wkm_get_globals(s'.wk_mstate)
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires s.activate_conds == s'.activate_conds
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsSubjID(s.subjects, id) && !WSM_IsOSDrvID(s.subjects, Drv_ID(id))  
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: Except OS drivers, other subjects have unchanged PIDs
    
    ensures WK_ValidState_DevsActivateCond(s'.subjects, s'.objects, s'.id_mappings, s'.activate_conds, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidState_DevsActivateCond();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);
    var activate_conds := s.activate_conds;

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);
    var activate_conds' := s'.activate_conds;

    forall dev_id, dev_id2 | dev_id in activate_conds'.ehci_activate_cond &&
                dev_id2 in activate_conds'.ehci_activate_cond[dev_id]
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) == 
                WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), dev_id.sid)
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id2.sid) == 
                WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), dev_id2.sid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
    }
}