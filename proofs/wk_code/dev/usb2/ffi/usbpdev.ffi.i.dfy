include "usbpdev.ffi.s.dfy"
include "../../../state_properties_validity.i.dfy"
include "../../../ins/util/ffi.i.dfy"

// Lemma: CALL_USBPDev_Clear ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbpdev_clear_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_USBPDev_Clear_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_usbpdev_clear(s, old_esp)

    requires var result := ffi_usbpdev_clear(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_objs := result.2;
            r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack), objects := new_objs)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove validity of <wk_mstate>
    assert wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s.wk_mstate, r.wk_mstate);

    // Prove validity of other state variables
    reveal p_ffi_usbpdev_clear_retval();
    Lemma_WK_ValidSubjsObjs_HoldIfOnlyUSBPDevFDDOValsAreChangedInObjs(s, r);

    Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s, r);

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    
    // Prove WK_ValidState_DevsActivateCond
    assert forall id :: WSM_IsSubjID(s.subjects, id)
            ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == 
                WSM_SubjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id);
    reveal WK_ValidState_DevsActivateCond();

    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

// Lemma: AXIOM_Assign_USBPDevs_To_OS_Partition ends up at a result state fulfilling ValidState
lemma Lemma_AXIOM_Assign_USBPDevs_To_OS_Partition_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)
    
    requires WK_ValidGlobalVarValues_USBPDevList(s.subjects, s.id_mappings, wkm_get_globals(s.wk_mstate))
    requires forall i :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(wkm_get_globals(s.wk_mstate), i) == WS_PartitionID(PID_INVALID)
        // Requirment: Needed for ValidInstruction

    requires var result_subjs := AXIOM_Assign_USBPDevs_To_OS_Partition_Property(s);
            r == s.(subjects := result_subjs)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove validity of <wk_mstate>
    assert wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s.wk_mstate, r.wk_mstate);

    // Prove validity of other state variables
    forall id | id in s.subjects.os_devs
        ensures s.subjects.os_devs[id].hcoded_td_id in s.objects.os_tds
    {
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    }
    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s, r);

    Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnUSBPDevsMoveToOSPartition(s, r);
    Lemma_ValidState_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition_OnUSBPDevsMoveToOSPartition(s, r);

    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    reveal WK_ValidGlobalVarValues_USBPDevs();

    reveal WK_ValidGlobalVarValues_USBPDevList();

    // Prove WK_ValidState_DevsActivateCond
    reveal WK_ValidState_DevsActivateCond();

    assert forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
            ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) == 
                WSM_SubjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), dev_id.sid);
    forall dev_id, dev_id2 | dev_id in s.activate_conds.ehci_activate_cond &&
                    dev_id2 in s.activate_conds.ehci_activate_cond[dev_id]
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id2.sid) == 
                WSM_SubjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), dev_id2.sid)
    {
        assert dev_id2 in s.subjects.eehcis;
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
    }
    assert WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate));

    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

lemma Lemma_AXIOM_Assign_USBPDevs_To_OS_Partition_Prove_WK_SecureObjsAddrs_MemSeparation(s:state, s':state)
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

    requires s.subjects.os_drvs == s'.subjects.os_drvs
    requires s.subjects.os_devs == s'.subjects.os_devs
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(s'.subjects.usbpdevs)
    requires forall id :: id in s.subjects.usbpdevs
                ==> (s.subjects.usbpdevs[id].hcoded_td_id == s'.subjects.usbpdevs[id].hcoded_td_id &&
                     s.subjects.usbpdevs[id].fd_ids == s'.subjects.usbpdevs[id].fd_ids &&
                     s.subjects.usbpdevs[id].do_ids == s'.subjects.usbpdevs[id].do_ids)
        // Requirement: Modifications to subjects

    requires s.wk_mstate == s'.wk_mstate
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires s.objects == s'.objects

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
    Lemma_ValidState_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition_OnUSBPDevsMoveToOSPartition(s, s');
    assert forall id :: WSM_IsWimpDrvDOID(s.objects, id)
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
            WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.oid);

    // Prove WK_SecureObjsAddrs_MemSeparation
    Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnUSBPDevsMoveToOSPartition(s, s');

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




/*********************** Private Lemmas ********************/
// Lemma: When moving USBPDevs to the OS partition, WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition holds
lemma Lemma_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnUSBPDevsMoveToOSPartition(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))

    requires s.subjects.os_drvs == s'.subjects.os_drvs
    requires s.subjects.os_devs == s'.subjects.os_devs
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(s'.subjects.usbpdevs)
    requires forall id :: id in s.subjects.usbpdevs
                ==> (s.subjects.usbpdevs[id].hcoded_td_id == s'.subjects.usbpdevs[id].hcoded_td_id &&
                     s.subjects.usbpdevs[id].fd_ids == s'.subjects.usbpdevs[id].fd_ids &&
                     s.subjects.usbpdevs[id].do_ids == s'.subjects.usbpdevs[id].do_ids)
        // Requirement: Modifications to subjects

    requires s.wk_mstate == s'.wk_mstate
    requires s.objects == s'.objects
    requires s.id_mappings == s'.id_mappings

    ensures WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
        // Property 1
    ensures forall id :: WSM_IsOSSubjID(s.subjects, id)
                ==> WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id) == 
                    WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id)
    ensures forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id) == 
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id)
        // Property 2
{
    reveal WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition();
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

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

    forall s_id, o_id | WSM_IsOSSubjID(subjs', s_id) && WSM_DoOwnObj(subjs', s_id, o_id)
        ensures WSM_SubjPID(subjs', objs', id_mappings', globals', s_id) == WSM_ObjPID(subjs', objs', id_mappings', globals', o_id)
            // For Property 1
        ensures WSM_SubjPID(subjs', objs', id_mappings', globals', s_id) == WSM_SubjPID(subjs, objs, id_mappings, globals, s_id)
        ensures WSM_ObjPID(subjs', objs', id_mappings', globals', o_id) == WSM_ObjPID(subjs, objs, id_mappings, globals, o_id)
    {
        assert WSM_SubjPID(subjs', objs', id_mappings', globals', s_id) == WSM_SubjPID(subjs, objs, id_mappings, globals, s_id);

        // Prove WSM_IsOSObj(objs, o_id)
        assert WSM_DoOwnObj(subjs, s_id, o_id);

        reveal WK_ValidObjs_ObjInSubjsMustBeInState();
        assert WSM_IsOSObj(objs, o_id);

        assert WSM_ObjPID(subjs, objs, id_mappings, globals, o_id) == ObjPID_OSObj(objs, o_id);
    }
}

// Lemma: When moving USBPDevs to the OS partition, WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition holds
// [NOTE] Needs 40s to verify
lemma Lemma_ValidState_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition_OnUSBPDevsMoveToOSPartition(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires s.subjects.os_drvs == s'.subjects.os_drvs
    requires s.subjects.os_devs == s'.subjects.os_devs
    requires s.subjects.wimp_drvs == s'.subjects.wimp_drvs
    requires s.subjects.eehcis == s'.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(s'.subjects.usbpdevs)
    requires forall id :: id in s.subjects.usbpdevs
                ==> (s.subjects.usbpdevs[id].hcoded_td_id == s'.subjects.usbpdevs[id].hcoded_td_id &&
                     s.subjects.usbpdevs[id].fd_ids == s'.subjects.usbpdevs[id].fd_ids &&
                     s.subjects.usbpdevs[id].do_ids == s'.subjects.usbpdevs[id].do_ids)
        // Requirement: Modifications to subjects

    requires s.wk_mstate == s'.wk_mstate
    requires s.objects == s'.objects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
        // Requirement: Some of other state variables are unchanged

    ensures WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
        // Property 1:
    ensures forall id :: WSM_IsWimpDrvDOID(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.oid)
        // Property 2: 
{
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
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

    // Prove property 1
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(subjs, objs, id_mappings, globals);
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(subjs', objs', id_mappings', globals');

    forall id | id in objs.eehci_hcoded_tds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var dev_id := EEHCIObj_FindOwner(subjs, objs, id.oid);
        assert WSM_DoOwnObj(subjs', dev_id.sid, id.oid);
    }

    forall id | id in objs.eehci_other_tds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var dev_id := EEHCIObj_FindOwner(subjs, objs, id.oid);
        assert WSM_DoOwnObj(subjs', dev_id.sid, id.oid);
    }

    forall id | id in objs.eehci_fds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var dev_id := EEHCIObj_FindOwner(subjs, objs, id.oid);
        assert WSM_DoOwnObj(subjs', dev_id.sid, id.oid);
    }

    forall id | id in objs.eehci_dos
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var dev_id := EEHCIObj_FindOwner(subjs, objs, id.oid);
        assert WSM_DoOwnObj(subjs', dev_id.sid, id.oid);
    }


    forall id | id in objs.wimpdrv_dos
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, id.oid);
        assert WSM_DoOwnObj(subjs', drv_id.sid, id.oid);
    }


    forall id | id in objs.usbtd_tds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid);
        assert idword == USBTDMappedObj_IDToUSBTDIDWord(subjs', objs', id_mappings', id.oid);
    }

    forall id | id in objs.usbtd_fds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid);
        assert idword == USBTDMappedObj_IDToUSBTDIDWord(subjs', objs', id_mappings', id.oid);
    }

    forall id | id in objs.usbtd_dos
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_ObjPID(subjs', objs', id_mappings', globals', id.oid)
    {
        var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid);
        assert idword == USBTDMappedObj_IDToUSBTDIDWord(subjs', objs', id_mappings', id.oid);
    }
}