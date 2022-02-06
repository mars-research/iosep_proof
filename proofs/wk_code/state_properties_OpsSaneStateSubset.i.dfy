include "state_properties_OpsSaneStateSubset.s.dfy"

/*********************** Properties of OpsSaneStateSubset ********************/
lemma Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s:state)
    requires OpsSaneStateSubset(s)

    ensures WK_ValidObjs_ObjIDs(s.objects)
{
    reveal WK_ValidObjs();
}

lemma Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_HCodedTDs(s:state)
    requires OpsSaneStateSubset(s)

    ensures WK_ValidObjs_ObjInSubjsMustBeInState(s.subjects, s.objects)
    ensures forall dev_id :: dev_id in s.subjects.os_devs
                ==> s.subjects.os_devs[dev_id].hcoded_td_id in s.subjects.os_devs[dev_id].td_ids
    ensures WK_ValidObjs_HCodedTDs(s.subjects, s.objects)
{
    reveal WK_ValidObjs();
}




/*********************** Other Public Lemmas ********************/
// Lemma: If OpsSaneStateSubset(s1) and InstSaneState(s2), and G_USBTD_MAP_MEM is unchanged, then OpsSaneStateSubset(s2)
lemma Lemma_OpsSaneStateSubset_HoldIfUSBTDsAreUnchanged(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires global_read_fullval(wkm_get_globals(s1.wk_mstate), G_USBTD_MAP_MEM()) == 
             global_read_fullval(wkm_get_globals(s2.wk_mstate), G_USBTD_MAP_MEM())
        // Requirement: G_USBTD_MAP_MEM is unchanged

    requires WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(
                s2.subjects, s2.objects, s2.id_mappings, wkm_get_globals(s2.wk_mstate))

    ensures OpsSaneStateSubset(s2)
{
    reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();
    reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();

    var s1_globals := wkm_get_globals(s1.wk_mstate);
    var s2_globals := wkm_get_globals(s2.wk_mstate);

    forall td_slot | usbtd_map_valid_slot_id(td_slot) &&
            usbtd_map_get_pid(s2_globals, td_slot) != WS_PartitionID(PID_INVALID)
        ensures (var td_type := usbtd_map_get_type(s2_globals, td_slot);
             assert usbtd_slot_valid_type(s2_globals, td_slot);
             usbtd_has_clear_content(s2_globals, td_slot, td_type) || 
             (usbtd_map_get_flags(s2_globals, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    {
        reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
        reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
    }
}

lemma Lemma_ProveWK_SecureObjsAddrs_MemSeparation(s:state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires forall wimpdrv_do_id:DO_ID, pmem2 ::
                    WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) &&
                    pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                ==> pmem2.paddr_start <= pmem2.paddr_end
    requires forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 ::
                    WSM_IsOSTDID(s.objects, os_obj_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), os_obj_id.oid) &&   // Active OS TD
                    WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) && // Active WimpDrv's DO
                    pmem1 in s.objs_addrs.tds_addrs[os_obj_id].paddrs && pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    requires forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 ::
                    WSM_IsOSFDID(s.objects, os_obj_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), os_obj_id.oid) &&   // Active OS FD
                    WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) && // Active WimpDrv's DO
                    pmem1 in s.objs_addrs.fds_addrs[os_obj_id].paddrs && pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    requires forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 ::
                    WSM_IsOSDOID(s.objects, os_obj_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), os_obj_id.oid) &&   // Active OS DO
                    WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) && // Active WimpDrv's DO
                    pmem1 in s.objs_addrs.dos_addrs[os_obj_id].paddrs && pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    requires forall i, j :: wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
                    i != j
                ==> WK_WimpDrv_DOMustNotOverlapWithEachOther(wkm_get_globals(s.wk_mstate), i, j)

    ensures WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))
{
    reveal WK_SecureObjsAddrs_MemSeparation();
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires s1.subjects.os_drvs == s2.subjects.os_drvs
    requires s1.subjects.os_devs == s2.subjects.os_devs

    requires s1.objects.os_tds == s2.objects.os_tds
    requires s1.objects.os_fds == s2.objects.os_fds
    requires s1.objects.os_dos == s2.objects.os_dos

    ensures WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s2.subjects, s2.objects, s2.id_mappings, wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsIDsAndPIDsAreUnchanged(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires MapGetKeys(s1.subjects.os_drvs) == MapGetKeys(s2.subjects.os_drvs)
    requires MapGetKeys(s1.subjects.os_devs) == MapGetKeys(s2.subjects.os_devs)
    requires MapGetKeys(s1.objects.os_tds) == MapGetKeys(s2.objects.os_tds)
    requires MapGetKeys(s1.objects.os_fds) == MapGetKeys(s2.objects.os_fds)
    requires MapGetKeys(s1.objects.os_dos) == MapGetKeys(s2.objects.os_dos)
        // Requirement: OS subjects'/objects' IDs are unchanged

    requires forall id :: id in s1.subjects.os_drvs
                ==> s1.subjects.os_drvs[id].pid == s2.subjects.os_drvs[id].pid
    requires forall id :: id in s1.subjects.os_devs
                ==> s1.subjects.os_devs[id].pid == s2.subjects.os_devs[id].pid
    requires forall id :: id in s1.objects.os_tds
                ==> s1.objects.os_tds[id].pid == s2.objects.os_tds[id].pid
    requires forall id :: id in s1.objects.os_fds
                ==> s1.objects.os_fds[id].pid == s2.objects.os_fds[id].pid
    requires forall id :: id in s1.objects.os_dos
                ==> s1.objects.os_dos[id].pid == s2.objects.os_dos[id].pid

    ensures WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s2.subjects, s2.objects, s2.id_mappings, wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires global_read_fullval(wkm_get_globals(s1.wk_mstate), G_USBTD_MAP_MEM()) == 
             global_read_fullval(wkm_get_globals(s2.wk_mstate), G_USBTD_MAP_MEM())

    ensures WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires global_read_fullval(wkm_get_globals(s1.wk_mstate), G_USBTD_MAP_MEM()) == 
             global_read_fullval(wkm_get_globals(s2.wk_mstate), G_USBTD_MAP_MEM())

    ensures WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();

    var globals1 := wkm_get_globals(s1.wk_mstate);
    var globals2 := wkm_get_globals(s2.wk_mstate);
    forall td_slot | usbtd_map_valid_slot_id(td_slot) &&
            usbtd_map_get_pid(globals2, td_slot) != WS_PartitionID(PID_INVALID)
        ensures (var td_type := usbtd_map_get_type(globals2, td_slot);
             assert usbtd_slot_valid_type(globals2, td_slot);
             usbtd_has_clear_content(globals2, td_slot, td_type) || 
             (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    {
        assert usbtd_map_valid_slot_id(td_slot);
        assert usbtd_map_get_pid(globals1, td_slot) != WS_PartitionID(PID_INVALID);

        var td_type := usbtd_map_get_type(globals2, td_slot);
        assert usbtd_slot_valid_type(globals2, td_slot);

        assert td_type == usbtd_map_get_type(globals1, td_slot);
        assert usbtd_slot_valid_type(globals1, td_slot);

        reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
        reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
        assert usbtd_has_clear_content(globals2, td_slot, td_type) || 
             (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit));
    }
}