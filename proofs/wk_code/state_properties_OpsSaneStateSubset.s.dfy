include "state_properties_validity.s.dfy"
include "dev/usb2/usb_tds_ops/usb_tds_checks.s.dfy"
include "utils/model/utils_objs_valid_state.s.dfy"

predicate OpsSaneStateSubset(s:state)
{
    var globals := wkm_get_globals(s.wk_mstate);

    InstSaneState(s) &&

    WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s.subjects, s.objects, s.id_mappings, globals) &&

    // Limitation 1: WK cannot verify USB TDs of type USBTDs_TYPE_iTD32 and USBTDs_TYPE_siTD32
    WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification(globals) && 

    // SI: Forall active USB TDs, they either have empty content or they have flags USBTD_SLOT_FLAG_SubmitDone and
    // USBTD_SLOT_FLAG_SlotSecure set
    // [NOTE] This is a validity SI, because it only eases state mappings
    WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure(globals) && 
    
    (true)
}

// Predicate: OS's I/O objects can be either active in the OS partition or inactive
predicate {:opaque} WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
{
    // OS's objects can only be in the OS partition or inactive
    (forall id :: id in objs.os_tds
        ==> (WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION) ||
            WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WS_PartitionID(PID_INVALID))
    ) &&
    (forall id :: id in objs.os_fds
        ==> (WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION) ||
            WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WS_PartitionID(PID_INVALID))
    ) &&
    (forall id :: id in objs.os_dos
        ==> (WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION) ||
            WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WS_PartitionID(PID_INVALID))
    ) &&

    (forall id :: id in subjs.os_drvs
        ==> (WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WS_PartitionID(PID_RESERVED_OS_PARTITION) ||
            WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID))
    ) &&
    (forall id :: id in subjs.os_devs
        ==> (WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WS_PartitionID(PID_RESERVED_OS_PARTITION) ||
            WSM_SubjPID(subjs, objs, id_mappings, globals, id.sid) == WS_PartitionID(PID_INVALID))
    ) &&

    (true)
}

// Predicate: WK can only verify USB TDs of type USBTDs_TYPE_QTD32 and USBTDs_TYPE_QH32
predicate {:opaque} WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    forall i :: usbtd_map_valid_slot_id(i) &&
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
        ==> (usbtd_map_get_type(globals, i) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals, i) == USBTDs_TYPE_QH32)
}

// Predicate: For all active USB TDs in <g_usbtd_mem>, they are either empty or their flags is 
// SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
predicate {:opaque} WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure(globals:globalsmap)
    requires WK_ValidGlobalState(globals)
{
    assert WK_USBTD_Map_ValidGlobalVarValues(globals);

    (forall td_slot :: usbtd_map_valid_slot_id(td_slot) &&
            usbtd_map_get_pid(globals, td_slot) != WS_PartitionID(PID_INVALID)
        ==> (var td_type := usbtd_map_get_type(globals, td_slot);
             assert usbtd_slot_valid_type(globals, td_slot);
             usbtd_has_clear_content(globals, td_slot, td_type) || 
             (usbtd_map_get_flags(globals, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    )
}




/*********************** State invariants satisfied after executing each CPU instruction ********************/
// State invariants (for both validity security predicates) satisfied after executing each CPU instruction
predicate InstSaneState(s:state)
{
    ValidState(s) &&
    SecureState(s)
}

predicate SecureState(s:state) // [TODO] Need revise
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
{
    var globals := wkm_get_globals(s.wk_mstate);

    WK_SecureMState(s.wk_mstate) &&
    WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals)
}

predicate WK_SecureMState(wkm:WK_MState) // [TODO] Need revise
    requires WK_ValidGlobalState(wkm_get_globals(wkm))
{
    var globals := wkm_get_globals(wkm);

    WK_USBTD_Map_SecureGlobalVarValues(globals) &&
    WK_EEHCI_Mem_SecureGlobalVarValues(globals) &&
    (true)
}

predicate {:opaque} WK_SecureObjsAddrs_MemSeparation(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, objs_addrs:WSM_Objects_Addrs, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
{
    reveal WK_ValidObjsAddrs();

    // 1. Active wimp driver objects must be separate in memory from each other
    // [NOTE] This predicate implies the predicate similar to the next SI
    (forall i, j :: wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ==> WK_WimpDrv_DOMustNotOverlapWithEachOther(globals, i, j)) &&

    // 2. Active OS objects must be separate in memory from any active wimp driver objects (i.e., DOs)
    (forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            WSM_IsOSTDID(objs, os_obj_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    ) &&
    (forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            WSM_IsOSFDID(objs, os_obj_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    ) &&
    (forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            WSM_IsOSDOID(objs, os_obj_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) &&   // Active OS DO
            WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    ) &&

    (true)
}








/*********************** Transition Constraints ********************/
predicate WKOps_UnchangedStateVars(s1:state, s2:state)
{
    // Immutable state variables
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&

    (true)
} 