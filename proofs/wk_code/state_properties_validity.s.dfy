include "state_properties_validity_subjs_objs_mstate.s.dfy"
include "utils/model/utils_objs_valid_state.s.dfy"

predicate ValidState(s:state)
{
    var globals := wkm_get_globals(s.wk_mstate);

    WK_ValidMState(s.wk_mstate) &&
    WK_ValidSubjs(s.subjects, s.id_mappings) &&
    WK_ValidObjs(s.subjects, s.objects) &&
    WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings) &&
    WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, globals) &&
    WK_ValidObjsAddrs(s.objects, s.objs_addrs, globals) &&
    WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals) &&
    WK_ValidGlobalVarValues_USBPDevs(s.subjects, globals) &&
    WK_ValidGlobalVarValues_USBPDevList(s.subjects, s.id_mappings, globals) &&

    WK_ValidState_DevsActivateCond(s.subjects, s.objects, s.id_mappings, s.activate_conds, globals) &&
    WK_ValidObjsAddrs_PEHCIs(s.subjects, s.objects, s.objs_addrs, s.id_mappings, s.activate_conds, globals) &&

    (true)
}

predicate {:opaque} WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
{
    Lemma_ObjsOwnedByOSSubjsMustBeInState(subjs, objs, id_mappings);
    
    // 4.1 For all OS objects, the PID of each object is the same with the PID of its owner subject
    (forall s_id, o_id :: WSM_IsOSSubjID(subjs, s_id) && WSM_DoOwnObj(subjs, s_id, o_id)
        ==> WSM_SubjPID(subjs, objs, id_mappings, globals, s_id) == WSM_ObjPID(subjs, objs, id_mappings, globals, o_id)) &&

    (true)
}

predicate {:opaque} WK_ValidState_DevsActivateCond(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, activate_conds:WSM_Dev_Activate_Conditions, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
{
    // Condition 6.1. In <ehci_activate_cond>, the mappings are from physical EHCIs to ephemeral ones
    //// In <ehci_activate_cond>, all keys are from OS devices, because physical EHCIs are OS devices
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond
        ==> dev_id in subjs.os_devs) &&
    //// In <ehci_activate_cond>, all values are from eEHCIs
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond
        ==> activate_conds.ehci_activate_cond[dev_id] <= MapGetKeys(subjs.eehcis)) &&

    // Condition 6.2. The keys of <ehci_activate_cond> can only be activated into red partition
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond
        ==> (WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id.sid) == WS_PartitionID(PID_INVALID) || 
             WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id.sid) == WS_PartitionID(PID_RESERVED_OS_PARTITION))
    ) &&

    // Condition 6.3. The keys of <ehci_activate_cond> are active/inactive in the OS partition at the same time
    //// [TODO] If we want to more on-demand, we should loose this SI and allow deactivation of physical EHCIs at 
    //// different time
    (forall dev_id1, dev_id2 :: dev_id1 in activate_conds.ehci_activate_cond &&
            dev_id2 in activate_conds.ehci_activate_cond
        ==> WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id1.sid) == 
            WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id2.sid)
    ) &&

    // Condition 6.4. The values of <ehci_activate_cond> can only be activated into green partitions; i.e., either 
    // inactive or in a green partition
    (forall dev_id, dev_id2 :: dev_id in activate_conds.ehci_activate_cond &&
            dev_id2 in activate_conds.ehci_activate_cond[dev_id]
        ==> WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id2.sid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    //// Condition 6.5 No common devices between keys and values
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond
        ==> activate_conds.ehci_activate_cond[dev_id] * MapGetKeys(activate_conds.ehci_activate_cond) == {}) &&

    //// Condition 6.6 If a device is active in red partition, then all mapped 
    //// devices are inactive
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond &&
            WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id.sid) != WS_PartitionID(PID_INVALID)
        ==> (forall dev_id2 :: dev_id2 in activate_conds.ehci_activate_cond[dev_id]
                ==> WSM_SubjPID(subjs, objs, id_mappings, globals, dev_id2.sid) == WS_PartitionID(PID_INVALID))
    ) &&

    (true)
}

predicate {:opaque} WK_ValidObjsAddrs_PEHCIs(
    subjs:WSM_Subjects, objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, id_mappings:WSM_ID_Mappings, 
    activate_conds:WSM_Dev_Activate_Conditions, globals:globalsmap
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
    requires WK_ValidState_DevsActivateCond(subjs, objs, id_mappings, activate_conds, globals)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjsAddrs();
    reveal WK_ValidState_DevsActivateCond();

    //// 5.3.5 Physical EHCIs do not have PIO addresses
    // [TODO] This SI can be loosen and allow pEHCIs to have PIO addresses if they are active in the OS partition. 
    (forall dev_id, id :: dev_id in WSM_AllDevIDs_pEHCIs(subjs, activate_conds) && 
            id in subjs.os_devs[dev_id].td_ids
        ==> objs_addrs.tds_addrs[id].pio_addrs == {}
    ) &&
    (forall dev_id, id :: dev_id in WSM_AllDevIDs_pEHCIs(subjs, activate_conds) && 
            id in subjs.os_devs[dev_id].fd_ids
        ==> objs_addrs.fds_addrs[id].pio_addrs == {}
    ) &&
    (forall dev_id, id :: dev_id in WSM_AllDevIDs_pEHCIs(subjs, activate_conds) && 
            id in subjs.os_devs[dev_id].do_ids
        ==> objs_addrs.dos_addrs[id].pio_addrs == {}
    ) &&

    //// 5.3.6 Physical EHCIs must be separate in memory from all wimp driver objects (i.e., DOs)
    //// [NOTE] We do not need to specify PEHCIs memory are not overlap with wimp objects, because PEHCIs' objects are
    //// in <objs.os_tds/fds/dos>, and this property has already been defined in <WK_ValidObjsAddrs_Separation>
    //// [NOTE] We do not need to specify PEHCIs memory are not overlap with other OS objects, because (1) OS drivers
    //// can never access inactive PEHCIs due to the preconditions in these operations, and (2) OS devices cannot access
    //// inactive PEHCIs due to the properties enforced by IOMMU + ACS.
    (forall pehci_id, pehci_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            pehci_id in WSM_AllDevIDs_pEHCIs(subjs, activate_conds) &&
            pehci_obj_id in subjs.os_devs[pehci_id].td_ids &&
            WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && // any WimpDrv's DO
            pmem1 in objs_addrs.tds_addrs[pehci_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    ) &&
    (forall pehci_id, pehci_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            pehci_id in WSM_AllDevIDs_pEHCIs(subjs, activate_conds) &&
            pehci_obj_id in subjs.os_devs[pehci_id].fd_ids &&
            WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && // any WimpDrv's DO
            pmem1 in objs_addrs.fds_addrs[pehci_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    ) &&
    (forall pehci_id, pehci_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            pehci_id in WSM_AllDevIDs_pEHCIs(subjs, activate_conds) &&
            pehci_obj_id in subjs.os_devs[pehci_id].do_ids &&
            WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && // any WimpDrv's DO
            pmem1 in objs_addrs.dos_addrs[pehci_obj_id].paddrs && pmem2 in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)    // Separate in memory
    ) &&
    
    (true)
}