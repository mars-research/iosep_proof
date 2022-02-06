include "state.dfy"
include "arch/headers.dfy"
include "mm/headers.dfy"
include "utils/model/headers_any_state.dfy"
include "drv/drv.s.dfy"
include "dev/usb2/usb_pdev.s.dfy"
include "dev/usb2/eehci.s.dfy"
include "dev/usb2/usb_tds.s.dfy"
include "partition_id.s.dfy"

predicate WK_ValidMState(wkm:WK_MState)
{
    Valid_WKMachineState_Arch(wkm) && 
    WK_ValidMemState(wkm) &&   
    WK_ValidGlobalState(wkm_get_globals(wkm)) && 
    
    (true)
}

// Valid global state must have valid global variables' (gvars') declarations and definitions
predicate WK_ValidGlobalState(globals:globalsmap)
{
    WK_ValidGlobalVars_Decls(globals) &&
    WK_ValidGlobalVars_Vals(globals) &&

    (true)
}

// Predicates that must be hold for gvars' values
predicate WK_ValidGlobalVars_Vals(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{  
    WK_ValidPartitionIDs_InGlobalVars(globals) &&  
    WK_WimpDrvs_ValidGlobalVarValues(globals) &&

    WK_WimpUSBPDev_ValidGlobalVarValues(globals) &&
    WK_EEHCI_Info_ValidGlobalVarValues(globals) &&
    WK_EEHCI_Mem_ValidGlobalVarValues(globals) &&
    WK_USBTD_Map_ValidGlobalVarValues(globals) &&

    (true)
}




/*********************** SIs related to subjects and objects ********************/
predicate {:opaque} WK_ValidSubjs(subjs:WSM_Subjects, id_mappings:WSM_ID_Mappings)
    ensures WK_ValidSubjs(subjs, id_mappings) ==> WK_ValidSubjs_SubjIDs(subjs)
    ensures WK_ValidSubjs(subjs, id_mappings) ==> WK_ValidSubjs_eEHCIs(subjs)
{
    // 1.2. Additional state invariants for eEHCIs and USBPDevs
    WK_ValidSubjs_eEHCIs(subjs) &&

    // 1.3. Different types of subjects have different Drv_IDs, Dev_IDs and subject IDs
    WK_ValidSubjs_SubjIDs(subjs) &&
    
    // 1.4. Non-empty set of subjects
    |MapGetKeys(subjs.os_drvs)| > 0 &&

    (true)
}

predicate {:opaque} WK_ValidObjs(subjs:WSM_Subjects, objs:WSM_Objects)
    requires WK_ValidSubjs_SubjIDs(subjs)

    ensures WK_ValidObjs(subjs, objs) ==> WK_ValidObjs_eEHCIs(subjs, objs)
{
    // 2.1 Different types of objects have different TD_IDs, FD_IDs, DO_IDs and object IDs
    WK_ValidObjs_ObjIDs(objs) &&

    // 2.2 Non-empty set of objects
    (|MapGetKeys(objs.os_tds)| + |MapGetKeys(objs.os_fds)| + |MapGetKeys(objs.os_dos)| + 
    |objs.eehci_hcoded_tds| + |objs.eehci_other_tds| + |objs.eehci_fds| + |objs.eehci_dos| + 
    |MapGetKeys(objs.usbpdev_tds)| + |MapGetKeys(objs.usbpdev_fds)| + |MapGetKeys(objs.usbpdev_dos)| + |MapGetKeys(objs.wimpdrv_dos)| + 
    |(objs.usbtd_tds)| + |(objs.usbtd_fds)| + |(objs.usbtd_dos)| > 0) &&

    // 2.3 Hardcoded TDs of OS devices are in devices
    // [NOTE] Not needed for eEHCIs, as their <td_ids> have already contained hardcoded TDs according to WK_ValidSubjs_eEHCIs
    (forall dev_id :: dev_id in subjs.os_devs
        ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids) &&

    // 2.4 No two subjects own the same object
    (forall o_id, s_id1, s_id2 :: 
        s_id1 in WSM_AllSubjsIDs(subjs) && s_id2 in WSM_AllSubjsIDs(subjs) && 
        WSM_DoOwnObj(subjs, s_id1, o_id) && WSM_DoOwnObj(subjs, s_id2, o_id)
        ==> s_id1 == s_id2) &&

    // 2.5 TDs/FDs/DOs in subjects are also in the state
    WK_ValidObjs_ObjInSubjsMustBeInState(subjs, objs) &&

    // 2.6 - 2.8 Hardcoded TDs related SIs
    WK_ValidObjs_HCodedTDs(subjs, objs) &&
    
    // 2.10 The objects of wimp drivers, eEHCIs, and USBPDevs recorded in <objs> are all internal objects
    WK_ValidObjs_InternalObjsOf_WimpSubjects(subjs, objs) &&

    // 2.11 - 2.12 Additioonal SIs for objects in eEHCIs
    WK_ValidObjs_eEHCIs(subjs, objs) &&

    (true)
}

predicate {:opaque} WK_ValidIDMappings(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings)
{
    // 3.1. In WSM_ID_Mappings, if a key maps to Drv_IDs/Dev_ID/TD_ID/FD_ID/DO_ID exist in the system, then it must map 
    // to a unique ID
    WK_ValidIDMappings_UniqueIDs(subjs, objs, id_mappings) &&

    // 3.2 All useful (i.e., valid and not empty) IDs in words and USBPDev addresses are in <id_mappings>
    //// All wimp driver ID in words (except WimpDrv_ID_RESERVED_EMPTY) maps to Drv_ID
    // [NOTE] We do not require all values in this map to be a Drv_ID in s.objs.wimp_drvs, which should be a precondition 
    // of operations and satisfied by wimp driver management codes
    (forall e:word :: e != WimpDrv_ID_RESERVED_EMPTY 
        <==> e in id_mappings.wimpdrv_ids) &&

    //// All valid USBPDev addresses except the empty address maps to Dev_ID in <id_mappings.usbpdev_ids>
    (forall addr:USBPDev_Addr :: addr in id_mappings.usbpdev_ids
        <==> (
                var addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
                Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
                addr != usb_parse_usbpdev_addr(addr_raw)
            )
    ) &&

    //// All eehci ID in words (except eEHCI_ID_INVALID) maps to Dev_ID
    (forall e:word :: e != eEHCI_ID_INVALID 
        <==> e in id_mappings.eehci_ids) &&

    //// All USB TD ID in words (except USBTD_ID_INVALID) maps to TD/FD/DO
    (forall e:word :: e != USBTD_ID_INVALID
        <==> e in id_mappings.usbtd_to_td) &&
    (forall e:word :: e != USBTD_ID_INVALID
        <==> e in id_mappings.usbtd_to_fd) &&
    (forall e:word :: e != USBTD_ID_INVALID
        <==> e in id_mappings.usbtd_to_do) &&

    // 3.3 For wimp subjects and objects, if they exist in the system, then their IDs in words and addresses must also
    // exist in the mapping
    WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords(id_mappings, MapGetKeys(subjs.wimp_drvs)) &&
    WK_ValidIDMappings_EEHCIIDsMustMapToIDWords(id_mappings, MapGetKeys(subjs.eehcis)) &&
    WK_ValidIDMappings_USBPDevIDsMustMapToAddrs(id_mappings, MapGetKeys(subjs.usbpdevs)) &&
    WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs(id_mappings, objs.usbtd_tds, objs.usbtd_fds, objs.usbtd_dos) &&

    (true)
}

predicate {:opaque} WK_ValidObjsAddrs(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)

    ensures WK_ValidObjsAddrs(objs, objs_addrs, globals)
                ==> (MapGetKeys(objs_addrs.tds_addrs) == MapGetKeys(objs.os_tds) + MapGetKeys(objs.eehci_hcoded_tds) + 
                                         objs.eehci_other_tds + MapGetKeys(objs.usbpdev_tds) + (objs.usbtd_tds)
                    ) &&
                    (MapGetKeys(objs_addrs.fds_addrs) == MapGetKeys(objs.os_fds) + 
                                                        objs.eehci_fds + MapGetKeys(objs.usbpdev_fds) + (objs.usbtd_fds)
                    ) &&
                    (MapGetKeys(objs_addrs.dos_addrs) == MapGetKeys(objs.os_dos) + objs.eehci_dos + 
                                                        MapGetKeys(objs.usbpdev_dos) + MapGetKeys(objs.wimpdrv_dos) + (objs.usbtd_dos)
                    )
    ensures WK_ValidObjsAddrs(objs, objs_addrs, globals)
                ==> (forall id, pmem :: id in objs.os_tds && pmem in objs_addrs.tds_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&
                    (forall id, pmem :: id in objs.os_fds && pmem in objs_addrs.fds_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&
                    (forall id, pmem :: id in objs.os_dos && pmem in objs_addrs.dos_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end)
{
    // 5.1 All objects in <objs> appear in <objs_addrs>
    (MapGetKeys(objs_addrs.tds_addrs) == MapGetKeys(objs.os_tds) + MapGetKeys(objs.eehci_hcoded_tds) + 
                                         objs.eehci_other_tds + MapGetKeys(objs.usbpdev_tds) + (objs.usbtd_tds)
    ) &&
    (MapGetKeys(objs_addrs.fds_addrs) == MapGetKeys(objs.os_fds) + 
                                         objs.eehci_fds + MapGetKeys(objs.usbpdev_fds) + (objs.usbtd_fds)
    ) &&
    (MapGetKeys(objs_addrs.dos_addrs) == MapGetKeys(objs.os_dos) + objs.eehci_dos + 
                                         MapGetKeys(objs.usbpdev_dos) + MapGetKeys(objs.wimpdrv_dos) + (objs.usbtd_dos)
    ) &&

    // 5.2 All physical memory regions of OS objects are valid memory regions
    (forall id, pmem :: id in objs.os_tds && pmem in objs_addrs.tds_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&
    (forall id, pmem :: id in objs.os_fds && pmem in objs_addrs.fds_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&
    (forall id, pmem :: id in objs.os_dos && pmem in objs_addrs.dos_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&

    //// 5.3.1 eEHCIs' objects are located in eEHCIs' memory, and have no PIO addresses
    (forall id :: id in objs.eehci_hcoded_tds ==> objs_addrs.tds_addrs[id] == ObjAddrs({}, {})) &&
    (forall id :: id in objs.eehci_other_tds ==> objs_addrs.tds_addrs[id] == ObjAddrs({PAddrRegion(eehci_mem_pbase(globals), eehci_mem_pend(globals))}, {})) &&
    (forall id :: id in objs.eehci_fds ==> objs_addrs.fds_addrs[id] == ObjAddrs({PAddrRegion(eehci_mem_pbase(globals), eehci_mem_pend(globals))}, {})) &&
    (forall id :: id in objs.eehci_dos ==> objs_addrs.dos_addrs[id] == ObjAddrs({PAddrRegion(eehci_mem_pbase(globals), eehci_mem_pend(globals))}, {})) &&

    //// 5.3.2 USBPDevs do not have paddrs and PIO addresses
    (forall id :: id in objs.usbpdev_tds ==> objs_addrs.tds_addrs[id] == ObjAddrs({}, {})) &&
    (forall id :: id in objs.usbpdev_fds ==> objs_addrs.fds_addrs[id] == ObjAddrs({}, {})) && 
    (forall id :: id in objs.usbpdev_dos ==> objs_addrs.dos_addrs[id] == ObjAddrs({}, {})) &&

    //// 5.3.3 USB TDs are located in global variables' memory, and have no PIO addresses
    // [NOTE] To prove the security properties, it is fine to specify USB TDs in the entire global variables' memory 
    // here, instead of <g_usbtd_map_mem>. This is because WK_Mem_Separate_Segs() ensures global variables have their 
    // own memory, WK_GlobalDecls() and WK_ValidGlobalVars_Decls() ensures different global variables are separated in 
    // memory, and the definition of <g_usbtd_map_mem> ensures different USB TDs also have their own memory
    (forall id :: id in objs.usbtd_tds ==> objs_addrs.tds_addrs[id] == ObjAddrs({PAddrRegion(WK_DATASeg_BasePAddr(), WK_DATASeg_EndPAddr())}, {})) &&
    (forall id :: id in objs.usbtd_fds ==> objs_addrs.fds_addrs[id] == ObjAddrs({PAddrRegion(WK_DATASeg_BasePAddr(), WK_DATASeg_EndPAddr())}, {})) &&
    (forall id :: id in objs.usbtd_dos ==> objs_addrs.dos_addrs[id] == ObjAddrs({PAddrRegion(WK_DATASeg_BasePAddr(), WK_DATASeg_EndPAddr())}, {})) &&

    //// 5.3.4 (Recall that each wimp driver has one DO) For each wimp driver, its DO locates at one continous physical 
    // memory region, and do not have PIO addresses
    (forall id, pmem :: id in objs.wimpdrv_dos && pmem in objs_addrs.dos_addrs[id].paddrs ==> WK_ValidPMemRegion(pmem.paddr_start, pmem.paddr_end)) &&
    (forall id :: id in objs.wimpdrv_dos 
        ==> (|objs_addrs.dos_addrs[id].paddrs| == 1 && objs_addrs.dos_addrs[id].pio_addrs == {})) &&

    // 5.4 Proper separation of address spaces enforced by mHV and other components of WK
    WK_ValidObjsAddrs_Separation(objs, objs_addrs, globals) &&

    (true)
}

predicate WK_ValidObjsAddrs_Separation(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
    requires (MapGetKeys(objs_addrs.tds_addrs) == MapGetKeys(objs.os_tds) + MapGetKeys(objs.eehci_hcoded_tds) + 
                                         objs.eehci_other_tds + MapGetKeys(objs.usbpdev_tds) + (objs.usbtd_tds)
            ) &&
            (MapGetKeys(objs_addrs.fds_addrs) == MapGetKeys(objs.os_fds) + 
                                                objs.eehci_fds + MapGetKeys(objs.usbpdev_fds) + (objs.usbtd_fds)
            ) &&
            (MapGetKeys(objs_addrs.dos_addrs) == MapGetKeys(objs.os_dos) + objs.eehci_dos + 
                                                MapGetKeys(objs.usbpdev_dos) + MapGetKeys(objs.wimpdrv_dos) + (objs.usbtd_dos)
            )
    requires (forall id, pmem :: id in objs.os_tds && pmem in objs_addrs.tds_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&
            (forall id, pmem :: id in objs.os_fds && pmem in objs_addrs.fds_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end) &&
            (forall id, pmem :: id in objs.os_dos && pmem in objs_addrs.dos_addrs[id].paddrs ==> pmem.paddr_start < pmem.paddr_end)
    requires (forall id, pmem :: id in objs.wimpdrv_dos && pmem in objs_addrs.dos_addrs[id].paddrs ==> WK_ValidPMemRegion(pmem.paddr_start, pmem.paddr_end))
{
    // 5.7.1 All (active and inactive) OS objects must be separate from WK memory
    (forall id, pmem :: id in objs.os_tds && pmem in objs_addrs.tds_addrs[id].paddrs
        ==> WK_Mem_NotOverlapWithWKMem(pmem.paddr_start, pmem.paddr_end)
    ) &&
    (forall id, pmem :: id in objs.os_fds && pmem in objs_addrs.fds_addrs[id].paddrs
        ==> WK_Mem_NotOverlapWithWKMem(pmem.paddr_start, pmem.paddr_end)
    ) &&
    (forall id, pmem :: id in objs.os_dos && pmem in objs_addrs.dos_addrs[id].paddrs
        ==> WK_Mem_NotOverlapWithWKMem(pmem.paddr_start, pmem.paddr_end)
    ) &&
    
    // 5.7.2 All (active and inactive) OS objects are separate from eEHCI physical memory
    (forall id, pmem :: id in objs.os_tds && pmem in objs_addrs.tds_addrs[id].paddrs
        ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, eehci_mem_pbase(globals), eehci_mem_pend(globals))
    ) &&
    (forall id, pmem :: id in objs.os_fds && pmem in objs_addrs.fds_addrs[id].paddrs
        ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, eehci_mem_pbase(globals), eehci_mem_pend(globals))
    ) &&
    (forall id, pmem :: id in objs.os_dos && pmem in objs_addrs.dos_addrs[id].paddrs
        ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, eehci_mem_pbase(globals), eehci_mem_pend(globals))
    ) &&

    // 5.7.3 All (active and inactive) wimp driver DOs must be separate from WK memory
    (forall id, pmem :: id in objs.wimpdrv_dos && pmem in objs_addrs.dos_addrs[id].paddrs
        ==> WK_Mem_NotOverlapWithWKMem(pmem.paddr_start, pmem.paddr_end)
    ) &&

    // 5.7.4 All (active and inactive) wimp driver DOs must be separate from eEHCI physical memory
    (forall id, pmem :: id in objs.wimpdrv_dos && pmem in objs_addrs.dos_addrs[id].paddrs
        ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, eehci_mem_pbase(globals), eehci_mem_pend(globals))
    ) &&

    (true)
}

// State validity properties related to active USBPDevs in global variables
predicate {:opaque} WK_ValidGlobalVarValues_USBPDevs(subjs:WSM_Subjects, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
{
    // If a USBPDev is active, then its addr recorded in <g_wimpdevs_info> must be in 
    // usbpdevlist_get_all_non_empty_addrs(globals)
    (forall slot :: usbpdev_valid_slot_id(slot) &&
            usbpdev_get_pid(globals, slot) != WS_PartitionID(PID_INVALID) &&
            usbpdev_get_updateflag(globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ==> (
                var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, slot);
                var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

                usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals)
            )
    ) &&

    // If a USBPDev has <active_in_os> set, then all devices recorded in <g_wimpdevs_info> must have PID_INVALID in 
    // the record
    (
        forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(subjs, usbpdev_id)
            ==> (
                    subjs.usbpdevs[usbpdev_id].active_in_os == true
                        ==> (forall i :: usbpdev_valid_slot_id(i)
                                    ==> usbpdev_get_pid(globals, i) == WS_PartitionID(PID_INVALID))
                )
    )
}

// State validity properties related to <g_usbpdev_devlist> in global variables
predicate {:opaque} WK_ValidGlobalVarValues_USBPDevList(subjs:WSM_Subjects, id_mappings:WSM_ID_Mappings, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
{
    // 1. <g_usbpdev_devlist> stores ALL USBPDevs given to wimp partitions 
    (forall usbpdev_addr :: usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals)
        ==> (
            usbpdev_addr in id_mappings.usbpdev_ids &&
            id_mappings.usbpdev_ids[usbpdev_addr] in subjs.usbpdevs
        )
    ) &&

    (forall dev_id :: dev_id in subjs.usbpdevs
        ==> (exists usbpdev_addr :: usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals) &&
                usbpdev_addr in id_mappings.usbpdev_ids &&
                id_mappings.usbpdev_ids[usbpdev_addr] == dev_id
            )
    ) &&

    (true)
}




/*********************** Utility Predicates ********************/
// Predicate: For each ID in <wimpdrv_ids>, it must be mapped in <id_mappings.wimpdrv_ids> as a value
predicate {:opaque} WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords(id_mappings:WSM_ID_Mappings, wimpdrv_ids:set<Drv_ID>)
{
    forall id:Drv_ID :: id in wimpdrv_ids
        ==> (exists e:word :: e in id_mappings.wimpdrv_ids && 
                id_mappings.wimpdrv_ids[e] == id)
}

// Predicate: For each ID in <eehci_ids>, it must be mapped in <id_mappings.usbpdev_ids> as a value
predicate {:opaque} WK_ValidIDMappings_EEHCIIDsMustMapToIDWords(id_mappings:WSM_ID_Mappings, eehci_ids:set<Dev_ID>)
{
    forall id:Dev_ID :: id in eehci_ids
        ==> (exists e:word :: e in id_mappings.eehci_ids && 
                id_mappings.eehci_ids[e] == id)
}

// Predicate: For each ID in <usbpdev_ids>, it must be mapped in <id_mappings.usbpdev_ids> as a value
predicate {:opaque} WK_ValidIDMappings_USBPDevIDsMustMapToAddrs(id_mappings:WSM_ID_Mappings, usbpdev_ids:set<Dev_ID>)
{
    forall id:Dev_ID :: id in usbpdev_ids
        ==> (exists e:USBPDev_Addr :: e in id_mappings.usbpdev_ids && 
                id_mappings.usbpdev_ids[e] == id)
}

// Predicate: Additional predicates for USB TD id mappings
predicate {:opaque} WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs(id_mappings:WSM_ID_Mappings, usbtd_tds:set<TD_ID>, usbtd_fds:set<FD_ID>, usbtd_dos:set<DO_ID>)
{
    // For each ID in <usbtd_*>, it must be mapped in <id_mappings.usbtd_to_*> as a value
    (forall id:TD_ID :: id in usbtd_tds
        ==> (exists e:word :: e in id_mappings.usbtd_to_td && 
                id_mappings.usbtd_to_td[e] == id)
    ) &&
    (forall id:FD_ID :: id in usbtd_fds
        ==> (exists e:word :: e in id_mappings.usbtd_to_fd && 
                id_mappings.usbtd_to_fd[e] == id)
    ) &&
    (forall id:DO_ID :: id in usbtd_dos
        ==> (exists e:word :: e in id_mappings.usbtd_to_do && 
                id_mappings.usbtd_to_do[e] == id)
    ) &&

    // If a TD/FD/DO is mapped to a USB TD and exists in the system, then the object ID appears in the corresponding 
    // id_mappings.usbtd_to_* only
    (forall e, id :: id in usbtd_tds && e in id_mappings.usbtd_to_fd
        ==> id_mappings.usbtd_to_fd[e].oid != id.oid) &&
    (forall e, id :: id in usbtd_tds && e in id_mappings.usbtd_to_do
        ==> id_mappings.usbtd_to_do[e].oid != id.oid) &&
    (forall e, id :: id in usbtd_fds && e in id_mappings.usbtd_to_td
        ==> id_mappings.usbtd_to_td[e].oid != id.oid) &&
    (forall e, id :: id in usbtd_fds && e in id_mappings.usbtd_to_do
        ==> id_mappings.usbtd_to_do[e].oid != id.oid) &&
    (forall e, id :: id in usbtd_dos && e in id_mappings.usbtd_to_fd
        ==> id_mappings.usbtd_to_fd[e].oid != id.oid) &&
    (forall e, id :: id in usbtd_dos && e in id_mappings.usbtd_to_td
        ==> id_mappings.usbtd_to_td[e].oid != id.oid) &&

    (true)
}

// Predicate: <map_*_ids> in the given eEHCI must map to unique object IDs
predicate WK_ValidSubjs_eEHCIs_ObjMapInEachEEHCIMapToUniqueObjID(eehci:eEHCI)
{
    (forall e1, e2 :: e1 in eehci.map_td_ids && 
            e2 in eehci.map_td_ids
        ==> (e1 == e2 <==> eehci.map_td_ids[e1] == eehci.map_td_ids[e2])
    ) &&

    (forall e1, e2 :: e1 in eehci.map_fd_ids && 
            e2 in eehci.map_fd_ids
        ==> (e1 == e2 <==> eehci.map_fd_ids[e1] == eehci.map_fd_ids[e2])
    ) &&

    (forall e1, e2 :: e1 in eehci.map_do_ids && 
            e2 in eehci.map_do_ids
        ==> (e1 == e2 <==> eehci.map_do_ids[e1] == eehci.map_do_ids[e2])
    )
}

predicate {:opaque} WK_ValidSubjs_SubjIDs(subjs:WSM_Subjects)
{
    //// 1.3.1 Different subjects have different internal subject IDs, and hence different Drv_IDs/Dev_IDs
    (forall id1 :: id1 in subjs.wimp_drvs
        ==> (Dev_ID(id1.sid) !in subjs.eehcis && 
             Dev_ID(id1.sid) !in subjs.usbpdevs &&
             id1 !in subjs.os_drvs &&
             Dev_ID(id1.sid) !in subjs.os_devs)
    ) &&
    (forall id1 :: id1 in subjs.eehcis
        ==> (id1 !in subjs.usbpdevs &&
             Drv_ID(id1.sid) !in subjs.os_drvs &&
             id1 !in subjs.os_devs)
    ) &&
    (forall id1 :: id1 in subjs.usbpdevs
        ==> (Drv_ID(id1.sid) !in subjs.os_drvs &&
             id1 !in subjs.os_devs)
    ) &&
    (forall id1 :: id1 in subjs.os_drvs
        ==> (Dev_ID(id1.sid) !in subjs.os_devs)
    ) &&

    (true)
}

predicate {:opaque} WK_ValidSubjs_eEHCIs(subjs:WSM_Subjects)
{
    // 1.2.1. Correct mapping of memory offsets of eEHCI registers to TD/FD/DO IDs
    // [NOTE] G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset and G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset are not eEHCI objects,
    // G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset stores the eEHCI's name, and G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset is
    // for invoking eEHCI operations in the eEHCI separation code
    (forall e :: e in subjs.eehcis
        ==> MapGetKeys(subjs.eehcis[e].map_do_ids) == {G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset} &&
            MapGetKeys(subjs.eehcis[e].map_fd_ids) == {G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset, 
                G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset} &&
                // [Assumption] eEHCIs can issue transfers, even if the enable bit is set to FALSE. Devices do not issue
                // transfers, if the referenced slot/address is empty
            MapGetKeys(subjs.eehcis[e].map_td_ids) == eehci_usbtd_regs_offsets()
    ) &&

    // 1.2.2. <map_*_ids> in each eEHCI must map to unique object IDs
    (forall e :: e in subjs.eehcis ==> WK_ValidSubjs_eEHCIs_ObjMapInEachEEHCIMapToUniqueObjID(subjs.eehcis[e])) &&

    // 1.2.3. Correct values in eEHCI's <td_ids>, <fd_ids> and <do_ids>
    (forall e :: e in subjs.eehcis
        ==> (subjs.eehcis[e].td_ids == OwnedTDs_eEHCI_ExcludeHCodedTD(subjs, e) + {subjs.eehcis[e].hcoded_td_id} &&
             subjs.eehcis[e].fd_ids == OwnedFDs_eEHCI(subjs, e) &&
             subjs.eehcis[e].do_ids == OwnedDOs_eEHCI(subjs, e))
    ) &&

    (true)
}

predicate {:opaque} WK_ValidObjs_eEHCIs(subjs:WSM_Subjects, objs:WSM_Objects)
{
    // 2.11 <map_*_ids> map to objects owned by eEHCIs
    (forall e, k :: e in subjs.eehcis && k in subjs.eehcis[e].map_td_ids
        ==> subjs.eehcis[e].map_td_ids[k] in objs.eehci_other_tds) &&
    (forall e, k :: e in subjs.eehcis && k in subjs.eehcis[e].map_fd_ids
        ==> subjs.eehcis[e].map_fd_ids[k] in objs.eehci_fds) &&
    (forall e, k :: e in subjs.eehcis && k in subjs.eehcis[e].map_do_ids
        ==> subjs.eehcis[e].map_do_ids[k] in objs.eehci_dos) &&

    // 2.12 In <subjs.eehcis[e].map_td_ids> for each eEHCI, it does not map registers to the eEHCI's hardcoded TD
    (forall e, k :: e in subjs.eehcis && k in subjs.eehcis[e].map_td_ids
        ==> subjs.eehcis[e].map_td_ids[k] != subjs.eehcis[e].hcoded_td_id) &&

    (true)
}

predicate {:opaque} WK_ValidObjs_ObjIDs(objs:WSM_Objects)
{
    //// 2.1.1 Different objects have different internal object IDs, and hence different TD_ID/FD_ID/DO_ID
    (forall id1 :: id1 in objs.os_tds
        ==> (FD_ID(id1.oid) !in objs.os_fds &&
             DO_ID(id1.oid) !in objs.os_dos &&
             id1 !in objs.eehci_hcoded_tds &&
             id1 !in objs.eehci_other_tds &&
             FD_ID(id1.oid) !in objs.eehci_fds &&
             DO_ID(id1.oid) !in objs.eehci_dos &&
             id1 !in objs.usbpdev_tds &&
             FD_ID(id1.oid) !in objs.usbpdev_fds &&
             DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             id1 !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.os_fds
        ==> (DO_ID(id1.oid) !in objs.os_dos &&
             TD_ID(id1.oid) !in objs.eehci_hcoded_tds &&
             TD_ID(id1.oid) !in objs.eehci_other_tds &&
             id1 !in objs.eehci_fds &&
             DO_ID(id1.oid) !in objs.eehci_dos &&
             TD_ID(id1.oid) !in objs.usbpdev_tds &&
             id1 !in objs.usbpdev_fds &&
             DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             id1 !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.os_dos
        ==> (TD_ID(id1.oid) !in objs.eehci_hcoded_tds &&
             TD_ID(id1.oid) !in objs.eehci_other_tds &&
             FD_ID(id1.oid) !in objs.eehci_fds &&
             id1 !in objs.eehci_dos &&
             TD_ID(id1.oid) !in objs.usbpdev_tds &&
             FD_ID(id1.oid) !in objs.usbpdev_fds &&
             id1 !in objs.usbpdev_dos &&
             id1 !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             id1 !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.eehci_hcoded_tds
        ==> (id1 !in objs.eehci_other_tds &&
             FD_ID(id1.oid) !in objs.eehci_fds &&
             DO_ID(id1.oid) !in objs.eehci_dos &&
             id1 !in objs.usbpdev_tds &&
             FD_ID(id1.oid) !in objs.usbpdev_fds &&
             DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             id1 !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.eehci_other_tds
        ==> (FD_ID(id1.oid) !in objs.eehci_fds &&
             DO_ID(id1.oid) !in objs.eehci_dos &&
             id1 !in objs.usbpdev_tds &&
             FD_ID(id1.oid) !in objs.usbpdev_fds &&
             DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             id1 !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.eehci_fds
        ==> (DO_ID(id1.oid) !in objs.eehci_dos &&
             TD_ID(id1.oid) !in objs.usbpdev_tds &&
             id1 !in objs.usbpdev_fds &&
             DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             id1 !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.eehci_dos
        ==> (TD_ID(id1.oid) !in objs.usbpdev_tds &&
             FD_ID(id1.oid) !in objs.usbpdev_fds &&
             id1 !in objs.usbpdev_dos &&
             id1 !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             id1 !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.usbpdev_tds
        ==> (FD_ID(id1.oid) !in objs.usbpdev_fds &&
             DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.usbpdev_fds
        ==> (DO_ID(id1.oid) !in objs.usbpdev_dos &&
             DO_ID(id1.oid) !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             id1 !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.usbpdev_dos
        ==> (id1 !in objs.wimpdrv_dos &&
             TD_ID(id1.oid) !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             id1 !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.wimpdrv_dos
        ==> (TD_ID(id1.oid) !in objs.usbtd_tds &&
             FD_ID(id1.oid) !in objs.usbtd_fds &&
             id1 !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.usbtd_tds
        ==> (FD_ID(id1.oid) !in objs.usbtd_fds &&
             DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&
    (forall id1 :: id1 in objs.usbtd_fds
        ==> (DO_ID(id1.oid) !in objs.usbtd_dos)
    ) &&

    (true)
}

predicate {:opaque} WK_ValidObjs_ObjInSubjsMustBeInState(subjs:WSM_Subjects, objs:WSM_Objects)
{
    // 2.5.1. For Wimp Drivers
    (forall drv_id :: drv_id in subjs.wimp_drvs
        ==> subjs.wimp_drvs[drv_id].do_id in objs.wimpdrv_dos) &&
    (forall id :: id in objs.wimpdrv_dos
        ==> (exists drv_id :: drv_id in subjs.wimp_drvs && 
             subjs.wimp_drvs[drv_id].do_id == id)) &&

    // 2.5.2. For eEHCIs
    (forall dev_id, id :: dev_id in subjs.eehcis && 
            id in OwnedTDs_eEHCI_ExcludeHCodedTD(subjs, dev_id)
        ==> id in objs.eehci_other_tds) &&
    (forall dev_id :: dev_id in subjs.eehcis
        ==> subjs.eehcis[dev_id].hcoded_td_id in objs.eehci_hcoded_tds) &&
    (forall dev_id, id :: dev_id in subjs.eehcis && 
            id in subjs.eehcis[dev_id].fd_ids
        ==> id in objs.eehci_fds) &&
    (forall dev_id, id :: dev_id in subjs.eehcis && 
            id in subjs.eehcis[dev_id].do_ids
        ==> id in objs.eehci_dos) &&

    // 2.5.3. For USBPDevs
    (forall dev_id :: dev_id in subjs.usbpdevs
        ==> subjs.usbpdevs[dev_id].hcoded_td_id in objs.usbpdev_tds) &&
    (forall dev_id, id :: dev_id in subjs.usbpdevs && 
            id in subjs.usbpdevs[dev_id].fd_ids
        ==> id in objs.usbpdev_fds) &&
    (forall dev_id, id :: dev_id in subjs.usbpdevs && 
            id in subjs.usbpdevs[dev_id].do_ids
        ==> id in objs.usbpdev_dos) &&

    // 2.5.4. For OS drivers
    (forall drv_id, id :: drv_id in subjs.os_drvs && 
            id in subjs.os_drvs[drv_id].td_ids
        ==> id in objs.os_tds) &&
    (forall drv_id, id :: drv_id in subjs.os_drvs && 
            id in subjs.os_drvs[drv_id].fd_ids
        ==> id in objs.os_fds) &&
    (forall drv_id, id :: drv_id in subjs.os_drvs && 
            id in subjs.os_drvs[drv_id].do_ids
        ==> id in objs.os_dos) &&

    // 2.5.5. For OS devices
    (forall dev_id, id :: dev_id in subjs.os_devs && 
            id in subjs.os_devs[dev_id].td_ids
        ==> id in objs.os_tds) &&
    (forall dev_id, id :: dev_id in subjs.os_devs && 
            id in subjs.os_devs[dev_id].fd_ids
        ==> id in objs.os_fds) &&
    (forall dev_id, id :: dev_id in subjs.os_devs && 
            id in subjs.os_devs[dev_id].do_ids
        ==> id in objs.os_dos) &&

    (true)
}

predicate {:opaque} WK_ValidObjs_HCodedTDs(subjs:WSM_Subjects, objs:WSM_Objects)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs_ObjInSubjsMustBeInState(subjs, objs)
    requires forall dev_id :: dev_id in subjs.os_devs
        ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids
{
    // 2.6. No individual hardcoded TD request R and W to the same TD
    var hcoded_tds := WSM_BuildMap_DevsToHCodedTDVals(subjs, objs);
    (forall dev_id :: dev_id in WSM_AllDevIDs(subjs)
        ==> (forall td_id :: td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
            ==> HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds[td_id].amodes != {R,W})) &&

    //// Condition 2.7 Hardcoded TDs do not reference any hardcoded TDs
    (forall dev_id, td_id :: dev_id in WSM_AllDevIDs(subjs) &&
                td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
        ==> td_id !in WSM_AllHCodedTDIDs(subjs)) &&

    //// Condition 2.8 Objects refed in hardcoded TDs must be owned by the device 
    (forall dev_id :: dev_id in WSM_AllDevIDs(subjs)
        ==> (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
                WSM_OwnedTDs(subjs, dev_id.sid)) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
                WSM_OwnedFDs(subjs, dev_id.sid)) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
                WSM_OwnedDOs(subjs, dev_id.sid))
    ) && 

    (true)
}

predicate {:opaque} WK_ValidObjs_InternalObjsOf_WimpSubjects(subjs:WSM_Subjects, objs:WSM_Objects)
{
    // 2.10.1 All <objs.wimpdrv_dos> are internal objects
    (forall id :: id in objs.wimpdrv_dos
        ==> (exists drv_id :: drv_id in subjs.wimp_drvs && 
             subjs.wimp_drvs[drv_id].do_id == id)
    ) &&

    // 2.10.2 All <objs.eehci_*> are internal objects
    (forall id :: id in objs.eehci_hcoded_tds
        ==> (exists dev_id :: dev_id in subjs.eehcis &&
             subjs.eehcis[dev_id].hcoded_td_id == id)
    ) &&
    (forall id :: id in objs.eehci_other_tds
        ==> (exists dev_id :: dev_id in subjs.eehcis &&
             id in OwnedTDs_eEHCI_ExcludeHCodedTD(subjs, dev_id))
    ) &&
    (forall id :: id in objs.eehci_fds
        ==> (exists dev_id :: dev_id in subjs.eehcis &&
             id in subjs.eehcis[dev_id].fd_ids)
    ) &&
    (forall id :: id in objs.eehci_dos
        ==> (exists dev_id :: dev_id in subjs.eehcis &&
             id in subjs.eehcis[dev_id].do_ids)
    ) &&

    // 2.10.3 All <objs.usbpdev_*> are internal objects
    (forall id :: id in objs.usbpdev_tds
        ==> (exists dev_id :: dev_id in subjs.usbpdevs &&
             subjs.usbpdevs[dev_id].hcoded_td_id == id)
    ) &&
    (forall id :: id in objs.usbpdev_fds
        ==> (exists dev_id :: dev_id in subjs.usbpdevs &&
             id in subjs.usbpdevs[dev_id].fd_ids)
    ) &&
    (forall id :: id in objs.usbpdev_dos
        ==> (exists dev_id :: dev_id in subjs.usbpdevs &&
             id in subjs.usbpdevs[dev_id].do_ids)
    ) &&

    (true)
}

predicate {:opaque} WK_ValidIDMappings_UniqueIDs(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings)
{
    //// If a wimpdrv_id_word maps to a WimpDrv Drv_ID in subjs.wimp_drvs, then it must map to a unique ID
    (forall e1, e2 :: e1 in id_mappings.wimpdrv_ids && 
            e2 in id_mappings.wimpdrv_ids &&
            id_mappings.wimpdrv_ids[e1] in subjs.wimp_drvs &&
            id_mappings.wimpdrv_ids[e2] in subjs.wimp_drvs
        ==> (e1 == e2 <==> id_mappings.wimpdrv_ids[e1] == id_mappings.wimpdrv_ids[e2])
    ) &&

    //// If a USBPDev_Addr maps to a USBPDev Dev_ID in subjs.usbpdevs, then it must map to a unique ID
    (forall e1, e2 :: e1 in id_mappings.usbpdev_ids && 
            e2 in id_mappings.usbpdev_ids &&
            id_mappings.usbpdev_ids[e1] in subjs.usbpdevs &&
            id_mappings.usbpdev_ids[e2] in subjs.usbpdevs
        ==> (e1 == e2 <==> id_mappings.usbpdev_ids[e1] == id_mappings.usbpdev_ids[e2])
    ) &&

    //// If a eehci_id_word maps to an eEHCI Dev_ID in subjs.eehcis, then it must map to a unique ID
    (forall e1, e2 :: e1 in id_mappings.eehci_ids && 
            e2 in id_mappings.eehci_ids &&
            id_mappings.eehci_ids[e1] in subjs.eehcis &&
            id_mappings.eehci_ids[e2] in subjs.eehcis
        ==> (e1 == e2 <==> id_mappings.eehci_ids[e1] == id_mappings.eehci_ids[e2])
    ) &&

    //// If a usbtd_id_word maps to an <usbtd_td> in objs.usbtd_tds, then it must map to a unique ID
    (forall e1, e2 :: e1 in id_mappings.usbtd_to_td && 
            e2 in id_mappings.usbtd_to_td &&
            id_mappings.usbtd_to_td[e1] in objs.usbtd_tds &&
            id_mappings.usbtd_to_td[e2] in objs.usbtd_tds
        ==> (e1 == e2 <==> id_mappings.usbtd_to_td[e1] == id_mappings.usbtd_to_td[e2])
    ) &&

    //// If a usbtd_id_word maps to an <usbtd_fd> in objs.usbtd_fds, then it must map to a unique ID
    (forall e1, e2 :: e1 in id_mappings.usbtd_to_fd && 
            e2 in id_mappings.usbtd_to_fd &&
            id_mappings.usbtd_to_fd[e1] in objs.usbtd_fds &&
            id_mappings.usbtd_to_fd[e2] in objs.usbtd_fds
        ==> (e1 == e2 <==> id_mappings.usbtd_to_fd[e1] == id_mappings.usbtd_to_fd[e2])
    ) &&

    //// If a usbtd_id_word maps to an <usbtd_do> in objs.usbtd_dos, then it must map to a unique ID
    (forall e1, e2 :: e1 in id_mappings.usbtd_to_do && 
            e2 in id_mappings.usbtd_to_do &&
            id_mappings.usbtd_to_do[e1] in objs.usbtd_dos &&
            id_mappings.usbtd_to_do[e2] in objs.usbtd_dos
        ==> (e1 == e2 <==> id_mappings.usbtd_to_do[e1] == id_mappings.usbtd_to_do[e2])
    ) &&

    (true)
}

// State validity properties related to both global variables and the state variable <objs_addrs> 
predicate {:opaque} WK_ValidObjAddrs_WimpDrv_DOPAddrs(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, objs_addrs:WSM_Objects_Addrs, globals:globalsmap
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires (MapGetKeys(objs_addrs.tds_addrs) == MapGetKeys(objs.os_tds) + MapGetKeys(objs.eehci_hcoded_tds) + 
                                         objs.eehci_other_tds + MapGetKeys(objs.usbpdev_tds) + (objs.usbtd_tds)
            ) &&
            (MapGetKeys(objs_addrs.fds_addrs) == MapGetKeys(objs.os_fds) + 
                                                objs.eehci_fds + MapGetKeys(objs.usbpdev_fds) + (objs.usbtd_fds)
            ) &&
            (MapGetKeys(objs_addrs.dos_addrs) == MapGetKeys(objs.os_dos) + objs.eehci_dos + 
                                                MapGetKeys(objs.usbpdev_dos) + MapGetKeys(objs.wimpdrv_dos) + (objs.usbtd_dos)
            )
{
    // 1. In each slot of active WimpDrv's info, the recorded paddr base and end must match <objs_addrs>
    (forall i :: wimpdrv_valid_slot_id(i) && 
            wimpdrv_do_get_flag(globals, i) == WimpDrv_Slot_UpdateFlag_Complete &&
            wimpdrv_get_pid(globals, i) != WS_PartitionID(PID_INVALID)
        ==> (
                var drv_id_word:word := wimpdrv_get_id_word(globals, i);
                var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, drv_id_word);
                WSM_IsWimpDrvID(subjs, drv_id) &&
                    // Such active wimp driver must exist in the system
                var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs, objs, id_mappings, drv_id_word);
                var pmem := objs_addrs.dos_addrs[wimpdrv_do_id].paddrs;
                pmem == {PAddrRegion(wimpdrv_do_get_paddr_base(globals, i), wimpdrv_do_get_paddr_end(globals, i))}
                    // And its address stored in the global variable must match its spec in <objs_addrs>
            )
    ) &&

    (true)
}




/*********************** Utility Functions - General Subjects/Objects ********************/
function WSM_BuildMap_DevsToHCodedTDVals(subjs:WSM_Subjects, objs:WSM_Objects) : map<Dev_ID, TD_Val>
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs_ObjInSubjsMustBeInState(subjs, objs)
    requires forall dev_id :: dev_id in subjs.os_devs
        ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids
    
    ensures MapGetKeys(WSM_BuildMap_DevsToHCodedTDVals(subjs, objs)) == 
                MapGetKeys(subjs.os_devs) + MapGetKeys(subjs.usbpdevs) + MapGetKeys(subjs.eehcis)
    ensures MapGetKeys(WSM_BuildMap_DevsToHCodedTDVals(subjs, objs)) == WSM_AllDevIDs(subjs)
{
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    MapConcat(
        MapConcat(WSM_BuildMap_DevsToHCodedTDVals_OSDevs(subjs, objs), WSM_BuildMap_DevsToHCodedTDVals_USBPDevs(subjs, objs)),
        WSM_BuildMap_DevsToHCodedTDVals_EEHCIs(subjs, objs)
    )
}




/*********************** Util Functions and Predicates - WimpDrv ********************/
function WimpDrv_IDWord_ToDrvID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, drv_id_word:word) : Drv_ID
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY
{
    reveal WK_ValidIDMappings();

    id_mappings.wimpdrv_ids[drv_id_word]
}

// Get the DO_ID of the given wimp driver's DO
function WimpDrv_GetDOID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, drv_id_word:word) : DO_ID
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, drv_id_word) in subjs.wimp_drvs

    ensures WimpDrv_GetDOID(subjs, objs, id_mappings, drv_id_word) in objs.wimpdrv_dos
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    var id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, drv_id_word);

    subjs.wimp_drvs[id].do_id
}




/*********************** Util Lemmas ********************/
// Lemma: Objects owned by OS subjects must exist in the state
lemma Lemma_ObjsOwnedByOSSubjsMustBeInState(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)

    ensures forall s_id, o_id :: WSM_IsOSSubjID(subjs, s_id) && WSM_DoOwnObj(subjs, s_id, o_id)
            ==> WSM_IsObjID(objs, o_id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall s_id, o_id | WSM_IsOSSubjID(subjs, s_id) && WSM_DoOwnObj(subjs, s_id, o_id)
        ensures WSM_IsObjID(objs, o_id)
    {
        if(Drv_ID(s_id) in subjs.os_drvs) 
        {
            assert TD_ID(o_id) in subjs.os_drvs[Drv_ID(s_id)].td_ids || FD_ID(o_id) in subjs.os_drvs[Drv_ID(s_id)].fd_ids || DO_ID(o_id) in subjs.os_drvs[Drv_ID(s_id)].do_ids;
            assert WSM_IsObjID(objs, o_id);
        }
        else
        {
            assert Dev_ID(s_id) in subjs.os_devs;
            assert WSM_IsObjID(objs, o_id);
        }
    }
}

// Lemma: Objects owned by OS subjects must exist in the state. Apply the lemma for one subject and object
lemma Lemma_ObjsOwnedByOSSubjsMustBeInState_ApplyForOneSubjAndObj(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, s_id:Subject_ID, o_id:Object_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)

    requires WSM_IsOSSubjID(subjs, s_id)
    requires WSM_DoOwnObj(subjs, s_id, o_id)

    ensures WSM_IsObjID(objs, o_id)
{
    Lemma_ObjsOwnedByOSSubjsMustBeInState(subjs, objs, id_mappings);
}