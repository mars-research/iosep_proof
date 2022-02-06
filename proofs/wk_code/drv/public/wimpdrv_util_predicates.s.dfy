include "../drv.s.dfy"
include "../../utils/model/utils_objs_any_state.s.dfy"

// Predicate: The given memory region [do_pbase, do_pend) is not overlap with any active OS objects
predicate WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(
    objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, do_pbase:word, do_pend:uint
)
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
        // Requirement: Some predicates from WK_ValidObjsAddrs

    requires WK_ValidPMemRegion(do_pbase, do_pend)
{
    (forall os_obj_id:TD_ID, pmem1:: 
            WSM_IsOSTDID(objs, os_obj_id) && ObjPID_OSObj(objs, os_obj_id.oid) != WS_PartitionID(PID_INVALID) &&   // Active OS TD
            pmem1 in objs_addrs.tds_addrs[os_obj_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_pbase, do_pend)    // Separate in memory
    ) &&
    (forall os_obj_id:FD_ID, pmem1 :: 
            WSM_IsOSFDID(objs, os_obj_id) && ObjPID_OSObj(objs, os_obj_id.oid) != WS_PartitionID(PID_INVALID) &&   // Active OS FD
            pmem1 in objs_addrs.fds_addrs[os_obj_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_pbase, do_pend)    // Separate in memory
    ) &&
    (forall os_obj_id:DO_ID, pmem1 :: 
            WSM_IsOSDOID(objs, os_obj_id) && ObjPID_OSObj(objs, os_obj_id.oid) != WS_PartitionID(PID_INVALID) &&   // Active OS DO
            pmem1 in objs_addrs.dos_addrs[os_obj_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_pbase, do_pend)    // Separate in memory
    )
}