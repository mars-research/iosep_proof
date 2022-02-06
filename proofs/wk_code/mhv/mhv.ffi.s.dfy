include "../ins/util/ffi.s.dfy"
include "../state_properties_validity.i.dfy"
include "../utils/model/utils_objs_valid_state.s.dfy"
include "../drv/public/wimpdrv_util_predicates.s.dfy"

/*********************** Axioms ********************/
// Given the current <os_mem_active_map> and the physical memory region [paddr_start, paddr_end) to be activated in the 
// OS partition, there must exist a function to tell what external objects in the OS partition can be activated
// [NOTE] This axiom should not activate any OS objects owned by OS devices. This is because OS drivers and devices are
// in MMIO, not main memory
// [NOTE] This function/predicate has been covered by <ffi_pmem_activate_main_mem_in_os>
function {:axiom} os_external_objs_to_be_activated(
    subjs:WSM_Subjects, objs:WSM_Objects, os_mem_active_map:PMem_Active_Map, 
    paddr_start:word, paddr_end:uint
) : (result:(set<Drv_ID>, set<TD_ID>, set<FD_ID>, set<DO_ID>))
    requires WK_ValidPMemRegion(paddr_start, paddr_end)

    ensures result.0 == {}
    ensures forall id :: id in result.1 ==> WSM_IsOSTDID(objs, id)
    ensures forall id :: id in result.2 ==> WSM_IsOSFDID(objs, id)
    ensures forall id :: id in result.3 ==> WSM_IsOSDOID(objs, id)
    ensures forall s_id, o_id :: s_id in WSM_AllSubjsIDs(subjs) &&
                    o_id in (TDIDsToObjIDs(result.1) + FDIDsToObjIDs(result.2) + DOIDsToObjIDs(result.3))
                ==> !WSM_DoOwnObj(subjs, s_id, o_id)
        // Property: Only external objects are returned
    /*ensures forall id :: id in result.0 ==> WSM_IsOSDrvID(subjs, id)
    ensures forall id :: id in result.1 ==> WSM_IsOSTDID(objs, id)
    ensures forall id :: id in result.2 ==> WSM_IsOSFDID(objs, id)
    ensures forall id :: id in result.3 ==> WSM_IsOSDOID(objs, id)
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in result.1
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in result.2
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in result.3
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid) */
        // Property: Objects to be activated are not owned by any OS devices

// Given the current <os_mem_active_map> and the physical memory region [paddr_start, paddr_end) to be deactivated in 
// the OS partition, there must exist a function to tell what OS drivers and objects can be deactivated
// [NOTE] This axiom should not deactivate any OS objects owned by OS devices. This is because OS drivers and devices are
// in different physical memory regions
// [NOTE] This function/predicate has been covered by <ffi_pmem_deactivate_main_mem_from_os>
function {:axiom} os_external_objs_to_be_deactivated(
    subjs:WSM_Subjects, objs:WSM_Objects, os_mem_active_map:PMem_Active_Map, 
    paddr_start:word, paddr_end:uint
) : (result:(set<Drv_ID>, set<TD_ID>, set<FD_ID>, set<DO_ID>))
    requires WK_ValidPMemRegion(paddr_start, paddr_end)
    
    ensures result.0 == {}
    ensures forall id :: id in result.1 ==> WSM_IsOSTDID(objs, id)
    ensures forall id :: id in result.2 ==> WSM_IsOSFDID(objs, id)
    ensures forall id :: id in result.3 ==> WSM_IsOSDOID(objs, id)
    ensures forall s_id, o_id :: s_id in WSM_AllSubjsIDs(subjs) &&
                    o_id in (TDIDsToObjIDs(result.1) + FDIDsToObjIDs(result.2) + DOIDsToObjIDs(result.3))
                ==> !WSM_DoOwnObj(subjs, s_id, o_id)
        // Property: Only external objects are returned
    /*ensures forall id :: id in result.0 ==> WSM_IsOSDrvID(subjs, id)
    ensures forall id :: id in result.1 ==> WSM_IsOSTDID(objs, id)
    ensures forall id :: id in result.2 ==> WSM_IsOSFDID(objs, id)
    ensures forall id :: id in result.3 ==> WSM_IsOSDOID(objs, id)
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in result.1
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in result.2
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in result.3
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid) */
        // Property: Objects to be deactivated are not owned by any OS devices

// Exists a function to correctly update <os_mem_active_map> according to the given physical memory region 
// [paddr_start, paddr_end) to be activated
// [NOTE] This function/predicate has been covered by <ffi_pmem_activate_main_mem_in_os>
function {:axiom} ffi_pmem_activate_main_mem_in_os_update_active_map(
    os_mem_active_map:PMem_Active_Map, paddr_start:word, paddr_end:uint
) :(result:PMem_Active_Map)

// Exists a function to correctly update <os_mem_active_map> according to the given physical memory region 
// [paddr_start, paddr_end) to be deactivated
// [NOTE] This function/predicate has been covered by <ffi_pmem_deactivate_main_mem_from_os>
function {:axiom} ffi_pmem_deactivate_main_mem_from_os_update_active_map(
    os_mem_active_map:PMem_Active_Map, paddr_start:word, paddr_end:uint
) :(result:PMem_Active_Map)




/*********************** Outputs of external functions ********************/
const FFI_PMem_ActivateInOS_ReturnWords:int := 1;
const FFI_PMem_DeactivateFromOS_ReturnWords:int := 0;
const FFI_PMem_AssignToWimps_ReturnWords:int := 1;
const FFI_PMem_ReleaseFromWimps_ReturnWords:int := 0;

const FFI_PMem_ActivateInOS_StackParamsWords:int := 2;
const FFI_PMem_DeactivateFromOS_StackParamsWords:int := 2;
const FFI_PMem_AssignToWimps_StackParamsWords:int := 2;
const FFI_PMem_ReleaseFromWimps_StackParamsWords:int := 2;




/*********************** FFIs ********************/
// Predicate: The given memory region [paddr_start, paddr_end) is not overlap with any active OS objects
predicate OS_NoActiveObjectsInPMemRegion(
    objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, paddr_start:word, paddr_end:uint
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

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
{
    (forall os_obj_id:TD_ID, pmem1:: 
            WSM_IsOSTDID(objs, os_obj_id) && ObjPID_OSObj(objs, os_obj_id.oid) != WS_PartitionID(PID_INVALID) &&   // Active OS TD
            pmem1 in objs_addrs.tds_addrs[os_obj_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)    // Separate in memory
    ) &&
    (forall os_obj_id:FD_ID, pmem1 :: 
            WSM_IsOSFDID(objs, os_obj_id) && ObjPID_OSObj(objs, os_obj_id.oid) != WS_PartitionID(PID_INVALID) &&   // Active OS FD
            pmem1 in objs_addrs.fds_addrs[os_obj_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)    // Separate in memory
    ) &&
    (forall os_obj_id:DO_ID, pmem1 :: 
            WSM_IsOSDOID(objs, os_obj_id) && ObjPID_OSObj(objs, os_obj_id.oid) != WS_PartitionID(PID_INVALID) &&   // Active OS DO
            pmem1 in objs_addrs.dos_addrs[os_obj_id].paddrs
        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)    // Separate in memory
    )
}

// [mHV] FFI: <pmem_activate_main_mem_in_os>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] "main memory" is the physical memory address space for processes (i.e., excluding MMIOs and relevant)
// Input params on stack: (paddr_end:word) at esp + ARCH_WORD_BYTES, (paddr_start:word) at esp
// Return on stack: (ret:uint32) at esp
function {:axiom} ffi_pmem_activate_main_mem_in_os(s:state) : (result:(wk_memmap, map<x86Reg, word>, WSM_Subjects, WSM_Objects, PMem_Active_Map))
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_activate_main_mem_in_os(s, old_esp)
    ensures ffi_preserve_sp_and_bp(s.wk_mstate, result.1)
    ensures ffi_preserve_old_stack(s.wk_mstate, result.0, FFI_PMem_ActivateInOS_ReturnWords) // Return parameters take 1 word
    ensures ffi_pmem_activate_main_mem_in_os_stack_and_statevars(s, result.0, result.2, result.3, result.4)
                // Property: <pmem_activate_main_mem_in_os> activates OS subjects and objects due to assign the memory 
                // [paddr_start, paddr_end) back to the OS partition

predicate ins_valid_pmem_activate_main_mem_in_os(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    //reveal WK_ValidObjsAddrs();

    var old_stack := wkm_stack_get_all(s.wk_mstate);
    var old_globals := wkm_get_globals(s.wk_mstate);

    var paddr_start := stack_get_val(old_stack, old_esp);
    var paddr_end := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);

    WK_ValidPMemRegion(paddr_start, paddr_end)
        // Requirement 1: paddr_start <= paddr_end
}

// [mHV] FFI: <pmem_deactivate_main_mem_from_os>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] "main memory" is the physical memory address space for processes (i.e., excluding MMIOs and relevant)
// Input params on stack: (paddr_end:word) at esp + ARCH_WORD_BYTES, (paddr_start:word) at esp
// Return on stack: None
function {:axiom} ffi_pmem_deactivate_main_mem_from_os(s:state) : (result:(wk_memmap, map<x86Reg, word>, WSM_Subjects, WSM_Objects, PMem_Active_Map))
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_deactivate_main_mem_from_os(s, old_esp)
    ensures ffi_preserve_sp_and_bp(s.wk_mstate, result.1)
    ensures ffi_preserve_old_stack(s.wk_mstate, result.0, FFI_PMem_DeactivateFromOS_ReturnWords) // Words for return parameters
    ensures ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars(s, result.0, result.2, result.3, result.4)
                // Property: <pmem_deactivate_main_mem_from_os> deactivates OS subjects and objects due to assign the memory 
                // [paddr_start, paddr_end) to wimp drivers

predicate ins_valid_pmem_deactivate_main_mem_from_os(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    var old_stack := wkm_stack_get_all(s.wk_mstate);
    var old_globals := wkm_get_globals(s.wk_mstate);

    var paddr_start := stack_get_val(old_stack, old_esp);
    var paddr_end := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);

    WK_ValidPMemRegion(paddr_start, paddr_end)
}

// [mHV] FFI: <pmem_assign_main_mem_to_wimps>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] "main memory" is the physical memory address space for processes (i.e., excluding MMIOs and relevant)
// Input params on stack: (paddr_end:word) at esp + ARCH_WORD_BYTES, (paddr_start:word) at esp
// Return on stack: (ret:uint32) at esp
function {:axiom} ffi_pmem_assign_main_mem_to_wimps(s:state) : (result:(wk_memmap, map<x86Reg, word>))
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_assign_main_mem_to_wimps(s, old_esp)
    ensures ffi_preserve_sp_and_bp(s.wk_mstate, result.1)
    ensures ffi_preserve_old_stack(s.wk_mstate, result.0, FFI_PMem_AssignToWimps_ReturnWords) // Words for return parameters
    ensures ffi_pmem_assign_main_mem_to_wimps_stack_and_statevars(s, result.0)
                // Property: <pmem_assign_main_mem_to_wimps> activates OS subjects and objects due to assign the memory 
                // [paddr_start, paddr_end) back to the OS partition

predicate ins_valid_pmem_assign_main_mem_to_wimps(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    //reveal WK_ValidObjsAddrs();

    var old_stack := wkm_stack_get_all(s.wk_mstate);
    var old_globals := wkm_get_globals(s.wk_mstate);

    var paddr_start := stack_get_val(old_stack, old_esp);
    var paddr_end := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);

    WK_ValidPMemRegion(paddr_start, paddr_end)
        // Requirement 1: paddr_start <= paddr_end
}

// [mHV] FFI: <pmem_release_main_mem_from_wimps>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] "main memory" is the physical memory address space for processes (i.e., excluding MMIOs and relevant)
// Input params on stack: (paddr_end:word) at esp + ARCH_WORD_BYTES, (paddr_start:word) at esp
// Return on stack: None
function {:axiom} ffi_pmem_release_main_mem_from_wimps(s:state) : (result:(wk_memmap, map<x86Reg, word>))
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_release_main_mem_from_wimps(s, old_esp)
    ensures ffi_preserve_sp_and_bp(s.wk_mstate, result.1)
    ensures ffi_preserve_old_stack(s.wk_mstate, result.0, FFI_PMem_ReleaseFromWimps_ReturnWords) // Words for return parameters

predicate ins_valid_pmem_release_main_mem_from_wimps(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    reveal WK_ValidObjsAddrs();

    var old_stack := wkm_stack_get_all(s.wk_mstate);
    var old_globals := wkm_get_globals(s.wk_mstate);

    var paddr_start := stack_get_val(old_stack, old_esp);
    var paddr_end := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);

    WK_ValidPMemRegion(paddr_start, paddr_end) &&
        // Requirement 1: paddr_start <= paddr_end
    (forall wimpdrv_do_id, pmem :: WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) && 
                pmem in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs &&
                is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
            ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) == WS_PartitionID(PID_INVALID))
        // Requirement 2: No active wimp driver's DO overlaps with [paddr_start, paddr_end)
}




/*********************** Predicates of external functions ********************/
// Property: <pmem_activate_main_mem_in_os> activates OS subjects and objects due to assign the memory [paddr_start, paddr_end)
// back to the OS partition
predicate {:opaque} ffi_pmem_activate_main_mem_in_os_stack_and_statevars(
    s:state, new_stack:wk_memmap, new_subjects:WSM_Subjects, new_objects:WSM_Objects, new_os_mem_active_map:PMem_Active_Map
)
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_activate_main_mem_in_os(s, old_esp)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_PMem_ActivateInOS_ReturnWords) // Return parameters take 1 word 
{
    reveal ffi_preserve_old_stack();
    reveal WK_ValidObjsAddrs();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var paddr_end:uint := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var paddr_start:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);

    ffi_pmem_activate_main_mem_in_os_stack_and_statevars_inner(s, paddr_start, paddr_end, ret, new_subjects, new_objects, new_os_mem_active_map)
}

predicate ffi_pmem_activate_main_mem_in_os_stack_and_statevars_inner(
    s:state, 
    paddr_start:word, paddr_end:word, ret:word,
    new_subjects:WSM_Subjects, new_objects:WSM_Objects, new_os_mem_active_map:PMem_Active_Map
)
    requires ValidState(s)
    requires WK_ValidPMemRegion(paddr_start, paddr_end)
{
    reveal ffi_preserve_old_stack();
    reveal WK_ValidObjsAddrs();
    var s_wkm := s.wk_mstate;
    var old_globals := wkm_get_globals(s_wkm);

    Lemma_ValidState_ProveWK_ValidObjs_ObjIDs(s);
    if(ret == TRUE) then
        var result := os_external_objs_to_be_activated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
        var os_drvs := result.0;
        var os_tds := result.1;
        var os_fds := result.2;
        var os_dos := result.3;

        (new_os_mem_active_map == ffi_pmem_activate_main_mem_in_os_update_active_map(s.os_mem_active_map, paddr_start, paddr_end)) &&
            // Property 1: <os_mem_active_map> is modified correctly
        (forall id:Drv_ID :: id in os_drvs ==> WSM_OSSubjPID(s.subjects, id.sid) == WS_PartitionID(PID_INVALID)) &&
        (forall id :: id in os_tds ==> ObjPID_OSObj(s.objects, id.oid) == WS_PartitionID(PID_INVALID)) &&
        (forall id :: id in os_fds ==> ObjPID_OSObj(s.objects, id.oid) == WS_PartitionID(PID_INVALID)) &&
        (forall id :: id in os_dos ==> ObjPID_OSObj(s.objects, id.oid) == WS_PartitionID(PID_INVALID)) &&
            // Property 2: These subjects and objects are inactive before
        (
            var os_drvs' := WSM_OSSetDrvsPIDs(s.subjects.os_drvs, os_drvs, WS_PartitionID(PID_RESERVED_OS_PARTITION));

            new_subjects == s.subjects.(os_drvs := os_drvs')
        ) &&
            // Property 3: OS's drivers are activated correctly
        (
            // Clear the objects being activated (i.e., ClearObjs)
            var temp_tds := WSM_ClearOSTDs(s.objects.os_tds, os_tds);
            var temp_fds := WSM_ClearOSFDs(s.objects.os_fds, os_fds);
            var temp_dos := WSM_ClearOSDOs(s.objects.os_dos, os_dos);

            // Modify the PID of these objects (i.e., SetPbjsPIDs)
            var os_tds' := WSM_SetOSTDsPIDs(temp_tds, os_tds, WS_PartitionID(PID_RESERVED_OS_PARTITION));
            var os_fds' := WSM_SetOSFDsPIDs(temp_fds, os_fds, WS_PartitionID(PID_RESERVED_OS_PARTITION));
            var os_dos' := WSM_SetOSDOsPIDs(temp_dos, os_dos, WS_PartitionID(PID_RESERVED_OS_PARTITION));

            new_objects == s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos')
        ) &&
            // Property 4: OS's objects are cleared and activated correctly
            // [NOTE] An object to be activated may have a larger memory than the memory to be activated here. Thus, it
            // is posssible that clearing the given memory region does not mean clearing the entire object. In this case,
            // one can always regard a sequence of Drv/DevWrite to this object happens right after this activation ops.
        (
            var r := s.(subjects := new_subjects, objects := new_objects);
            Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);

            Lemma_OSObjs_ExternalObjs_ExcludeOSDevObjs(s.subjects, s.objects, os_tds, os_fds, os_dos);
            Lemma_OSObjs_IfSetExcludeOSDevObjs_ThenAlsoExcludeOSHCodedTDs(s.subjects, os_tds);
            Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s, r);

            WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(new_subjects, new_objects, s.id_mappings, old_globals)
        ) &&
            // Property 5: The PIDs of OS subjects and objects must still fulfill 
            // <WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition>
        (
            var r := s.(subjects := new_subjects, objects := new_objects);

            forall wimpdrv_do_id:DO_ID, pmem2 :: 
                WSM_IsWimpDrvDOID(r.objects, wimpdrv_do_id) && WSM_IsActiveObj(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), wimpdrv_do_id.oid) && // Active WimpDrv's DO
                pmem2 in r.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
            ==> WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(r.objects, r.objs_addrs, pmem2.paddr_start, pmem2.paddr_end)
        )
            // Property 6: After OS drivers and objects activation, No active wimp driver's DO overlaps with active OS 
            // objects
    else
        new_subjects == s.subjects &&
        new_objects == s.objects &&
        new_os_mem_active_map == s.os_mem_active_map
}

// Property: <pmem_deactivate_main_mem_from_os> deactivates OS subjects and objects due to assign the memory 
// [paddr_start, paddr_end) to wimp drivers
predicate {:opaque} ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars(
    s:state, new_stack:wk_memmap, new_subjects:WSM_Subjects, new_objects:WSM_Objects, new_os_mem_active_map:PMem_Active_Map
)
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_activate_main_mem_in_os(s, old_esp)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_PMem_DeactivateFromOS_ReturnWords) // Return parameters take 1 word 
{
    reveal ffi_preserve_old_stack();
    reveal WK_ValidObjsAddrs();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var paddr_end:uint := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var paddr_start:word := stack_get_val(old_stack, old_esp);

    ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars_inner(s, paddr_start, paddr_end, new_subjects, new_objects, new_os_mem_active_map)
}

predicate ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars_inner(
    s:state, 
    paddr_start:word, paddr_end:word,
    new_subjects:WSM_Subjects, new_objects:WSM_Objects, new_os_mem_active_map:PMem_Active_Map
)
    requires ValidState(s)
    requires WK_ValidPMemRegion(paddr_start, paddr_end)
{
    reveal ffi_preserve_old_stack();
    reveal WK_ValidObjsAddrs();
    var s_wkm := s.wk_mstate;
    var old_globals := wkm_get_globals(s_wkm);

    Lemma_ValidState_ProveWK_ValidObjs_ObjIDs(s);

    var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var os_drvs := result.0;
    var os_tds := result.1;
    var os_fds := result.2;
    var os_dos := result.3;

    (new_os_mem_active_map == ffi_pmem_deactivate_main_mem_from_os_update_active_map(s.os_mem_active_map, paddr_start, paddr_end)) &&
        // Property 1: <os_mem_active_map> is modified correctly
    (forall id:Drv_ID :: id in os_drvs ==> WSM_OSSubjPID(s.subjects, id.sid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in os_tds ==> ObjPID_OSObj(s.objects, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in os_fds ==> ObjPID_OSObj(s.objects, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in os_dos ==> ObjPID_OSObj(s.objects, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
        // Property 2: These subjects and objects are active in the OS partition before
    (
        var os_drvs' := WSM_OSSetDrvsPIDs(s.subjects.os_drvs, os_drvs, WS_PartitionID(PID_INVALID));

        new_subjects == s.subjects.(os_drvs := os_drvs')
    ) &&
        // Property 3: OS's drivers are deactivated correctly
    (
        // Modify the PID of these objects (i.e., SetPbjsPIDs)
        var os_tds' := WSM_SetOSTDsPIDs(s.objects.os_tds, os_tds, WS_PartitionID(PID_INVALID));
        var os_fds' := WSM_SetOSFDsPIDs(s.objects.os_fds, os_fds, WS_PartitionID(PID_INVALID));
        var os_dos' := WSM_SetOSDOsPIDs(s.objects.os_dos, os_dos, WS_PartitionID(PID_INVALID));

        new_objects == s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos')
    ) &&
        // Property 4: OS's objects are deactivated correctly
    (
        var r := s.(subjects := new_subjects, objects := new_objects);
        Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
        Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s, r);

        WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(new_subjects, new_objects, s.id_mappings, old_globals)
    ) &&
        // Property 5: The PIDs of OS subjects and objects must still fulfill 
        // <WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition>
    OS_NoActiveObjectsInPMemRegion(new_objects, s.objs_addrs, paddr_start, paddr_end)
        // Property 6: No active OS objects overlaps with [paddr_start, paddr_end)
}

// Property: <pmem_assign_main_mem_to_wimps> assign the memory region [paddr_start, paddr_end) to the wimp partitions.
// The function returns true if the given memory region is inactive (i.e., no active OS objects overlaps with the memory) 
// in the OS partition
predicate {:opaque} ffi_pmem_assign_main_mem_to_wimps_stack_and_statevars(s:state, new_stack:wk_memmap)
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_assign_main_mem_to_wimps(s, old_esp)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_PMem_AssignToWimps_ReturnWords) // Return parameters take 1 word 
{
    reveal ffi_preserve_old_stack();
    reveal WK_ValidObjsAddrs();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var paddr_end:uint := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var paddr_start:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);

    if(ret == TRUE) then
        OS_NoActiveObjectsInPMemRegion(s.objects, s.objs_addrs, paddr_start, paddr_end)
            // Property 1: No active OS objects overlaps with [paddr_start, paddr_end)
    else
        true
}