include "../ins/util/ffi.s.dfy"
include "drv.s.dfy"
include "../state_properties_validity.s.dfy"
include "../utils/model/utils_objs_valid_state.s.dfy"

/*********************** Outputs of external functions ********************/
const FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords:int := 1;

const FFI_WimpDrv_DO_Clear_StackParamsWords:int := 1;
const FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords:int := 2;

// [WimpDrv] FFI: "wimpdrv_DO_clear", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, because the external component of wimp app process management may provide this function
// Input params on stack: (drv_slot:word) at esp
// Return params on stack: None
function {:axiom} ffi_wimpdrv_DO_clear(s:state) : (result:(wk_memmap, map<x86Reg, word>, WSM_Objects)) 
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             IsAddrInStack(old_esp + FFI_WimpDrv_DO_Clear_StackParamsWords * ARCH_WORD_BYTES - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_wimpdrv_DO_clear(s, old_esp)

    ensures var s_wkm := s.wk_mstate;
            ffi_preserve_sp_and_bp(s_wkm, result.1)
    ensures var s_wkm := s.wk_mstate;
            ffi_preserve_old_stack(s_wkm, result.0, 0) // Return parameters take 0 word

    ensures p_ffi_wimpdrv_DO_clear_retval(s, result.0, result.2)

predicate ins_valid_wimpdrv_DO_clear(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_WimpDrv_DO_Clear_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    var old_stack := wkm_stack_get_all(s.wk_mstate);
    var old_globals := wkm_get_globals(s.wk_mstate);

    var drv_slot := stack_get_val(old_stack, old_esp);

    wimpdrv_valid_slot_id(drv_slot) &&
    wimpdrv_do_get_flag(old_globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&
        // One should clear the wimp driver's DO after filling the info of the wimp driver
    var drv_id := wimpdrv_get_id_word(old_globals, drv_slot);
    drv_id != WimpDrv_ID_RESERVED_EMPTY &&
    WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id) in s.subjects.wimp_drvs
}

// [To-implement] FFI
// Desired properties of the external function "wimpdrv_DO_check_paddr_range", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// Input params on stack: (do_pend:paddr) at esp + ARCH_WORD_BYTES, (do_pbase:paddr) at esp
// Return params on stack: (ret:word) at esp
function {:axiom} ffi_wimpdrv_DO_check_paddr_range(s:state) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address

    ensures var s_wkm := s.wk_mstate;
            ffi_preserve_sp_and_bp(s_wkm, result.1)
    ensures var s_wkm := s.wk_mstate;
            ffi_preserve_old_stack(s_wkm, result.0, FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords) // Return parameters take 1 word

    ensures p_ffi_wimpdrv_DO_check_paddr_range_retval(s, result.0)




/*********************** Predicates of external functions ********************/
// Property: Correctness properties of the return values of <wimpdrv_DO_clear> 
predicate {:opaque} p_ffi_wimpdrv_DO_clear_retval(s:state, new_stack:wk_memmap, new_objs:WSM_Objects)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_WimpDrv_DO_Clear_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_wimpdrv_DO_clear(s, old_esp)
    requires var s_wkm := s.wk_mstate; 
             ffi_preserve_old_stack(s_wkm, new_stack, 0) // Return parameters take 0 word
{
    reveal ffi_preserve_old_stack();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var drv_slot := stack_get_val(old_stack, old_esp);
    var drv_id := wimpdrv_get_id_word(old_globals, drv_slot);

    var do_id := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id);

    p_ffi_wimpdrv_DO_clear_objects(s, new_objs, do_id)
}

predicate p_ffi_wimpdrv_DO_clear_objects(s:state, new_objs:WSM_Objects, do_id:DO_ID)
    requires do_id in s.objects.wimpdrv_dos
{
    // Other objects are unchanged
    s.objects.os_tds == new_objs.os_tds &&
    s.objects.os_fds == new_objs.os_fds &&
    s.objects.os_dos == new_objs.os_dos &&
    s.objects.eehci_hcoded_tds == new_objs.eehci_hcoded_tds &&
    s.objects.eehci_other_tds == new_objs.eehci_other_tds &&
    s.objects.eehci_fds == new_objs.eehci_fds &&
    s.objects.eehci_dos == new_objs.eehci_dos &&
    s.objects.usbpdev_tds == new_objs.usbpdev_tds &&
    s.objects.usbpdev_fds == new_objs.usbpdev_fds &&
    s.objects.usbpdev_dos == new_objs.usbpdev_dos &&
    s.objects.usbtd_tds == new_objs.usbtd_tds &&
    s.objects.usbtd_fds == new_objs.usbtd_fds &&
    s.objects.usbtd_dos == new_objs.usbtd_dos &&
    
    // Clear the content of the wimp driver's DO only
    MapGetKeys(s.objects.wimpdrv_dos) == MapGetKeys(new_objs.wimpdrv_dos) &&
    (forall do_id2 :: do_id2 in s.objects.wimpdrv_dos && do_id2 != do_id
        ==> s.objects.wimpdrv_dos[do_id2] == new_objs.wimpdrv_dos[do_id2]) &&
    WSM_IsDOClearVal(new_objs.wimpdrv_dos, do_id)
}

predicate wimpdrv_DO_clear_non_mstate_relationship(s1:state, s2:state, drv_id:word)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)
    requires drv_id != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(s1.subjects, s1.objects, s1.id_mappings, drv_id) in s1.subjects.wimp_drvs 
{
    var do_id := WimpDrv_GetDOID(s1.subjects, s1.objects, s1.id_mappings, drv_id);

    // Immutable state variables
    s1.subjects == s2.subjects &&
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&

    // Relationship of objects
    p_ffi_wimpdrv_DO_clear_objects(s1, s2.objects, do_id) &&

    (true)
}

// Property: Correctness properties of the return values of <wimpdrv_DO_check_paddr_range> 
predicate {:opaque} p_ffi_wimpdrv_DO_check_paddr_range_retval(s:state, new_stack:wk_memmap)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate; 
             ffi_preserve_old_stack(s_wkm, new_stack, FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords) // Return parameters take 1 word
{
    reveal ffi_preserve_old_stack();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var do_pbase := stack_get_val(old_stack, old_esp);
    var do_pend := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var ret := stack_get_val(new_stack, old_esp);

    (ret == TRUE) ==> (
        do_pbase <= do_pend &&
            // A valid paddr memory range
        (forall i:uint32 :: wimpdrv_valid_slot_id(i) && wimpdrv_do_get_flag(old_globals, i) == WimpDrv_Slot_UpdateFlag_Complete &&
                wimpdrv_get_pid(old_globals, i) != WS_PartitionID(PID_INVALID)
            ==> !is_mem_region_overlap(wimpdrv_do_get_paddr_base(old_globals, i), wimpdrv_do_get_paddr_end(old_globals, i), 
                    do_pbase, do_pend))
            // The DO paddr region of the new wimp driver does not overlap with existing submitted wimp drivers
    )
}