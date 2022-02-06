include "../../../ins/util/ffi.s.dfy"
include "../../../state_properties_validity.s.dfy"
include "../../../utils/model/utils_objs_valid_state.s.dfy"

/*********************** Outputs of external functions ********************/
const FFI_USBPDev_Clear_StackParamsWords:int := 2;

// [USBPDev Clearing] FFI (external component): "usbpdev_clear", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE-Important] <usbpdev_clear> method must preserve the USBPDev's ID; e.g., hub USB address and device USB address. 
// Because USB devices are assigned to be USB address 0 after resetting them, WK must backup and restore USB device's 
// address in the <usbpdev_clear> method
// Input params on stack: (usbpdev_addr_high:word) at esp + ARCH_WORD_BYTES, (usbpdev_addr_low:word) at esp
// Return params on stack: None
function {:axiom} ffi_usbpdev_clear(s:state) : (result:(wk_memmap, map<x86Reg, word>, WSM_Objects)) 
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_USBPDev_Clear_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_usbpdev_clear(s, old_esp)

    ensures var s_wkm := s.wk_mstate;
            ffi_preserve_sp_and_bp(s_wkm, result.1)
    ensures var s_wkm := s.wk_mstate;
            ffi_preserve_old_stack(s_wkm, result.0, 0) // Return parameters take 0 word

    ensures p_ffi_usbpdev_clear_retval(s, result.0, result.2)

predicate ins_valid_usbpdev_clear(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_USBPDev_Clear_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    var old_stack := wkm_stack_get_all(s.wk_mstate);
    var old_globals := wkm_get_globals(s.wk_mstate);

    var usbpdev_addr_low := stack_get_val(old_stack, old_esp);
    var usbpdev_addr_high := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var usbpdev_addr_raw := UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low);
    usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
    var addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
    var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    usb_is_usbpdev_addr_valid(empty_addr) &&
    addr != usb_parse_usbpdev_addr(empty_addr) &&
        // Requirement: The USBPDev must be located at a non-empty address
    Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs
}

// Modify all USBPDevs's PIDs to be the OS partition's PID.
// This function/predicate is based on the axiom mentioned in <OS_Activate_AllReleasedPEHCIsAndUSBPDevs>
function {:axiom} AXIOM_Assign_USBPDevs_To_OS_Partition_Property(s:state) : (result_subjs:WSM_Subjects)
    ensures result_subjs.wimp_drvs == s.subjects.wimp_drvs &&
            result_subjs.eehcis == s.subjects.eehcis &&
            result_subjs.os_drvs == s.subjects.os_drvs &&
            result_subjs.os_devs == s.subjects.os_devs
        // Other subjects is unchanged
    ensures MapGetKeys(result_subjs.usbpdevs) == MapGetKeys(s.subjects.usbpdevs)
    ensures forall id :: id in s.subjects.usbpdevs
                ==> result_subjs.usbpdevs[id].hcoded_td_id == s.subjects.usbpdevs[id].hcoded_td_id &&
                    result_subjs.usbpdevs[id].fd_ids == s.subjects.usbpdevs[id].fd_ids &&
                    result_subjs.usbpdevs[id].do_ids == s.subjects.usbpdevs[id].do_ids
    ensures forall id :: id in s.subjects.usbpdevs
                ==> result_subjs.usbpdevs[id].active_in_os == true
        // Only <active_in_os> of all USBPDevs is set to true




/*********************** Predicates of external functions ********************/
// Property: Correctness properties of the return values of <usbpdev_clear> 
predicate {:opaque} p_ffi_usbpdev_clear_retval(s:state, new_stack:wk_memmap, new_objs:WSM_Objects)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_USBPDev_Clear_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_usbpdev_clear(s, old_esp)
    requires var s_wkm := s.wk_mstate; 
             ffi_preserve_old_stack(s_wkm, new_stack, 0) // Return parameters take 0 word
{
    reveal ffi_preserve_old_stack();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var usbpdev_addr_low := stack_get_val(old_stack, old_esp);
    var usbpdev_addr_high := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var addr:USBPDev_Addr := usb_parse_usbpdev_addr(UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low));
    var dev_id := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr);

    p_ffi_usbpdev_clear_objects(s, new_objs, dev_id)
}

predicate p_ffi_usbpdev_clear_objects(s:state, new_objs:WSM_Objects, dev_id:Dev_ID)
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires dev_id in s.subjects.usbpdevs
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    var usbpdev_fd_ids := s.subjects.usbpdevs[dev_id].fd_ids;
    var usbpdev_do_ids := s.subjects.usbpdevs[dev_id].do_ids;

    // Other objects are unchanged
    s.objects.os_tds == new_objs.os_tds &&
    s.objects.os_fds == new_objs.os_fds &&
    s.objects.os_dos == new_objs.os_dos &&
    s.objects.eehci_hcoded_tds == new_objs.eehci_hcoded_tds &&
    s.objects.eehci_other_tds == new_objs.eehci_other_tds &&
    s.objects.eehci_fds == new_objs.eehci_fds &&
    s.objects.eehci_dos == new_objs.eehci_dos &&
    s.objects.usbtd_tds == new_objs.usbtd_tds &&
    s.objects.usbtd_fds == new_objs.usbtd_fds &&
    s.objects.usbtd_dos == new_objs.usbtd_dos &&
    s.objects.wimpdrv_dos == new_objs.wimpdrv_dos &&
    s.objects.usbpdev_tds == new_objs.usbpdev_tds &&

    // In <usbpdev_fds>, clear the contents of the USBPDev's FDs only
    MapGetKeys(s.objects.usbpdev_fds) == MapGetKeys(new_objs.usbpdev_fds) &&
    (forall fd_id2 :: (fd_id2 in s.objects.usbpdev_fds) && (fd_id2 !in usbpdev_fd_ids)
        ==> s.objects.usbpdev_fds[fd_id2] == new_objs.usbpdev_fds[fd_id2]) &&
    (forall fd_id2 :: fd_id2 in usbpdev_fd_ids
        ==> WSM_IsFDClearVal(new_objs.usbpdev_fds, fd_id2)) &&
    
    // In <usbpdev_dos>, clear the contents of the USBPDev's DOs only
    MapGetKeys(s.objects.usbpdev_dos) == MapGetKeys(new_objs.usbpdev_dos) &&
    (forall do_id2 :: (do_id2 in s.objects.usbpdev_dos) && (do_id2 !in usbpdev_do_ids)
        ==> s.objects.usbpdev_dos[do_id2] == new_objs.usbpdev_dos[do_id2]) &&
    (forall do_id2 :: do_id2 in usbpdev_do_ids
        ==> WSM_IsDOClearVal(new_objs.usbpdev_dos, do_id2)) &&
    
    (true)
}

predicate usbpdev_clear_non_mstate_relationship(s1:state, s2:state, addr:USBPDev_Addr)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             addr != usb_parse_usbpdev_addr(empty_addr)
        // Requirement: The USBPDev must be located at a non-empty address
    requires Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs
{
    var dev_id := Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr);

    // Immutable state variables
    s1.subjects == s2.subjects &&
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&

    // Relationship of objects
    p_ffi_usbpdev_clear_objects(s1, s2.objects, dev_id) &&

    (true)
}