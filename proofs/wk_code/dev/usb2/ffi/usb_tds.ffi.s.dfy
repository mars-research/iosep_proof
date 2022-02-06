include "../../../ins/util/ffi.s.dfy"
include "../../../state_properties_validity.s.dfy"
include "../usb_tds.i.dfy"

// Predicate: The USB qTD referred by <td_vaddr> must be stored in <g_usbtd_map_mem>
// [NOTE] Deprecated
predicate usbtd_ffi_valid_usbtd_vaddr_on_stack(td_vaddr:addr)
    requires is_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()) + G_USBTDs_MAP_MEM_SZ_Tight)
{
    var td_vaddr_end := td_vaddr + MAX_USB_TD_BYTES;
    var usbtd_mem_vbase := AddressOfGlobal(G_USBTD_MAP_MEM());
    var usbtd_mem_vend := usbtd_mem_vbase + G_USBTDs_MAP_MEM_SZ_Tight;

    is_valid_vaddr(td_vaddr) && (td_vaddr_end <= usbtd_mem_vend) &&
    is_mem_region_inside(usbtd_mem_vbase, usbtd_mem_vend, td_vaddr, td_vaddr_end)
}




/*********************** Outputs of external functions ********************/
const FFI_USBTD_CopyFromUser_ReturnWords:int := 1;
const FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords:int := 1;

const FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords:int := 4;
const FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords:int := 5;

const FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords:int := 6;
const FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords:int := 5;
const FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords:int := 3;

const FFI_USBTD_FSTN32_ParseTDPtrs_ReturnWords:int := 4;
const FFI_USBTD_IsRefTargetUSBTD_ReturnWords:int := 1;

// <StackParamsWords> = max(input_params, output_params)
const FFI_USBTD_CopyFromUser_StackParamsWords:int := 5;
const FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords:int := 1;
const FFI_USBTD_Backup_StackParamsWords:int := 1;
const FFI_USBTD_Restore_StackParamsWords:int := 1;
const FFI_USBTD_IsRefTargetUSBTD_StackParamsWords:int := 2;
const FFI_USBTD_Clear_Content_StackParamsWords:int := 2;

const FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords:int := FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords;
const FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords:int := FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords;

const FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords:int := FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords;
const FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords:int := FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords;
const FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords:int := FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords;

const FFI_USBTD_FSTN32_ParseTDPtrs_StackParamsWords:int := FFI_USBTD_FSTN32_ParseTDPtrs_ReturnWords;

// [USB TD] FFI: "usbtd_qtd32_parseQTDpointer", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word) at esp
// Return params on stack: (next_qtd_p_Tflag:word/bool) at esp + 3 * ARCH_WORD_BYTES, 
// (alt_next_qtd_p_Tflag:word/bool) at esp + 2 * ARCH_WORD_BYTES
// (next_qtd_slot:word) at esp + ARCH_WORD_BYTES, (alt_next_qtd_slot:word) at esp
function {:axiom} ffi_usbtd_qtd32_parseTDPtrs(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_qtd32_parseTDPtrs_retval(old_wkm, result.0)

// [USB TD] FFI: "usbtd_qtd32_parseBufpointer", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word) at esp
// Return params on stack: (BufPointer4:word) at esp + 4 * ARCH_WORD_BYTES, (BufPointer3:word) at esp + 3 * ARCH_WORD_BYTES, 
// (BufPointer2:word) at esp + 2 * ARCH_WORD_BYTES
// (BufPointer1:word) at esp + ARCH_WORD_BYTES, (BufPointer0:word) at esp
function {:axiom} ffi_usbtd_qtd32_parseDataBufPtrs(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_qtd32_parseDataBufPtrs_retval(old_wkm, result.0)

// [USB TD] FFI: "usbtd_qh32_parseTDPtrs", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word) at esp
// Return params on stack: (next_qh_p_Tflag:word/bool) at esp + 5 * ARCH_WORD_BYTES, 
// (next_qtd_p_Tflag:word/bool) at esp + 4 * ARCH_WORD_BYTES, (alt_next_qtd_p_Tflag:word/bool) at esp + 3 * ARCH_WORD_BYTES
// (next_qh_slot:paddr) at esp + 2 * ARCH_WORD_BYTES (next_qtd_slot:paddr) at esp + ARCH_WORD_BYTES, (alt_next_qtd_slot:paddr) at esp
function {:axiom} ffi_usbtd_qh32_parseTDPtrs(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(slot)
        // Requirement: The USB QH referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_qh32_parseTDPtrs_retval(old_wkm, result.0)

// [USB TD] FFI: "usbtd_qh32_parseDataBufPtrs", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word) at esp
// Return params on stack: (BufPointer4:word) at esp + 4 * ARCH_WORD_BYTES, (BufPointer3:word) at esp + 3 * ARCH_WORD_BYTES, 
// (BufPointer2:word) at esp + 2 * ARCH_WORD_BYTES
// (BufPointer1:word) at esp + ARCH_WORD_BYTES, (BufPointer0:word) at esp
function {:axiom} ffi_usbtd_qh32_parseDataBufPtrs(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(slot)
        // Requirement: The USB QH referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_qh32_parseDataBufPtrs_retval(old_wkm, result.0)

// [USB TD] FFI: "usbtd_qh32_parseTargetUSBDevID", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word) at esp
// Return params on stack: (ret:word/bool) at esp, (dev_addr_low:uint32) at esp + ARCH_WORD_BYTES,
// (dev_addr_high:uint32) at esp + 2 * ARCH_WORD_BYTES
function {:axiom} ffi_usbtd_qh32_parseTargetUSBDevID(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(slot)
        // Requirement: The USB QH referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_qh32_parseTargetUSBDevID_retval(old_wkm, result.0)







// [USB TD] FFI: "usbtd_fstn32_parseTDPtrs", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_vaddr:byte* (32-bytes aligned)) at esp
// Return params on stack: (normal_link_p_Tflag:word/bool) at esp + 3 * ARCH_WORD_BYTES, 
// (back_link_p_Tflag:word/bool) at esp + 2 * ARCH_WORD_BYTES
// (normal_link_p:word) at esp + ARCH_WORD_BYTES, (back_link_p:word) at esp
function {:axiom} ffi_usbtd_fstn32_parseTDPtrs(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_USBTD_FSTN32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_vaddr := stack_get_val(old_stack, old_esp);
            usbtd_ffi_valid_usbtd_vaddr_on_stack(td_vaddr)
        // Requirement: The USB FSTN referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_FSTN32_ParseTDPtrs_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_fstn32_parseTDPtrs_retval(old_wkm, result.0)

// [USB TD] FFI: <usbtd_copy_from_user>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] This function is an FFI, so one could easily support different sources of new TD values
// Input params on stack: (td_size:word) at esp + 4 * ARCH_WORD_BYTES, (td_paddr:paddr) at esp + 3 * ARCH_WORD_BYTES, 
// (wimpdrv_id:word) at esp + 2 * ARCH_WORD_BYTES, (wimpdrv_slot_id:word) at esp + ARCH_WORD_BYTES, 
// (slot:word/uint32) at esp
// Return on stack: (ret:uint32) at esp
function {:axiom} ffi_usbtd_copy_from_user(old_wkm:WK_MState) : (result:(wk_memmap, globalsmap, map<x86Reg, word>))
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    ensures ffi_preserve_sp_and_bp(old_wkm, result.2)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_CopyFromUser_ReturnWords) // Return parameters take 1 word 
    ensures WK_ValidGlobalVars_Decls(result.1)
    ensures ffi_usbtd_copy_from_user_stack_and_globals(old_wkm, result.0, result.1)
                // Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot 
                // and eehci_id correctly

// [USB TD] FFI: <usbtd_check_not_modify_usbpdev_addrs>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] This function is an FFI, so one could easily support different sources of new TD values
// Input params on stack: (td_slot:word/uint32) at esp
// Return on stack: (ret:uint32) at esp
function {:axiom} ffi_usbtd_check_not_modify_usbpdev_addrs(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>))
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords) // Return parameters take 1 word 
    ensures ffi_ffi_usbtd_check_not_modify_usbpdev_addrs_stack_and_globals(old_wkm, result.0)
                // Property: <usbtd_check_not_modify_usbpdev_addrs> checks the given USB TD correctly

// [USB TD] FFI: <usbtd_backup>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word/uint32) at esp
// Return on stack: None
function {:axiom} ffi_usbtd_backup(old_wkm:WK_MState) : (result:(wk_memmap, globalsmap, map<x86Reg, word>))
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Backup_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot)
    ensures ffi_preserve_sp_and_bp(old_wkm, result.2)
    ensures ffi_preserve_old_stack(old_wkm, result.0, 0) // Return parameters take 0 word 
    ensures WK_ValidGlobalVars_Decls(result.1)
    ensures ffi_usbtd_backup_stack_and_globals(old_wkm, result.1)
                // Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot 
                // and eehci_id correctly


// [USB TD] FFI: <usbtd_restore>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_slot:word/uint32) at esp
// Return on stack: None
function {:axiom} ffi_usbtd_restore(old_wkm:WK_MState) : (result:(wk_memmap, globalsmap, map<x86Reg, word>))
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
            ins_valid_usbtd_restore(wkm_stack_get_all(old_wkm), wkm_get_globals(old_wkm), old_esp)
    ensures ffi_preserve_sp_and_bp(old_wkm, result.2)
    ensures ffi_preserve_old_stack(old_wkm, result.0, 0) // Return parameters take 0 word 
    ensures WK_ValidGlobalVars_Decls(result.1)
    ensures ffi_usbtd_restore_stack_and_globals(old_wkm, result.1)
                // Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot 
                // and eehci_id correctly

// Is the instruction operand <o> for call instructions a valid source operand?
predicate ins_valid_usbtd_restore(old_stack:wk_memmap, old_globals:globalsmap, old_esp:vaddr)
    requires x86wk_valid_memstate(old_stack)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES)
{
    var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
    var td_slot := stack_get_val(old_stack, old_esp); 

    usbtd_map_valid_slot_id(td_slot) &&
    TestBit(usbtd_map_get_flags(old_globals, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false &&
        // Must not restore to a verified/secure USB TD
    eehci_mem_no_ref_to_usbtd_slot(old_globals, td_slot) &&

    (
        // No duplicate USBTD ID after restore
        forall i :: usbtd_map_valid_slot_id(i) && i != td_slot &&
                usbtd_map_get_idword(old_globals, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(old_globals, i) != usbtd_temp_get_id(old_globals)
    ) &&

    usbtd_temp_valid_id(old_globals) &&
    usbtd_temp_valid_pid(old_globals) &&
    usbtd_temp_valid_type(old_globals) &&
    usbtd_temp_valid_busid(old_globals) && 
    usbtd_temp_valid_wimpdrv_slotid(old_globals) && 
    usbtd_temp_valid_usbpdev_slotid(old_globals) &&
    usbtd_temp_get_flags(old_globals) == 0
}

predicate ins_valid_usbtd_clear_content(old_stack:wk_memmap, old_globals:globalsmap, old_esp:vaddr)
    requires x86wk_valid_memstate(old_stack)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
    var td_slot := stack_get_val(old_stack, old_esp); 
    var td_type := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);

    usbtd_map_valid_slot_id(td_slot) &&
    TestBit(usbtd_map_get_flags(old_globals, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false &&
        // Must not clear to a verified/secure USB TD
    eehci_mem_no_ref_to_usbtd_slot(old_globals, td_slot) &&
    (
        (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32) || 
        (td_type == USBTDs_TYPE_iTD32) || (td_type == USBTDs_TYPE_siTD32)
    )
}

// [To-implement] FFI
// Desired properties of the external function "usbtd_is_ref_target_usbtd", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// Input params on stack: (refed_td_slot:word) at esp + ARCH_WORD_BYTES, (td_slot:word) at esp
// Return params on stack: (ret:word/bool) at esp
function {:axiom} ffi_usbtd_is_ref_target_usbtd(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_USBTD_IsRefTargetUSBTD_ReturnWords) // Words for return parameters 

    ensures p_ffi_usbtd_is_ref_target_usbtd_retval(old_wkm, result.0)

// [USB TD] FFI: <usbtd_clear_content>
// This function changes regs, stack and global on return, but nothing else
// [NOTE] This function is an FFI, so one could easily support various types of USB TDs, even for different USB versions
// Input params on stack: (td_type:word/uint32) at esp + ARCH_WORD_BYTES, (td_slot:word/uint32) at esp
// Return on stack: None
function {:axiom} ffi_usbtd_clear_content(old_wkm:WK_MState) : (result:(wk_memmap, globalsmap, map<x86Reg, word>))
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
            ins_valid_usbtd_clear_content(wkm_stack_get_all(old_wkm), wkm_get_globals(old_wkm), old_esp)
    ensures ffi_preserve_sp_and_bp(old_wkm, result.2)
    ensures ffi_preserve_old_stack(old_wkm, result.0, 0) // Return parameters take 0 word 
    ensures WK_ValidGlobalVars_Decls(result.1)
    ensures ffi_usbtd_clear_content_stack_and_globals(old_wkm, result.1)
                // Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot 
                // and eehci_id correctly




/*********************** Predicates of external functions ********************/
// Property: Correctness properties of the return values of <usbtd_qtd32_parseQTDpointers> 
predicate {:opaque} p_ffi_usbtd_qtd32_parseTDPtrs_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_slot> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var out_next_qtd_p_Tflag := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var out_alt_next_qtd_p_Tflag := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var out_next_qtd_slot:word := stack_get_val(new_stack, old_esp + 1 * ARCH_WORD_BYTES);
    var out_alt_next_qtd_slot:word := stack_get_val(new_stack, old_esp);

    var td_slot := stack_get_val(old_stack, old_esp);
    var result := usbtd_qtd32_parse_TDPtrs_from_global(old_globals, td_slot);

    var td_next_qtd_slot:uint32 := result.0;
    var td_alt_next_qtd_slot:uint32 := result.1;
    var next_qtd_p_Tflag:uint32 := result.2;
    var alt_next_qtd_p_Tflag:uint32 := result.3;

    out_next_qtd_p_Tflag == next_qtd_p_Tflag &&
    out_alt_next_qtd_p_Tflag == alt_next_qtd_p_Tflag &&
    out_next_qtd_slot == td_next_qtd_slot && 
    out_alt_next_qtd_slot == td_alt_next_qtd_slot
}

// Property: Correctness properties of the return values of <usbtd_qtd32_parseBUFpointers>
predicate {:opaque} p_ffi_usbtd_qtd32_parseDataBufPtrs_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_slot> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var out_buf4_p:word := stack_get_val(new_stack, old_esp + 4 * ARCH_WORD_BYTES);
    var out_buf3_p:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var out_buf2_p:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var out_buf1_p:word := stack_get_val(new_stack, old_esp + 1 * ARCH_WORD_BYTES);
    var out_buf0_p:word := stack_get_val(new_stack, old_esp);

    var td_vaddr := stack_get_val(old_stack, old_esp);
    var result := usbtd_qtd32_parse_DataBufPtrs_from_global(old_globals, td_vaddr);

    var r_buf0_p:uint32 := result.0;
    var r_buf1_p:uint32 := result.1;
    var r_buf2_p:uint32 := result.2;
    var r_buf3_p:uint32 := result.3;
    var r_buf4_p:uint32 := result.4;
    
    (out_buf0_p == r_buf0_p) && (out_buf1_p == r_buf1_p) && (out_buf2_p == r_buf2_p) && (out_buf3_p == r_buf3_p) && (out_buf4_p == r_buf4_p)
}

// Property: Correctness properties of the return values of <usbtd_qh32_parseTDPtrs> 
predicate {:opaque} p_ffi_usbtd_qh32_parseTDPtrs_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(slot)
        // Requirement: The USB qTD referred by <td_addr> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var out_next_qh_p_Tflag := stack_get_val(new_stack, old_esp + 5 * ARCH_WORD_BYTES);
    var out_next_qtd_p_Tflag := stack_get_val(new_stack, old_esp + 4 * ARCH_WORD_BYTES);
    var out_alt_next_qtd_p_Tflag := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var out_next_qh_slot:paddr := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var out_next_qtd_slot:paddr := stack_get_val(new_stack, old_esp + 1 * ARCH_WORD_BYTES);
    var out_alt_next_qtd_slot:paddr := stack_get_val(new_stack, old_esp);

    var td_slot := stack_get_val(old_stack, old_esp);
    var result := usbtd_qh32_parse_TDPtrs_from_global(old_globals, td_slot);

    var next_qh_slot:uint32 := result.0;
    var next_qtd_slot:uint32 := result.1; 
    var alt_next_qtd_slot:uint32 := result.2;
    var next_qh_p_Tflag:uint32 := result.3;
    var next_qtd_p_Tflag:uint32 := result.4;
    var alt_next_qtd_p_Tflag:uint32 := result.5;

    out_next_qh_p_Tflag == next_qh_p_Tflag &&
    out_next_qtd_p_Tflag == next_qtd_p_Tflag &&
    out_alt_next_qtd_p_Tflag == alt_next_qtd_p_Tflag &&
    out_next_qh_slot == next_qh_slot &&
    out_next_qtd_slot == next_qtd_slot && 
    out_alt_next_qtd_slot == alt_next_qtd_slot
}

// Property: Correctness properties of the return values of <usbtd_qh32_parseDataBufPtrs>
predicate {:opaque} p_ffi_usbtd_qh32_parseDataBufPtrs_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_addr> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var out_buf4_p:word := stack_get_val(new_stack, old_esp + 4 * ARCH_WORD_BYTES);
    var out_buf3_p:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var out_buf2_p:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var out_buf1_p:word := stack_get_val(new_stack, old_esp + 1 * ARCH_WORD_BYTES);
    var out_buf0_p:word := stack_get_val(new_stack, old_esp);

    var td_slot := stack_get_val(old_stack, old_esp);
    var result := usbtd_qh32_parse_DataBufPtrs_from_global(old_globals, td_slot);

    var r_buf0_p:uint32 := result.0;
    var r_buf1_p:uint32 := result.1;
    var r_buf2_p:uint32 := result.2;
    var r_buf3_p:uint32 := result.3;
    var r_buf4_p:uint32 := result.4;
    
    (out_buf0_p == r_buf0_p) && (out_buf1_p == r_buf1_p) && (out_buf2_p == r_buf2_p) && (out_buf3_p == r_buf3_p) && (out_buf4_p == r_buf4_p)
}

// Property: Correctness properties of the return values of <usbtd_qh32_parseTargetUSBDevID> 
predicate {:opaque} p_ffi_usbtd_qh32_parseTargetUSBDevID_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(slot)
        // Requirement: The USB qTD referred by <slot> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var ret:word := stack_get_val(new_stack, old_esp);
    var out_dev_addr_low := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var out_dev_addr_high := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var out_dev_id_uint64:uint64 := UInt64_FromTwoUInt32s(out_dev_addr_high, out_dev_addr_low);
    var slot := stack_get_val(old_stack, old_esp);
    
    if(ret == TRUE) then
            // 1. The <out_dev_id_uint64> must represent a valid USBPDev ID
        usb_is_usbpdev_addr_valid(out_dev_id_uint64) &&
            // 2. The value in the global variable must be a valid USBPDev ID
        usbtd_qh32_can_parse_TargetUSBDevID_from_global(old_globals, slot) &&
            // 3. The returned USBPDev ID is the ID in the global variable
        (
            var expect_id:USBPDev_Addr := usbtd_qh32_parse_TargetUSBPDevAddr_from_global(old_globals, slot);
            var out_dev_id:USBPDev_Addr := usb_parse_usbpdev_addr(out_dev_id_uint64);
            out_dev_id == expect_id
        )
    else
        // If ret == FALSE, then <out_dev_id_uint64> could be anything
        true
}



// Property: Correctness properties of the return values of <usbtd_fstn32_parseTDPtrs> 
predicate {:opaque} p_ffi_usbtd_fstn32_parseTDPtrs_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_FSTN32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_FSTN32_ParseTDPtrs_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_vaddr := stack_get_val(old_stack, old_esp);
            usbtd_ffi_valid_usbtd_vaddr_on_stack(td_vaddr)
        // Requirement: The USB qTD referred by <td_addr> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var out_normal_link_p_Tflag := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var out_back_link_p_Tflag := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var out_normal_link_p:paddr := stack_get_val(new_stack, old_esp + 1 * ARCH_WORD_BYTES);
    var out_back_link_p:paddr := stack_get_val(new_stack, old_esp);

    var td_addr := stack_get_val(old_stack, old_esp);

    var normal_link_p:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_addr), 0xFFFFFFE0); // According to EHCI specification, Section 3.7
    var back_link_p:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES), 0xFFFFFFE0); 
    var normal_link_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_addr), 0x1);
    var back_link_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES), 0x1);

    out_normal_link_p_Tflag == normal_link_p_Tflag &&
    out_back_link_p_Tflag == back_link_p_Tflag &&
    out_normal_link_p == normal_link_p && 
    out_back_link_p == back_link_p
}

// Property: <usbtd_copy_from_user> copies the USB TD from wimp driver to the given <slot> of <g_usbtd_mem_map>
predicate {:opaque} ffi_usbtd_copy_from_user_stack_and_globals(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_CopyFromUser_ReturnWords) // Return parameters take 1 word 
    requires WK_ValidGlobalVars_Decls(new_globals)
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var td_size:word := stack_get_val(old_stack, old_esp + 4 * ARCH_WORD_BYTES);
    var td_paddr:word := stack_get_val(old_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var wimpdrv_id:word := stack_get_val(old_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var wimpdrv_slot_id:word := stack_get_val(old_stack, old_esp + 1 * ARCH_WORD_BYTES);
    var slot:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);

    
    var slot_td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;

    if(ret == TRUE) then
        // 1. The wimp driver at <wimpdrv_slot_id> must be good
        (0 <= wimpdrv_slot_id < WimpDrv_Info_ENTRIES) &&
        (wimpdrv_do_get_flag(old_globals, wimpdrv_slot_id) == WimpDrv_Slot_UpdateFlag_Complete) &&
        // 2. <td_size> must be between (0, MAX_USB_TD_BYTES]
        (0 < td_size <= MAX_USB_TD_BYTES) &&
        // 3. The end of the copy source TD must be a valid paddr
        (is_valid_addr(td_paddr + td_size)) &&
        // 4. The target slot of USB TD is valid
        usbtd_map_valid_slot_id(slot) &&
        // 5. The copy source TD must be inside the given wimp driver's DO
        (
            var do_pbase:paddr := wimpdrv_do_get_paddr_base(old_globals, wimpdrv_slot_id);
            var do_pend:paddr := wimpdrv_do_get_paddr_end(old_globals, wimpdrv_slot_id);
            is_mem_region_inside(do_pbase, do_pend, td_paddr, td_paddr + td_size)
        ) &&
        // 6. Only the target USB TD's content is modified
        (
            ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals, new_globals, slot)
        ) &&
        // 7. The flag of the USB TD is 0
        (usbtd_map_get_flags(old_globals, slot) == 0)
    else
        new_globals == old_globals
}

// Property: <usbtd_check_not_modify_usbpdev_addrs> checks if the given USB TD has the functionality to modify any USBPDevs' addrs
predicate {:opaque} ffi_ffi_usbtd_check_not_modify_usbpdev_addrs_stack_and_globals(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords) // Return parameters take 1 word 
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var td_slot:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);

    if(ret == TRUE) then
        usbtd_map_valid_slot_id(td_slot) &&
        Is_USBTD_NotModifyUSBPDevsAddrs(old_globals, td_slot)
    else
        !usbtd_map_valid_slot_id(td_slot) || !Is_USBTD_NotModifyUSBPDevsAddrs(old_globals, td_slot)
}

predicate {:opaque} ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)
{
    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

    exists new_vals:seq<uint32> :: |new_vals| == MAX_USB_TD_BYTES/UINT32_BYTES &&
        (
            var new_globals1 := global_write_at_vaddr32(old_globals, G_USBTD_MAP_MEM(), td_addr, new_vals[0]);
            var new_globals2 := global_write_at_vaddr32(new_globals1, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES, new_vals[1]);
            var new_globals3 := global_write_at_vaddr32(new_globals2, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES, new_vals[2]);
            var new_globals4 := global_write_at_vaddr32(new_globals3, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES, new_vals[3]);
            var new_globals5 := global_write_at_vaddr32(new_globals4, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES, new_vals[4]);

            var new_globals6 := global_write_at_vaddr32(new_globals5, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES, new_vals[5]);
            var new_globals7 := global_write_at_vaddr32(new_globals6, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES, new_vals[6]);
            var new_globals8 := global_write_at_vaddr32(new_globals7, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES, new_vals[7]);
            var new_globals9 := global_write_at_vaddr32(new_globals8, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES, new_vals[8]);
            var new_globals10 := global_write_at_vaddr32(new_globals9, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES, new_vals[9]);

            var new_globals11 := global_write_at_vaddr32(new_globals10, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES, new_vals[10]);
            var new_globals12 := global_write_at_vaddr32(new_globals11, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES, new_vals[11]);
            var new_globals13 := global_write_at_vaddr32(new_globals12, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES, new_vals[12]);
            var new_globals14 := global_write_at_vaddr32(new_globals13, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES, new_vals[13]);
            var new_globals15 := global_write_at_vaddr32(new_globals14, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES, new_vals[14]);

            var new_globals16 := global_write_at_vaddr32(new_globals15, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES, new_vals[15]);
            var new_globals17 := global_write_at_vaddr32(new_globals16, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES, new_vals[16]);
            var new_globals18 := global_write_at_vaddr32(new_globals17, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES, new_vals[17]);
            var new_globals19 := global_write_at_vaddr32(new_globals18, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES, new_vals[18]);
            var new_globals20 := global_write_at_vaddr32(new_globals19, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES, new_vals[19]);

            var new_globals21 := global_write_at_vaddr32(new_globals20, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES, new_vals[20]);
            var new_globals22 := global_write_at_vaddr32(new_globals21, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES, new_vals[21]);
            var new_globals23 := global_write_at_vaddr32(new_globals22, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES, new_vals[22]);

            new_globals == new_globals23
        )
}

// Property: <usbtd_backup> copies the USB TD from wimp driver to the given <slot> of <g_usbtd_mem_map>
predicate ffi_usbtd_backup_stack_and_globals(old_wkm:WK_MState, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Backup_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot)
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var td_slot:word := stack_get_val(old_stack, old_esp);

    ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)
}

predicate {:opaque} ffi_usbtd_backup_stack_and_globals_inner(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot);
{
    lemma_DistinctGlobals();
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

    // Content
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(td_slot);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 1 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 2 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 3 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 4 * UINT32_BYTES) &&

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 5 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 6 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 7 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 8 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 9 * UINT32_BYTES) &&

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 10 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 11 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 12 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 13 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 14 * UINT32_BYTES) &&

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 15 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 16 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 17 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 18 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 19 * UINT32_BYTES) &&

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 20 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 21 * UINT32_BYTES) &&
        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr + 22 * UINT32_BYTES)
    ) &&

    // ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_ID_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // PID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_PID_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Type
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Bus ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // WimpDrv Slot ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // USBPDev Slot ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Flags
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Handle
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Input Param 1
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Input Param 2
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Input Param 3
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

        global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Other global variables are unchanged
    globals_other_gvar_unchanged(old_globals, new_globals, G_Temp_USBTD())
}

// Property: <usbtd_restore> copies the USB TD from wimp driver to the given <slot> of <g_usbtd_mem_map>
predicate ffi_usbtd_restore_stack_and_globals(old_wkm:WK_MState, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot)
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var td_slot:word := stack_get_val(old_stack, old_esp);

    ffi_usbtd_restore_stack_and_globals_inner(old_globals, new_globals, td_slot)
}

// [NOTE] Needs 80s to verify
predicate {:opaque} ffi_usbtd_restore_stack_and_globals_inner(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot);
{
    lemma_DistinctGlobals();
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

    // Content
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(td_slot);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 1 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 2 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 3 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 6 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 7 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 8 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 9 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 10 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 11 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 12 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 13 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 14 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 15 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 16 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 17 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 18 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 19 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 20 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 21 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 1 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 2 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 3 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 4 * UINT32_BYTES) &&

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 5 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 6 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 7 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 8 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 9 * UINT32_BYTES) &&

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 10 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 11 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 12 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 13 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 14 * UINT32_BYTES) &&

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 15 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 16 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 17 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 18 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 19 * UINT32_BYTES) &&

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 20 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 21 * UINT32_BYTES) &&
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr + 22 * UINT32_BYTES)
    ) &&

    // ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // PID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Type
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Bus ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // WimpDrv Slot ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // USBPDev Slot ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Flags
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Handle
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Input Param 1
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Input Param 2
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // Input Param 3
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_Temp_USBTD(), temp_td_addr)
    ) &&

    // In <g_usbtd_map_mem>, other USB TDs and global variables are unmodified 
    usbtd_map_modify_one_usbtd_only(old_globals, new_globals, td_slot)
}

// Property: Correctness properties of the return values of <usbtd_is_ref_target_usbtd> 
predicate {:opaque} p_ffi_usbtd_is_ref_target_usbtd_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_IsRefTargetUSBTD_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_slot> must be stored in <g_usbtd_map_mem>
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var ret:word := stack_get_val(new_stack, old_esp);

    var refed_td_slot := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    var td_slot := stack_get_val(old_stack, old_esp);

    (ret == TRUE) <==> usbtd_is_slot_ref_target_slot(old_globals, td_slot, refed_td_slot)
}

// Predicate: Is the given USB TD <td_slot> reference the target USB TD <target_td_slot>
predicate usbtd_is_slot_ref_target_slot(globals:globalsmap, td_slot:uint32, target_td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)

    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_type := usbtd_map_get_type(globals, td_slot);

    (td_type == USBTDs_TYPE_QTD32 ==>
        (
            var result := usbtd_qtd32_parse_TDPtrs_from_global(globals, td_slot);
            var td_next_qtd_slot:uint32 := result.0;
            var td_alt_next_qtd_slot:uint32 := result.1;
            var next_qtd_p_Tflag:uint32 := result.2;
            var alt_next_qtd_p_Tflag:uint32 := result.3;

            (next_qtd_p_Tflag != 1 &&  td_next_qtd_slot == target_td_slot) ||
            (alt_next_qtd_p_Tflag != 1 &&  td_alt_next_qtd_slot == target_td_slot)
        )
    ) &&

    (td_type == USBTDs_TYPE_QH32 ==>
        (
            var result := usbtd_qh32_parse_TDPtrs_from_global(globals, td_slot);
            var next_qh_slot:uint32 := result.0;
            var next_qtd_slot:uint32 := result.1; 
            var alt_next_qtd_slot:uint32 := result.2;
            var next_qh_p_Tflag:uint32 := result.3;
            var next_qtd_p_Tflag:uint32 := result.4;
            var alt_next_qtd_p_Tflag:uint32 := result.5;

            (next_qh_p_Tflag != 1 &&  next_qh_slot == target_td_slot) ||
            (next_qtd_p_Tflag != 1 &&  next_qtd_slot == target_td_slot) ||
            (alt_next_qtd_p_Tflag != 1 &&  alt_next_qtd_slot == target_td_slot)
        )
    ) &&

    // [TODO] Not support iTD and siTD yet
    (td_type != USBTDs_TYPE_iTD32) &&
    (td_type != USBTDs_TYPE_siTD32)
}

// Property: <usbtd_clear_content> clear the content of any types of USB TDs
predicate ffi_usbtd_clear_content_stack_and_globals(old_wkm:WK_MState, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
            ins_valid_usbtd_clear_content(wkm_stack_get_all(old_wkm), wkm_get_globals(old_wkm), old_esp)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot)
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);

    var td_slot:word := stack_get_val(old_stack, old_esp);
    var td_type := stack_get_val(old_stack, old_esp + ARCH_WORD_BYTES);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

    usbtd_has_clear_content(new_globals, td_slot, td_type) &&

    // ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
        
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // PID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
        
        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Type
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Bus ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // WimpDrv Slot ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // USBPDev Slot ID
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Flags
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Handle
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
        var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Input Param 1
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Input Param 2
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // Input Param 3
    (
        var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;

        global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr)
    ) &&

    // In <g_usbtd_map_mem>, other USB TDs and global variables are unmodified 
    usbtd_map_modify_one_usbtd_only(old_globals, new_globals, td_slot)
}




/*********************** Utility Functions ********************/
function usbtd_qtd32_parse_TDPtrs_from_global(globals:globalsmap, td_slot:uint32) : (paddr, paddr, uint32, uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 1 * UINT32_BYTES);
    // According to EHCI specification, Section 3.5. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

    (next_qtd_slot, alt_next_qtd_slot, next_qtd_p_Tflag, alt_next_qtd_p_Tflag)
}

function usbtd_qtd32_parse_DataBufPtrs_from_global(globals:globalsmap, td_slot:uint32) : (paddr, paddr, paddr, paddr, paddr)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 7 * UINT32_BYTES);
    // According to EHCI specification, Section 3.5
    var r_buf0_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 3 * UINT32_BYTES), 0xFFFFF000); 
    var r_buf1_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0xFFFFF000);
    var r_buf2_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0xFFFFF000);
    var r_buf3_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 6 * UINT32_BYTES), 0xFFFFF000);
    var r_buf4_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 7 * UINT32_BYTES), 0xFFFFF000);

    (r_buf0_p, r_buf1_p, r_buf2_p, r_buf3_p, r_buf4_p)
}

function usbtd_qh32_parse_TDPtrs_from_global(globals:globalsmap, td_slot:uint32) : (paddr, paddr, paddr, uint32, uint32, uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6
    var next_qh_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qh_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

    (next_qh_slot, next_qtd_slot, alt_next_qtd_slot, next_qh_p_Tflag, next_qtd_p_Tflag, alt_next_qtd_p_Tflag)
}

function usbtd_qh32_parse_DataBufPtrs_from_global(globals:globalsmap, td_slot:uint32) : (paddr, paddr, paddr, paddr, paddr)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 11 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6
    var r_buf0_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 7 * UINT32_BYTES), 0xFFFFF000); 
    var r_buf1_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 8 * UINT32_BYTES), 0xFFFFF000);
    var r_buf2_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 9 * UINT32_BYTES), 0xFFFFF000);
    var r_buf3_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 10 * UINT32_BYTES), 0xFFFFF000);
    var r_buf4_p:paddr := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 11 * UINT32_BYTES), 0xFFFFF000);

    (r_buf0_p, r_buf1_p, r_buf2_p, r_buf3_p, r_buf4_p)
}

// Predicate: The value in the global variable must be a valid USBPDev ID
predicate usbtd_qh32_can_parse_TargetUSBDevID_from_global(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    var td_addr:addr := usbtd_map_get_tdaddr(globals, slot);
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(slot);
    lemma_DistinctGlobals();
    
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, 1 * UINT32_BYTES);
    var uint32_1 := global_read_uint32(globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES);
    var hub_port := BitwiseAnd(RightShift(uint32_1, QH32_HUB_PORT_SHIFT_BITS), HUB_PORT_MASK);
    var hub_addr := BitwiseAnd(RightShift(uint32_1, QH32_HUB_ADDR_SHIFT_BITS), USB_ADDR_MASK);
    var dev_addr := BitwiseAnd(uint32_1, USB_ADDR_MASK);

    usb_is_hub_port_valid(hub_port) &&
    usb_is_dev_addr_valid(hub_addr) &&
    usb_is_dev_addr_valid(dev_addr)
}

function usbtd_qh32_parse_TargetUSBPDevAddr_from_global(globals:globalsmap, slot:uint32) : USBPDev_Addr
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
    requires usbtd_slot_valid_busid(globals, slot)

    requires usbtd_qh32_can_parse_TargetUSBDevID_from_global(globals, slot)
{
    reveal usb_is_dev_addr_valid();
    reveal usb_is_hub_port_valid();

    var bus_no:uint16 := usbtd_map_get_busid(globals, slot);
    var td_addr:addr := usbtd_map_get_tdaddr(globals, slot);
    
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, 1 * UINT32_BYTES);
    var uint32_1 := global_read_uint32(globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES);
    var hub_port := BitwiseAnd(RightShift(uint32_1, QH32_HUB_PORT_SHIFT_BITS), HUB_PORT_MASK);
    var hub_addr := BitwiseAnd(RightShift(uint32_1, QH32_HUB_ADDR_SHIFT_BITS), USB_ADDR_MASK);
    var dev_addr := BitwiseAnd(uint32_1, USB_ADDR_MASK);
    

    USBPDev_Addr(
        USBPDevAddr_Reserved1_Val,                          // reserved1
        bus_no,                                             // bus_no
        USBPDevAddr_Reserved2_Val,                          // reserved2
        hub_addr,                                           // hub_addr
        hub_port,                                           // hub_port
        dev_addr                                            // dev_addr
    )
}