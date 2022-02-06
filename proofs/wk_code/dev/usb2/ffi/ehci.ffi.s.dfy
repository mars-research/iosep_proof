include "../../../ins/util/ffi.s.dfy"
include "../../../state_properties_validity.s.dfy"

/*********************** Outputs of external functions ********************/
const FFI_EEHCI_FindRefToUSBTD_ReturnWords:int := 1;
const FFI_EEHCI_Activate_ReturnWords:int := 4;
const FFI_EEHCI_Deactivate_ReturnWords:int := 0;
const FFI_PEHCI_ActivateInOS_ReturnWords:int := 0;

const FFI_EEHCI_Activate_StackParamsWords:int := FFI_EEHCI_Activate_ReturnWords;
const FFI_EEHCI_Deactivate_StackParamsWords:int := 1;
const FFI_EEHCI_FindRefToUSBTD_StackParamsWords:int := FFI_EEHCI_FindRefToUSBTD_ReturnWords;
const FFI_PEHCI_ActivateInOS_StackParamsWords:int := 0;

// [EHCI] FFI (external component): EEHCI_Activate
// This function modifies both stack and global on return, but nothing else
// Input params on stack: None
// Return on stack: (new_handle:word) at esp + 3 * ARCH_WORD_BYTES, (new_eehci_slot:uint32) at esp + 2 * ARCH_WORD_BYTES,  
// (eehci_id:uint32) at esp + ARCH_WORD_BYTES, (ret:uint32) at esp
function {:axiom} ffi_eehci_activate(s:state) : (result:(wk_memmap, globalsmap, map<x86Reg, word>))
    requires ValidState(s)
    requires var old_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(old_wkm, ESP);
             IsAddrInStack(old_esp + FFI_EEHCI_Activate_ReturnWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    ensures var old_wkm := s.wk_mstate;
            ffi_preserve_sp_and_bp(old_wkm, result.2)
    ensures var old_wkm := s.wk_mstate;
            ffi_preserve_old_stack(old_wkm, result.0, FFI_EEHCI_Activate_ReturnWords) // Return parameters take 3 words 
    ensures WK_ValidGlobalVars_Decls(result.1)
    ensures var old_wkm := s.wk_mstate;
            ffi_eehci_activate_stack_and_globals(old_wkm, result.0, result.1)
    ensures ffi_eehci_activate_stack_and_globals2(s, result.0, result.1)
                // Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot 
                // and eehci_id correctly

// [EHCI] FFI (external component): EEHCI_Deactivate
// This function modifies both stack and global on return, but nothing else
// Input params on stack: (slot:word) at esp
// Return on stack: None
function {:axiom} ffi_eehci_deactivate(old_wkm:WK_MState) : (result:(wk_memmap, globalsmap, map<x86Reg, word>))
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
            ins_valid_eehci_deactivate(old_wkm, old_esp)
    ensures ffi_preserve_sp_and_bp(old_wkm, result.2)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_EEHCI_Deactivate_ReturnWords) // Return parameters take 0 word 
    ensures WK_ValidGlobalVars_Decls(result.1)
    ensures ffi_eehci_deactivate_stack_and_globals(old_wkm, result.0, result.1)
                // Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot 
                // and eehci_id correctly

predicate ins_valid_eehci_deactivate(s:WK_MState, old_esp:vaddr)
    requires WK_ValidMState(s)
    requires WK_Mem_Separate_Segs()

    requires var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
            is_valid_addr(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp + stack_params_space - ARCH_WORD_BYTES) &&
            is_vaddr_in_stack(old_esp)
{
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var eehci_slot := stack_get_val(old_stack, old_esp);

    eehci_valid_slot_id(eehci_slot) &&
    eehci_info_get_pid(old_globals, eehci_slot) == WS_PartitionID(PID_INVALID) &&
    EECHI_DoNotRefAnyUSBTD(old_globals, eehci_slot)
}

// [To-implement] FFI
// Desired properties of the external function "eehci_find_ref_to_usbtd", which is expected to append values to the 
// stack and write return values on the stack, and modify registers
// Input params on stack: (usbtd_slot_id:word) at esp
// Return params on stack: (eehci_slot_id:word) at esp
function {:axiom} ffi_eehci_find_ref_to_usbtd(old_wkm:WK_MState) : (result:(wk_memmap, map<x86Reg, word>)) 
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_FindRefToUSBTD_StackParamsWords * ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB TD referred by <td_addr> must be stored in <g_usbtd_map_mem>

    ensures ffi_preserve_sp_and_bp(old_wkm, result.1)
    ensures ffi_preserve_old_stack(old_wkm, result.0, FFI_EEHCI_FindRefToUSBTD_ReturnWords) // Words for return parameters 

    ensures p_ffi_eehci_find_ref_to_usbtd_retval(old_wkm, result.0)

predicate ins_valid_pEHCI_ActivateInOS(s:state, old_esp:vaddr)
    requires ValidState(s)
    requires WK_Mem_Separate_Segs()
{
    var globals := wkm_get_globals(s.wk_mstate);

    // No eEHCI is active
    (forall i :: eehci_valid_slot_id(i)
        ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID))
}

// [EHCI] FFI (external component): PEHCI_ActivateInOS
// This function modifies stacks, globals, subjects and objects.
// Input params on stack: None
// Return on stack: None
// [NOTE] This function must be an FFI, because specific physical EHCIs clear objects in different ways; e.g.,  
// additional registers. And WK calls micro-hypervisor (mhv) to move physical EHCIs between I/O partitions.
// [NOTE] It should be noted that all USB hubs connected to physical EHCIs are considered to be part of physical EHCIs.
// In other words, these USB hubs must be also properly cleaned and activated in OS
function {:axiom} ffi_pEHCI_ActivateInOS(s:state) : (result:(wk_memmap, map<x86Reg, word>, WSM_Subjects, WSM_Objects))
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pEHCI_ActivateInOS(s, old_esp)
    ensures ffi_preserve_sp_and_bp(s.wk_mstate, result.1)
    ensures ffi_preserve_old_stack(s.wk_mstate, result.0, FFI_PEHCI_ActivateInOS_ReturnWords) // Return parameters take 0 word
    ensures ffi_pehci_activate_in_os_stack_and_statevars(s, result.2, result.3)
                // Property: <PEHCI_ActivateInOS> activates all physical EHCIs back to the OS partition




/*********************** Predicates of external functions ********************/
// Property: <eehci_activate> allocates a slot in the global variable <g_eehci_mem> and return the slot and eehci_id
// correctly  
predicate {:opaque} ffi_eehci_activate_stack_and_globals(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES - ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Activate_ReturnWords) // Return parameters take 3 words 
    requires WK_ValidGlobalVars_Decls(new_globals)
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);
    var old_globals := wkm_get_globals(old_wkm);

    ((ret == TRUE) ==> eehci_valid_slot_id(new_eehci_slot)) &&
        // If return true, then the <eehci_id> does not appear in the old <g_eehci_mem>
    ((ret == TRUE) ==> new_eehci_id != eEHCI_ID_INVALID) &&
    ((ret == TRUE) ==> (forall i:word :: eehci_valid_slot_id(i)
                        ==> eehci_mem_get_eehci_id(old_globals, i) != new_eehci_id)
    ) &&
    ffi_eehci_activate_globals_relationship(old_globals, new_globals, new_eehci_slot, new_eehci_id, new_handle, ret)
}

predicate ffi_eehci_activate_stack_and_globals2(s:state, new_stack:wk_memmap, new_globals:globalsmap)
    requires ValidState(s)
    requires var old_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(old_wkm, ESP);
             IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES - ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_wkm := s.wk_mstate; 
             ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Activate_ReturnWords) // Return parameters take 3 words 
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_wkm := s.wk_mstate;
             ffi_eehci_activate_stack_and_globals(old_wkm, new_stack, new_globals)
{
    reveal ffi_preserve_old_stack();
    reveal ffi_eehci_activate_stack_and_globals();
    var old_wkm := s.wk_mstate;

    var old_esp := x86_get_reg(old_wkm, ESP);
    var new_eehci_idword:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);

    (ret == TRUE) ==> (
        var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, new_eehci_idword);
        eehci_id in s.subjects.eehcis
    )
}

predicate ffi_eehci_activate_globals_relationship(old_globals:globalsmap, new_globals:globalsmap, new_eehci_slot:word, new_eehci_id:word, new_handle:word, ret:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires ret == TRUE ==> eehci_valid_slot_id(new_eehci_slot)
    requires var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
             ret == TRUE ==> is_gvar_valid_addr(G_EEHCI_MEM(), vaddr1)
{
    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;

    ((ret == TRUE) ==> (
        var new_globals1 := global_write_word(old_globals, G_EEHCI_MEM(), vaddr1, new_eehci_id);
        eehci_mem_get_eehci_id(old_globals, new_eehci_slot) == eEHCI_ID_INVALID &&
            // Property: <new_eehci_id> is put at the beginning of a slot. 
            // In other words, a slot in <g_eehci_mem> is newly allocated for the eEHCI <new_eehci_id>
        var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), vaddr2, new_handle);
        eehci_mem_cleared_all_regs(new_globals2, new_globals, new_eehci_slot)
            // Property: Only <eehci_id> and <USBTD_regs> fields of the given eEHCI slot is modified
        )) &&
    ((ret != TRUE) ==> new_globals == old_globals)
}

// Property: <eehci_deactivate> allocates a slot in the global variable <g_eehci_mem> and return the slot and eehci_id
// correctly  
predicate {:opaque} ffi_eehci_deactivate_stack_and_globals(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
             ins_valid_eehci_deactivate(old_wkm, old_esp)

    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Deactivate_ReturnWords) // Return parameters take 1 word 
    requires WK_ValidGlobalVars_Decls(new_globals)
{
    reveal ffi_preserve_old_stack();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var in_slot:word := stack_get_val(old_stack, old_esp);
    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + in_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var old_globals := wkm_get_globals(old_wkm);

    ffi_eehci_deactivate_globals_relationship(old_globals, new_globals, in_slot)
}

predicate ffi_eehci_deactivate_globals_relationship(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires eehci_valid_slot_id(eehci_slot)
    requires var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
             is_gvar_valid_addr(G_EEHCI_MEM(), vaddr1)
{
    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;

    new_globals == global_write_word(old_globals, G_EEHCI_MEM(), vaddr1, eEHCI_ID_INVALID)
}

// Property: Correctness properties of the return values of <eehci_find_ref_to_usbtd> 
predicate {:opaque} p_ffi_eehci_find_ref_to_usbtd_retval(old_wkm:WK_MState, new_stack:wk_memmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_EEHCI_FindRefToUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_FindRefToUSBTD_ReturnWords) // Words for return parameters
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

    var td_slot := stack_get_val(old_stack, old_esp);
    var out_eehci_slot:word := stack_get_val(new_stack, old_esp);

    ((out_eehci_slot == eEHCI_SlotID_EMPTY) 
        ==> (forall i :: eehci_valid_slot_id(i) && eehci_is_active_wimp_eehci(old_globals, i)
                ==> EECHI_DoNotRefGivenUSBTD(old_globals, i, td_slot))
        // Property: If return eEHCI_SlotID_EMPTY, then all active eEHCIs do not ref the given USB TD
    ) &&
    
    ((out_eehci_slot != eEHCI_SlotID_EMPTY) 
        ==> (eehci_valid_slot_id(out_eehci_slot) && eehci_is_active_wimp_eehci(old_globals, out_eehci_slot) && 
             EEHCI_ExistEEHCI_RefGivenUSBTD(old_globals, out_eehci_slot, td_slot))
    )
}

// Property: <PEHCI_ActivateInOS> activates all physical EHCIs back to the OS partition
predicate {:opaque} ffi_pehci_activate_in_os_stack_and_statevars(
    s:state, new_subjects:WSM_Subjects, new_objects:WSM_Objects
)
    requires ValidState(s)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pEHCI_ActivateInOS(s, old_esp)
{
    reveal ffi_preserve_old_stack();
    reveal WK_ValidObjsAddrs();
    reveal WK_ValidState_DevsActivateCond();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var pehci_hcoded_td_ids := WSM_HCodedTDsOwnedByOSDevs(s, pehci_ids);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);
    var to_clear_objs := pehci_td_ids - pehci_hcoded_td_ids;

    // Prove objects are in s.objects
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    assert forall id:: id in pehci_hcoded_td_ids ==> id in s.objects.os_tds;
    assert forall id:: id in pehci_td_ids ==> id in s.objects.os_tds;
    assert forall id:: id in pehci_fd_ids ==> id in s.objects.os_fds;
    assert forall id:: id in pehci_do_ids ==> id in s.objects.os_dos;

    (
        var os_devs' := WSM_OSSetDevsPIDs(s.subjects.os_devs, pehci_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));

        new_subjects == s.subjects.(os_devs := os_devs')
    ) &&
        // Property 1: pEHCIs are activated correctly
    (
        // Clear the objects being activated (i.e., ClearObjs)
        var temp_tds := WSM_ClearOSTDs(s.objects.os_tds, to_clear_objs);
        var temp_fds := WSM_ClearOSFDs(s.objects.os_fds, pehci_fd_ids);
        var temp_dos := WSM_ClearOSDOs(s.objects.os_dos, pehci_do_ids);

        // Modify the PID of these objects (i.e., SetPbjsPIDs)
        var os_tds' := WSM_SetOSTDsPIDs(temp_tds, pehci_td_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));
        var os_fds' := WSM_SetOSFDsPIDs(temp_fds, pehci_fd_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));
        var os_dos' := WSM_SetOSDOsPIDs(temp_dos, pehci_do_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));

        new_objects == s.objects.(os_tds := os_tds', os_fds := os_fds', os_dos := os_dos')
    ) &&
        // Property 2: OS's objects are cleared and activated correctly

    (true)
}