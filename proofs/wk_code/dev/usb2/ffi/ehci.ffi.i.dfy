include "ehci.ffi.s.dfy"
include "../eehci_info.i.dfy"
include "../eehci_mem.i.dfy"
include "../usb_tds.i.dfy"
include "../usb_pdev.i.dfy"
include "../../../state_properties_validity.i.dfy"
include "../../../state_properties_OpsSaneStateSubset.i.dfy"
include "../usb_tds_ops/usb_tds_checks.i.dfy"
include "../../../ins/util/ffi.i.dfy"
include "../../../drv/public/wimpdrv_lemmas.i.dfy"
include "../../../mhv/mhv.ffi.i.dfy"

// Lemma: CALL_EEHCI_Activate ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_eehci_activate_ResultStateIsValidMState(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s, new_stack, new_globals)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    // Prove WK_ValidPartitionIDs_InGlobalVars(r)
    Lemma_ffi_eehci_activate_globals_only_g_eechi_mem_changed(s, new_stack, new_globals);

    assert gvar_read_fullval(s, G_Existing_PIDs()) == gvar_read_fullval(r, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));


    var old_esp := x86_get_reg(s, ESP);
    var old_globals := wkm_get_globals(s);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);
    var eehci_id_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var eehci_handle_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;

    if(ret == TRUE)
    {
        Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfEEHCIActivate(
            wkm_get_globals(s), wkm_get_globals(r), new_eehci_slot, eehci_id_vaddr, new_eehci_id, eehci_handle_vaddr, new_handle);
    }
}

// Lemma: CALL_EEHCI_Activate ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_eehci_activate_ResultStateIsValidState(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_ffi_eehci_activate_PreserveSubjPIDs(s, r, new_regs, new_stack, new_globals);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s,r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s,r);

    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

// Lemma: CALL_EEHCI_Activate ends up at a result state fulfilling WK_ValidMState and WK_EEHCI_Mem_SecureGlobalVarValues
lemma Lemma_ffi_eehci_activate_ResultStateIsValidMState_AndSecureEEHCIMemState(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires WK_SecureMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s, new_stack, new_globals)

    ensures WK_ValidMState(r)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    // Prove WK_ValidPartitionIDs_InGlobalVars(r)
    Lemma_ffi_eehci_activate_globals_only_g_eechi_mem_changed(s, new_stack, new_globals);

    assert gvar_read_fullval(s, G_Existing_PIDs()) == gvar_read_fullval(r, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));


    var old_esp := x86_get_reg(s, ESP);
    var old_globals := wkm_get_globals(s);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);
    var eehci_id_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var eehci_handle_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;

    if(ret == TRUE)
    {
        Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfEEHCIActivate(
            wkm_get_globals(s), wkm_get_globals(r), new_eehci_slot, eehci_id_vaddr, new_eehci_id, eehci_handle_vaddr, new_handle);
    }
}

// Lemma: CALL_EEHCI_Activate ends up at a result state fulfilling WK_SecureObjsAddrs_MemSeparation
lemma Lemma_ffi_eehci_activate_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s.wk_mstate)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))

    requires WK_ValidGlobalState(wkm_get_globals(r.wk_mstate))
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))

    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures WK_SecureObjsAddrs_MemSeparation(r.subjects, r.objects, r.id_mappings, r.objs_addrs, new_globals)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s, r);
}

// Lemma: CALL_EEHCI_Deactivate ends up at a result state fulfilling WK_SecureObjsAddrs_MemSeparation
lemma Lemma_ffi_eehci_deactivate_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s.wk_mstate)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))

    requires WK_ValidGlobalState(wkm_get_globals(r.wk_mstate))
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))

    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP); 
             ins_valid_eehci_deactivate(s.wk_mstate, old_esp)
             
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Deactivate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_deactivate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures WK_SecureObjsAddrs_MemSeparation(r.subjects, r.objects, r.id_mappings, r.objs_addrs, new_globals)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_deactivate_stack_and_globals();

    Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s, r);
}

// Lemma: CALL_EEHCI_Deactivate ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_eehci_deactivate_ResultStateIsValidMState(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s, ESP); 
             ins_valid_eehci_deactivate(s, old_esp)

    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_Deactivate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_deactivate_stack_and_globals(s, new_stack, new_globals)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_deactivate_stack_and_globals();

    // Prove WK_ValidPartitionIDs_InGlobalVars(r)
    Lemma_ffi_eehci_deactivate_globals_only_g_eechi_mem_changed(s, new_stack, new_globals);

    assert gvar_read_fullval(s, G_Existing_PIDs()) == gvar_read_fullval(r, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);
    var in_slot:word := stack_get_val(old_stack, old_esp);
    var eehci_id_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + in_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;

    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfEEHCIDeactivate(wkm_get_globals(s), wkm_get_globals(r), in_slot, eehci_id_vaddr);
}

// Lemma: CALL_EEHCI_Deactivate ends up at a result state fulfilling ValidState
lemma Lemma_ffi_eehci_deactivate_ResultStateIsValidState(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP); 
             ins_valid_eehci_deactivate(s.wk_mstate, old_esp)

    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Deactivate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_deactivate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_deactivate_stack_and_globals();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_ffi_eehci_deactivate_PreserveSubjPIDs(s, r, new_regs, new_stack, new_globals);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);

    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s,r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s,r);

    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

// Lemma: CALL_EEHCI_Deactivate ends up at a result state fulfilling WK_ValidMState and WK_EEHCI_Mem_SecureGlobalVarValues
lemma Lemma_ffi_eehci_deactivate_ResultStateIsValidMState_AndSecureEEHCIMemState(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires WK_SecureMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s, ESP); 
             ins_valid_eehci_deactivate(s, old_esp)

    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_Deactivate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_deactivate_stack_and_globals(s, new_stack, new_globals)

    ensures WK_ValidMState(r)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_deactivate_stack_and_globals();

    // Prove WK_ValidPartitionIDs_InGlobalVars(r)
    Lemma_ffi_eehci_deactivate_globals_only_g_eechi_mem_changed(s, new_stack, new_globals);

    assert gvar_read_fullval(s, G_Existing_PIDs()) == gvar_read_fullval(r, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);
    var in_slot:word := stack_get_val(old_stack, old_esp);
    var eehci_id_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + in_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfEEHCIDeactivate(wkm_get_globals(s), wkm_get_globals(r), in_slot, eehci_id_vaddr);
}

// Lemma: When activating an eEHCI, the result global variable must satisfy WK_USBTD_Map_SecureGlobalVarValues
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfEEHCIActivate(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires WK_SecureMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s, new_stack, new_globals)
        // Requirement: <ffi_eehci_deactivate> transits states correctly

    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s))

    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    reveal ffi_eehci_activate_stack_and_globals();
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    reveal eehci_mem_cleared_all_regs();

    var old_globals := wkm_get_globals(s);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(old_globals, new_globals);
}

// Lemma: When deactivating an eEHCI, the result global variable must satisfy WK_USBTD_Map_SecureGlobalVarValues
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfEEHCIDeactivate(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s, ESP); 
             ins_valid_eehci_deactivate(s, old_esp)

    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_Deactivate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires ffi_eehci_deactivate_stack_and_globals(s, new_stack, new_globals)
        // Requirement: <ffi_eehci_deactivate> transits states correctly

    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s))

    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    reveal ffi_eehci_deactivate_stack_and_globals();
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    var old_globals := wkm_get_globals(s);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(old_globals, new_globals);
}

// Lemma: CALL_EEHCI_FIND_RefToUSBTD ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_eehci_find_ref_to_usbtd_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_EEHCI_FindRefToUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_EEHCI_FindRefToUSBTD_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_EEHCI_FIND_RefToUSBTD ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_eehci_find_ref_to_usbtd_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_EEHCI_FindRefToUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_FindRefToUSBTD_ReturnWords)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
}

lemma Lemma_eehci_find_ref_to_usbtd_property(old_wkm:WK_MState, new_stack:wk_memmap)
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

    requires p_ffi_eehci_find_ref_to_usbtd_retval(old_wkm, new_stack)

    ensures x86wk_valid_memstate(new_stack)
    ensures var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var out_eehci_slot:word := stack_get_val(new_stack, old_esp);
            var old_globals := wkm_get_globals(old_wkm);
            var usbtd_slot := stack_get_val(old_stack, old_esp);
            (out_eehci_slot == eEHCI_SlotID_EMPTY)
                ==> (forall i :: eehci_valid_slot_id(i) ==> EECHI_DoNotRefGivenUSBTD(old_globals, i, usbtd_slot))
{
    reveal ffi_preserve_old_stack();
    reveal p_ffi_eehci_find_ref_to_usbtd_retval();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var old_stack := wkm_stack_get_all(old_wkm);
    var old_globals := wkm_get_globals(old_wkm);
    var out_eehci_slot:word := stack_get_val(new_stack, old_esp);
    var usbtd_slot := stack_get_val(old_stack, old_esp);

    if(out_eehci_slot == eEHCI_SlotID_EMPTY)
    {
        forall i | eehci_valid_slot_id(i)
            ensures EECHI_DoNotRefGivenUSBTD(old_globals, i, usbtd_slot)
        {
            // Dafny can automatically prove this statement
        }
    }
}

lemma Lemma_ffi_eehci_deactivate_globals_relationship_PreserveEECHI_DoNotRefAnyUSBTD(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires EECHI_DoNotRefAnyUSBTD(old_globals, eehci_slot)
    requires var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
             is_gvar_valid_addr(G_EEHCI_MEM(), vaddr1)
    requires ffi_eehci_deactivate_globals_relationship(old_globals, new_globals, eehci_slot)

    ensures EECHI_DoNotRefAnyUSBTD(new_globals, eehci_slot)
{
    forall usbtd_reg_id:int | (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
        ensures eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id) == USBTD_SlotID_INVALID
    {
        assert eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
    }
}

// Lemma: CALL_EEHCI_Activate preserves the WSM_SubjPID of all devices
lemma Lemma_ffi_eehci_activate_PreserveSubjPIDs(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures forall id :: WSM_IsSubjID(s.subjects, id)
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == 
                    WSM_SubjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    assert forall i :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == eehci_info_get_pid(globals', i);

    forall id | WSM_IsSubjID(s.subjects, id)
        ensures WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id)
    {
        if(Drv_ID(id) in subjs.os_drvs)
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (Dev_ID(id) in subjs.os_devs)
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (WSM_IsWimpDrvID(subjs, Drv_ID(id)))
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (WSM_IsUSBPDevID(subjs, Dev_ID(id)))
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else
        {
            assert WSM_IsEEHCIDevID(subjs, Dev_ID(id));

            Lemma_ffi_eehci_activate_PreserveSubjPIDsOfEEHCIs(s, r, new_regs, new_stack, new_globals);
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
    }
}

// Lemma: CALL_EEHCI_Deactivate preserves the WSM_SubjPID of all devices
lemma Lemma_ffi_eehci_deactivate_PreserveSubjPIDs(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP); 
             ins_valid_eehci_deactivate(s.wk_mstate, old_esp)

    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Deactivate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_deactivate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures forall id :: WSM_IsSubjID(s.subjects, id)
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == 
                    WSM_SubjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_deactivate_stack_and_globals();

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    assert forall i :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == eehci_info_get_pid(globals', i);

    forall id | WSM_IsSubjID(s.subjects, id)
        ensures WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id)
    {
        if(Drv_ID(id) in subjs.os_drvs)
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (Dev_ID(id) in subjs.os_devs)
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (WSM_IsWimpDrvID(subjs, Drv_ID(id)))
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (WSM_IsUSBPDevID(subjs, Dev_ID(id)))
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else
        {
            assert WSM_IsEEHCIDevID(subjs, Dev_ID(id));
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
    }
}

// Properties of <ffi_eehci_activate_globals_relationship> when eehci_activate returns true
lemma Lemma_ffi_eehci_activate_globals_relationship_Property(
    globals1:globalsmap, globals2:globalsmap, slot:word, new_eehci_id:word, new_handle:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)

    requires var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
             is_gvar_valid_addr(G_EEHCI_MEM(), vaddr1)

    requires ffi_eehci_activate_globals_relationship(globals1, globals2, slot, new_eehci_id, new_handle, TRUE);

    ensures eehci_mem_get_eehci_id(globals2, slot) == new_eehci_id
{
    reveal eehci_mem_cleared_all_regs();

    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;

    var new_globals1 := global_write_word(globals1, G_EEHCI_MEM(), vaddr1, new_eehci_id);
    var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), vaddr2, new_handle);
    assert eehci_mem_cleared_all_regs(new_globals2, globals2, slot);
    
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();
    reveal eechi_info_equal();
}

// Lemma: CALL_pEHCI_ActivateInOS ends up at a result state fulfilling ValidState
lemma Lemma_ffi_pEHCI_ActivateInOS_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pEHCI_ActivateInOS(s, old_esp)

    requires var result := ffi_pEHCI_ActivateInOS(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_subjs := result.2;
            var new_objs := result.3;
            r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack), subjects := new_subjs, objects := new_objs)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    var s_wkm := s.wk_mstate;
    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    // Prove validity of <wk_mstate>
    assert wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s.wk_mstate, r.wk_mstate);

    reveal ffi_pehci_activate_in_os_stack_and_statevars();

    Lemma_WK_ValidObjs_Properties(s.subjects, s.objects);
    Lemma_ffi_pehci_activate_in_os_stack_and_statevars_Properties(s, r.subjects, r.objects);
    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s, r);

    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsIDsAreUnchanged_IDMappings(s,r);

    assume WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate));
    //Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s,r);
    //Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_ValidObjAddrs_WimpDrv_DOPAddrs_OnOSSubjsObjsModification_IfIDsAreUnchanged(s,r);
    
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s, r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s, r);

    assume WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate));
    assume WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate));
    assert ValidState(r);
}

lemma Lemma_ffi_pehci_activate_in_os_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(
    s:state, r:state
)
    requires ValidState(s)

    requires WK_ValidGlobalState(wkm_get_globals(r.wk_mstate))
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))
    requires WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))
    requires WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))

    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    //requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP); 
             ins_valid_pEHCI_ActivateInOS(s, old_esp)

    requires ffi_pehci_activate_in_os_stack_and_statevars(s, r.subjects, r.objects)
    requires r.objs_addrs == s.objs_addrs
    requires r.id_mappings == s.id_mappings
    requires r.activate_conds == s.activate_conds
    requires wkm_get_globals(r.wk_mstate) == wkm_get_globals(s.wk_mstate)

    ensures WK_SecureObjsAddrs_MemSeparation(r.subjects, r.objects, r.id_mappings, r.objs_addrs, wkm_get_globals(r.wk_mstate))
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_pehci_activate_in_os_stack_and_statevars();

    reveal WK_ValidObjsAddrs_PEHCIs();
    reveal WK_SecureObjsAddrs_MemSeparation();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    // Prove Wimp drivers' DOs have unchanged PIDs, and WimpDrv DOs do not overlap with each other
    Lemma_ffi_pehci_activate_in_os_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation_InnerProveWimpDrvDOHaveUnchangedPIDAndValidMemRegion(s, r);

    // Prove pEHCI subject and object IDs are unchanged
    var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);

    Lemma_PEHCIsIDsObjIDsAreUnchanged(s, r);
    assert pehci_ids == WSM_AllDevIDs_pEHCIs(r.subjects, r.activate_conds);
    assert pehci_td_ids == WSM_TDsOwnedByOSDevs(r, pehci_ids);
    assert pehci_fd_ids == WSM_FDsOwnedByOSDevs(r, pehci_ids);
    assert pehci_do_ids == WSM_DOsOwnedByOSDevs(r, pehci_ids);

    Lemma_ffi_pehci_activate_in_os_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation_InnerProveOtherOSObjPIDsAreUnchanged(s, r);

    // Prove the property
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSTDID(objs, os_obj_id) == WSM_IsOSTDID(objs', os_obj_id);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);

        if(os_obj_id in pehci_td_ids)
        {
            reveal WK_ValidObjsAddrs_PEHCIs();
            assert WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate));
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
        else
        {
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
    }

    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSFDID(objs, os_obj_id) == WSM_IsOSFDID(objs', os_obj_id);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);

        if(os_obj_id in pehci_fd_ids)
        {
            reveal WK_ValidObjsAddrs_PEHCIs();
            assert WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate));
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
        else
        {
            reveal WK_SecureObjsAddrs_MemSeparation();
            assert WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate));
            assert objs_addrs'.fds_addrs[os_obj_id].paddrs == objs_addrs.fds_addrs[os_obj_id].paddrs;
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
    }

    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS DO
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSDOID(objs, os_obj_id) == WSM_IsOSDOID(objs', os_obj_id);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);

        if(os_obj_id in pehci_do_ids)
        {
            reveal WK_ValidObjsAddrs_PEHCIs();
            assert WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate));
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
        else
        {
            reveal WK_SecureObjsAddrs_MemSeparation();
            assert WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate));
            assert objs_addrs'.dos_addrs[os_obj_id].paddrs == objs_addrs.dos_addrs[os_obj_id].paddrs;
            assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);
        }
    }

    forall i, j | wimpdrv_valid_slot_id(i) && wimpdrv_valid_slot_id(j) &&
            i != j
        ensures WK_WimpDrv_DOMustNotOverlapWithEachOther(globals', i, j)
    {
        // Dafny can automatically prove it
    }

    Lemma_ProveWK_SecureObjsAddrs_MemSeparation(r);
}




/*********************** Private Lemmas ********************/
// CALL_EEHCI_Activate only changes g_eehci_mem among all global variables 
lemma Lemma_ffi_eehci_activate_globals_only_g_eechi_mem_changed(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES - ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Activate_ReturnWords) // Return parameters take 3 words 
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(old_wkm, new_stack, new_globals)

    ensures forall g :: g != G_EEHCI_MEM() && is_gvar_exist(g)
                ==> gvar_read_fullval(old_wkm, g) == global_read_fullval(new_globals, g)
{
    reveal ffi_eehci_activate_stack_and_globals();
    reveal eehci_mem_cleared_usbtd_regs();

    var old_globals := wkm_get_globals(old_wkm);
    var old_esp := x86_get_reg(old_wkm, ESP);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;
    var ret:word := stack_get_val(new_stack, old_esp);

    if(ret == TRUE)
    {
        reveal eehci_mem_cleared_all_regs();
        var new_globals1 := global_write_word(old_globals, G_EEHCI_MEM(), vaddr1, new_eehci_id);
        var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), vaddr2, new_handle); 
        assert eehci_mem_cleared_all_regs(new_globals2, new_globals, new_eehci_slot);
        assert new_globals == eehci_mem_clear_all_regs(new_globals2, new_eehci_slot);
        Lemma_eehci_mem_clear_all_regs_PreserveOtherGVars(new_globals2, new_globals, new_eehci_slot);
    }
    else
    {
        assert forall g :: g != G_EEHCI_MEM() && is_gvar_exist(g)
                ==> gvar_read_fullval(old_wkm, g) == global_read_fullval(new_globals, g);
    }
}

// CALL_EEHCI_Deactivate only changes g_eehci_mem among all global variables
lemma Lemma_ffi_eehci_deactivate_globals_only_g_eechi_mem_changed(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
             ins_valid_eehci_deactivate(old_wkm, old_esp)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Deactivate_ReturnWords) // Return parameters take 1 words 
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_deactivate_stack_and_globals(old_wkm, new_stack, new_globals)

    ensures forall g :: g != G_EEHCI_MEM() && is_gvar_exist(g)
                ==> gvar_read_fullval(old_wkm, g) == global_read_fullval(new_globals, g)
{
    reveal ffi_eehci_deactivate_stack_and_globals();
}

// Lemma: <ffi_eehci_activate_stack_and_globals> does not modify other eEHCI mem slots
lemma Lemma_ffi_eehci_activate_stack_and_globals_PreseveOtherEEHCIMemSlots(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Activate_ReturnWords) // Return parameters take 3 words 
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(old_wkm, new_stack, new_globals)

    requires x86wk_valid_memstate(new_stack)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var ret:word := stack_get_val(new_stack, old_esp);
            ret == TRUE

    requires var old_globals := wkm_get_globals(old_wkm);
            var old_esp := x86_get_reg(old_wkm, ESP);
            var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
            eehci_valid_slot_id(new_eehci_slot)

    ensures var old_globals := wkm_get_globals(old_wkm);
            var old_esp := x86_get_reg(old_wkm, ESP);
            var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
            forall i :: (eehci_valid_slot_id(i) && i != new_eehci_slot) ==> p_eehci_mem_equal(old_globals, new_globals, i)
{
    reveal ffi_eehci_activate_stack_and_globals();
    reveal eehci_mem_cleared_all_regs();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);
    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;
    var old_globals := wkm_get_globals(old_wkm);

    var new_globals1 := global_write_word(old_globals, G_EEHCI_MEM(), vaddr1, new_eehci_id);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(old_globals, new_globals1, new_eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset, new_eehci_id);
    assert forall i :: (eehci_valid_slot_id(i) && i != new_eehci_slot) ==> p_eehci_mem_equal(old_globals, new_globals1, i);

    var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), vaddr2, new_handle);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals1, new_globals2, new_eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset, new_handle);
    assert new_globals == eehci_mem_clear_all_regs(new_globals2, new_eehci_slot);
    Lemma_eehci_mem_clear_all_regs_PreserveOtherEEHCIMemSlots(new_globals2, new_globals, new_eehci_slot);

    forall i | (eehci_valid_slot_id(i) && i != new_eehci_slot) 
        ensures p_eehci_mem_equal(old_globals, new_globals, i)
    {
        Lemma_p_eehci_mem_slot_equal_transitive(new_globals1, new_globals2, new_globals, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals1, new_globals, i);
    }
}

// Lemma: <ffi_eehci_activate_stack_and_globals> has the new EEHCI ID word written in global variables
lemma Lemma_ffi_eehci_activate_stack_and_globals_ProveNewEEHCIIDWordIsWritten(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_EEHCI_Activate_ReturnWords) // Return parameters take 3 words 
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(old_wkm, new_stack, new_globals)

    requires x86wk_valid_memstate(new_stack)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var ret:word := stack_get_val(new_stack, old_esp);
            ret == TRUE

    requires var old_globals := wkm_get_globals(old_wkm);
            var old_esp := x86_get_reg(old_wkm, ESP);
            var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
            eehci_valid_slot_id(new_eehci_slot)

    ensures var old_globals := wkm_get_globals(old_wkm);
            var old_esp := x86_get_reg(old_wkm, ESP);
            var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
            var new_eehci_id_word:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
            new_eehci_id_word == eehci_mem_get_eehci_id(new_globals, new_eehci_slot);
{
    reveal ffi_eehci_activate_stack_and_globals();
    reveal eehci_mem_cleared_all_regs();

    var old_esp := x86_get_reg(old_wkm, ESP);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);
    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;
    var old_globals := wkm_get_globals(old_wkm);
}

// Lemma: CALL_EEHCI_Activate preserves the SubjPID_EEHCI_ByDevID of all eEHCIs
lemma Lemma_ffi_eehci_activate_PreserveSubjPIDsOfEEHCIs(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            IsAddrInStack(old_esp + FFI_EEHCI_Activate_StackParamsWords * ARCH_WORD_BYTES); 
            // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_EEHCI_Activate_ReturnWords)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_eehci_activate_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures forall id :: WSM_IsEEHCIDevID(s.subjects, id)
                ==> SubjPID_EEHCI_ByDevID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == 
                    SubjPID_EEHCI_ByDevID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_eehci_activate_stack_and_globals();

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();


    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    var old_esp := x86_get_reg(s.wk_mstate, ESP);
    var old_globals := wkm_get_globals(s.wk_mstate);
    var new_handle:word := stack_get_val(new_stack, old_esp + 3 * ARCH_WORD_BYTES);
    var new_eehci_slot:word := stack_get_val(new_stack, old_esp + 2 * ARCH_WORD_BYTES);
    var new_eehci_id_word:word := stack_get_val(new_stack, old_esp + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(new_stack, old_esp);
    var eehci_id_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var eehci_handle_vaddr := AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;

    if(ret == TRUE)
    {
        Lemma_ffi_eehci_activate_stack_and_globals_ProveNewEEHCIIDWordIsWritten(s.wk_mstate, new_stack, new_globals);
        var new_eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(subjs, objs, id_mappings, new_eehci_id_word);
        assert new_eehci_id == Map_EEHCIIDWord_ToDevID(subjs', objs', id_mappings', new_eehci_id_word);
        assert new_eehci_id_word == eehci_mem_get_eehci_id(new_globals, new_eehci_slot);

        assert forall i :: eehci_valid_slot_id(i)
                ==> eehci_info_get_pid(globals, i) == eehci_info_get_pid(globals', i);

        forall id | WSM_IsEEHCIDevID(s.subjects, id)
            ensures SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, id) == SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', id)
        {
            Lemma_ffi_eehci_activate_stack_and_globals_PreseveOtherEEHCIMemSlots(s.wk_mstate, new_stack, new_globals);
            reveal p_eehci_mem_equal();
                    
            if(id != new_eehci_id)
            {
                var id_word := EEHCI_DevID_ToIDWord(subjs, objs, id_mappings, id);
                if(eehci_idword_in_record(globals, id_word))
                {
                    var dev_slot := eehci_get_slot_by_idword(globals, id_word);

                    // Prove p_eehci_mem_equal(globals, globals', dev_slot)
                    assert dev_slot != new_eehci_slot;
                    assert p_eehci_mem_equal(globals, globals', dev_slot);
                    
                    // Prove dev_slot == eehci_get_slot_by_idword(globals', id_word)
                    assert dev_slot == eehci_get_slot_by_idword(globals', id_word);

                    assert SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, id) == eehci_info_get_pid(globals, dev_slot);
                    assert SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', id) == eehci_info_get_pid(globals', dev_slot);
                }
                else
                {
                    assert SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, id) == WS_PartitionID(PID_INVALID);

                    // Prove !eehci_idword_in_record(globals', id_word)
                    assert !eehci_idword_in_record(globals', id_word);
                    assert SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', id) == WS_PartitionID(PID_INVALID);
                }
                assert SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, id) == SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', id);
            }
            else
            {
                assert SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, id) == WS_PartitionID(PID_INVALID);

                assert eehci_info_get_pid(globals, new_eehci_slot) == WS_PartitionID(PID_INVALID);
                assert eehci_info_get_pid(globals', new_eehci_slot) == WS_PartitionID(PID_INVALID);
                assert SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', id) == WS_PartitionID(PID_INVALID);
            }
        }
    }
}

lemma Lemma_ffi_pehci_activate_in_os_stack_and_statevars_Properties(
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

    requires ffi_pehci_activate_in_os_stack_and_statevars(s, new_subjects, new_objects)

    ensures forall id :: id in s.subjects.os_devs
                ==> s.subjects.os_devs[id].hcoded_td_id in s.objects.os_tds
        // Properties needed by the following properties
    ensures MapGetKeys(s.subjects.os_devs) == MapGetKeys(new_subjects.os_devs)
    ensures MapGetKeys(s.objects.os_tds) == MapGetKeys(new_objects.os_tds)
    ensures forall id :: id in s.subjects.os_devs
                ==> (s.subjects.os_devs[id].hcoded_td_id == new_subjects.os_devs[id].hcoded_td_id &&
                     s.subjects.os_devs[id].td_ids == new_subjects.os_devs[id].td_ids &&
                     s.subjects.os_devs[id].fd_ids == new_subjects.os_devs[id].fd_ids &&
                     s.subjects.os_devs[id].do_ids == new_subjects.os_devs[id].do_ids)
    ensures forall id :: id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val == new_objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val
        // Property 1: HCoded TDs of OS devices are unchanged
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal ffi_pehci_activate_in_os_stack_and_statevars();

    var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var pehci_hcoded_td_ids := WSM_HCodedTDsOwnedByOSDevs(s, pehci_ids);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);
    var to_clear_objs := pehci_td_ids - pehci_hcoded_td_ids;

    assume forall id :: id in s.subjects.os_devs
                ==> s.subjects.os_devs[id].hcoded_td_id in s.objects.os_tds;

    assume forall id :: id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val == new_objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val;

    /*forall id | id in s.subjects.os_devs
        ensures s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val == new_objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val
    {
        var hcoded_td_id := s.subjects.os_devs[id].hcoded_td_id;
        assume hcoded_td_id in s.objects.os_tds;

        if(s.objects.os_tds[hcoded_td_id].val != new_objects.os_tds[hcoded_td_id].val)
        {
            assert hcoded_td_id in to_clear_objs;
            assert false;
        }
    } */

    //assert forall id :: id in to_clear_objs
    //        ==> id !in WSM_AllHCodedTDIDs_OSDevs(s.subjects);
}

lemma Lemma_ffi_pehci_activate_in_os_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation_InnerProveWimpDrvDOHaveUnchangedPIDAndValidMemRegion(
    s:state, r:state
)
    requires ValidState(s)

    requires WK_ValidGlobalState(wkm_get_globals(r.wk_mstate))
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))
    requires WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))
    requires WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))

    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP); 
             ins_valid_pEHCI_ActivateInOS(s, old_esp)

    requires ffi_pehci_activate_in_os_stack_and_statevars(s, r.subjects, r.objects)
    requires r.objs_addrs == s.objs_addrs
    requires r.id_mappings == s.id_mappings
    requires wkm_get_globals(r.wk_mstate) == wkm_get_globals(s.wk_mstate)

    //ensures WK_SecureObjsAddrs_MemSeparation(r.subjects, r.objects, r.id_mappings, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    ensures forall id :: WSM_IsWimpDrvDOID(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)
    ensures forall wimpdrv_do_id:DO_ID, pmem2 ::
                    WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) && WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) &&
                    pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                ==> pmem2.paddr_start <= pmem2.paddr_end
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_pehci_activate_in_os_stack_and_statevars();

    reveal WK_ValidObjsAddrs_PEHCIs();
    reveal WK_SecureObjsAddrs_MemSeparation();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    // Prove Wimp drivers' DOs have unchanged PIDs
    forall id | WSM_IsWimpDrvDOID(s.objects, id)
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();
        
        Lemma_WSM_IsWimpDrvDOID_Property(subjs, objs, id_mappings, id);
        Lemma_WSM_IsWimpDrvDOID_Property(subjs', objs', id_mappings', id);
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    ObjPID_WimpDrvObj(subjs, objs, id_mappings, globals, id.oid);
        assert WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid) ==
                    ObjPID_WimpDrvObj(subjs', objs', id_mappings', globals', id.oid);
        
        // Prove WimpDrvDO_FindOwner(subjs, objs, id.oid) == WimpDrvDO_FindOwner(subjs', objs', id.oid)
        var drv_id := WimpDrvDO_FindOwner(subjs, objs, id.oid);
        var drv_id' := WimpDrvDO_FindOwner(subjs', objs', id.oid);

        if(drv_id != drv_id')
        {
            assert id == subjs.wimp_drvs[drv_id].do_id;
            assert id == subjs'.wimp_drvs[drv_id'].do_id;

            assert subjs.wimp_drvs[drv_id].do_id == subjs.wimp_drvs[drv_id'].do_id;
            assert WSM_DoOwnObj(subjs, drv_id.sid, id.oid);
            assert WSM_DoOwnObj(subjs, drv_id'.sid, id.oid);

            assert (forall o_id, s_id1, s_id2 :: 
                        s_id1 in WSM_AllSubjsIDs(subjs) && s_id2 in WSM_AllSubjsIDs(subjs) && 
                        WSM_DoOwnObj(subjs, s_id1, o_id) && WSM_DoOwnObj(subjs, s_id2, o_id)
                        ==> s_id1 == s_id2);
            assert false;
        }
        assert drv_id == drv_id';
        
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, id.oid);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', drv_id.sid, id.oid);

        assert SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, drv_id) == SubjPID_WimpDrv_ByDrvID(subjs', objs', id_mappings', globals', drv_id);
    }

    forall wimpdrv_do_id:DO_ID, pmem2 | WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id) &&
            WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid) &&
            pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ensures pmem2.paddr_start <= pmem2.paddr_end
    {
        // Dafny can automatically prove it
    }
}

lemma Lemma_ffi_pehci_activate_in_os_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation_InnerProveOtherOSObjPIDsAreUnchanged(
    s:state, r:state
)
    requires ValidState(s)

    requires WK_ValidGlobalState(wkm_get_globals(r.wk_mstate))
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))
    requires WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))
    requires WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))

    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires var old_esp := x86_get_reg(s.wk_mstate, ESP); 
             ins_valid_pEHCI_ActivateInOS(s, old_esp)

    requires ffi_pehci_activate_in_os_stack_and_statevars(s, r.subjects, r.objects)
    requires r.objs_addrs == s.objs_addrs
    requires r.id_mappings == s.id_mappings
    requires r.activate_conds == s.activate_conds
    requires wkm_get_globals(r.wk_mstate) == wkm_get_globals(s.wk_mstate)

    ensures forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Property needed by the properties below
    ensures var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
            var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
            var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);
            (forall id :: WSM_IsOSTDID(s.objects, id) && id !in pehci_td_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)) &&
            (forall id :: WSM_IsOSFDID(s.objects, id) && id !in pehci_fd_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)) &&
            (forall id :: WSM_IsOSDOID(s.objects, id) && id !in pehci_do_ids
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid))
        // Property 1
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_pehci_activate_in_os_stack_and_statevars();

    reveal WK_ValidObjsAddrs_PEHCIs();
    reveal WK_SecureObjsAddrs_MemSeparation();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    // Prove pEHCI subject and object IDs are unchanged
    var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);

    Lemma_PEHCIsIDsObjIDsAreUnchanged(s, r);
    assert pehci_ids == WSM_AllDevIDs_pEHCIs(r.subjects, r.activate_conds);
    assert pehci_td_ids == WSM_TDsOwnedByOSDevs(r, pehci_ids);
    assert pehci_fd_ids == WSM_FDsOwnedByOSDevs(r, pehci_ids);
    assert pehci_do_ids == WSM_DOsOwnedByOSDevs(r, pehci_ids);

    // Prove property 1
    forall id | WSM_IsOSTDID(s.objects, id) && id !in pehci_td_ids
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();

        Lemma_SameIDsIffSameInternalIDs();
        assert WK_ValidObjs_ObjIDs(objs);
        assert FD_ID(id.oid) !in objs.os_fds;
        assert DO_ID(id.oid) !in objs.os_dos;
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) == objs.os_tds[id].pid;
        assert WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid) == objs'.os_tds[id].pid;

        assert objs.os_tds[id].pid == objs'.os_tds[id].pid;
    }

    forall id | WSM_IsOSFDID(s.objects, id) && id !in pehci_fd_ids
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();

        Lemma_SameIDsIffSameInternalIDs();
        assert WK_ValidObjs_ObjIDs(objs);
        assert TD_ID(id.oid) !in objs.os_tds;
        assert DO_ID(id.oid) !in objs.os_dos;
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) == objs.os_fds[id].pid;
        assert WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid) == objs'.os_fds[id].pid;

        assert objs.os_fds[id].pid == objs'.os_fds[id].pid;
    }

    forall id | WSM_IsOSDOID(s.objects, id) && id !in pehci_do_ids
        ensures WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) ==
                    WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid)
    {
        reveal WK_ValidSubjs();
        reveal WK_ValidSubjs_SubjIDs();
        reveal WK_ValidObjs();
        reveal WK_ValidObjs_ObjIDs();

        Lemma_SameIDsIffSameInternalIDs();
        assert WK_ValidObjs_ObjIDs(objs);
        assert TD_ID(id.oid) !in objs.os_tds;
        assert FD_ID(id.oid) !in objs.os_fds;
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid) == objs.os_dos[id].pid;
        assert WSM_ObjPID(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate), id.oid) == objs'.os_dos[id].pid;

        assert objs.os_dos[id].pid == objs'.os_dos[id].pid;
    }
}
