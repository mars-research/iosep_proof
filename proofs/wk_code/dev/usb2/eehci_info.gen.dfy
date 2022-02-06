include "../../ins/x86/ins_wrapper.gen.dfy"
include "..\\..\\wk_ops_commons.dfy"
include "usb_def.dfy"
include "eehci.s.dfy"
include "usb_tds.i.dfy"
include "usb_pdev.i.dfy"
include "eehci_info.i.dfy"
include "eehci_mem.i.dfy"
//-- _eehci_info_get_reserved
//--
//-- eehci_info_get_pid
//--
//-- eechi_id_get_bus_id

function method{:opaque} va_code_eechi_id_get_bus_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_SHR(va_op_word_reg(EDI),
    va_const_word(eEHCI_ID_BUSID_SHIFT_BITS)), va_CCons(va_code_AND(va_op_word_reg(EDI),
    va_const_word(eEHCI_ID_BUSID_MASK)), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma va_lemma_eechi_id_get_bus_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eechi_id_get_bus_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_retval_space := 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    bus_id:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    usb_parse_eehci_id(eehci_id).bus_id == bus_id
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0))))))
{
  reveal_va_code_eechi_id_get_bus_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b5, va_s5 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EDI));
  ghost var va_b6, va_s6 := va_lemma_Load(va_b5, va_s5, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b7, va_s7 := va_lemma_SHR(va_b6, va_s6, va_sM, va_op_word_reg(EDI),
    va_const_word(eEHCI_ID_BUSID_SHIFT_BITS));
  ghost var va_b8, va_s8 := va_lemma_AND(va_b7, va_s7, va_sM, va_op_word_reg(EDI),
    va_const_word(eEHCI_ID_BUSID_MASK));
  ghost var va_b9, va_s9 := va_lemma_Store(va_b8, va_s8, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDI));
  ghost var va_b10, va_s10 := va_lemma_POP_OneReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDI));
  ghost var va_b11, va_s11 := va_lemma_POP_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_3regs_mem_stateeq(va_old_s, va_s11);
  va_sM := va_lemma_empty(va_s11, va_sM);
}
//--
//-- _eehci_info_update_slot_to_valid_pid

function method{:opaque} va_code__eehci_info_update_slot_to_valid_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX),
    G_EEHCIs_Info()), va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP),
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 *
    ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_op_word_reg(EAX)),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Info_ENTRY_Reserved_BytesOffset)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI), va_const_word(G_EEHCI_INFO_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_EEHCIs_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(EBX)), va_CCons(va_code_STRglobal(G_EEHCIs_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(ESI), va_op_word_reg(ECX)), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma__eehci_info_update_slot_to_valid_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__eehci_info_update_slot_to_valid_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    eehci_valid_slot_id(slot) && eehci_mem_get_eehci_id(va_get_globals(va_s0), slot) !=
    eEHCI_ID_INVALID
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    EECHI_DoNotRefAnyUSBTD(va_get_globals(va_s0), slot)
  requires var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); pids_is_existing_wimp_pid(va_get_globals(va_s0), pid)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    reserved:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); eehci_info_only_change_slot_newvalue(va_get_globals(va_s0),
    va_get_globals(va_sM), slot, reserved, pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code__eehci_info_update_slot_to_valid_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var orig_esp := va_get_reg(ESP, va_s10);
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDX), G_EEHCIs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDI),
    va_op_word_reg(EAX));
  Lemma_NatMul_Ineq_4var(va_get_reg(EAX, va_s16), EEHCI_Info_ENTRY_SZ, eEHCI_INSTANCE_NUM,
    EEHCI_Info_ENTRY_SZ);
  assert isUInt32(va_get_reg(EAX, va_s16) * EEHCI_Info_ENTRY_SZ);  // line 159 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b19, va_s19 := va_lemma_MUL_Reg_32BitsResult(va_b16, va_s16, va_sM,
    va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ));
  ghost var va_b20, va_s20 := va_lemma_MOV_ToReg(va_b19, va_s19, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_ADD(va_b20, va_s20, va_sM, va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Info_ENTRY_Reserved_BytesOffset));
  ghost var va_b22, va_s22 := va_lemma_ADD(va_b21, va_s21, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_INFO_ENTRY_PID_BytesOffset));
  assert 0 <= va_get_reg(EAX, va_s22) < eEHCI_INSTANCE_NUM;  // line 166 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var offset := va_get_reg(EAX, va_s22) * EEHCI_Info_ENTRY_SZ;
  Lemma_NatMul_Ineq_NoEqualRight(va_get_reg(EAX, va_s22), eEHCI_INSTANCE_NUM, EEHCI_Info_ENTRY_SZ);
  assert 0 <= offset < eEHCI_INSTANCE_NUM * EEHCI_Info_ENTRY_SZ;  // line 169 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_NTimesUInt32IsStillAligned(va_get_reg(EAX, va_s22), EEHCI_Info_ENTRY_SZ);
  assert WordAligned(va_get_reg(EAX, va_s22) * EEHCI_Info_ENTRY_SZ);  // line 172 column 5 of file .\dev/usb2/eehci_info.vad
  assert ValidGlobalOffset(G_EEHCIs_Info(), offset);  // line 173 column 5 of file .\dev/usb2/eehci_info.vad
  assert forall usbtd_reg_id:int :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS ==>
    eehci_mem_get_usbtd_reg(va_get_globals(va_old_s), va_get_reg(EAX, va_s22), usbtd_reg_id) ==
    USBTD_SlotID_INVALID;  // line 175 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var new_globals := global_write_word(va_get_globals(va_s22), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22), va_get_reg(EBX, va_s22));
  ghost var new_this := va_s22.(wk_mstate := va_s22.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s22),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s22), G_WimpDrvs_Info());  // line 184 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 188 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfUpdateReservedFieldOnly(va_get_globals(va_s22),
    new_globals, va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22), va_get_reg(EBX, va_s22));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIINFOUpdateReservedField(va_get_globals(va_s22),
    new_globals, va_get_reg(EAX, va_s22), va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22),
    va_get_reg(EBX, va_s22));
  Lemma_EEHCIDoNotRefUSBTDs_IfSoBeforeAndGEEHCIINFOUpdateReservedField(va_get_globals(va_s22),
    new_globals, va_get_reg(EAX, va_s22), va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22),
    va_get_reg(EBX, va_s22));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s22,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s22,
    new_this);
  assert ins_valid_strglobal_word(va_s22.subjects, va_s22.objects, va_s22.id_mappings,
    va_s22.objs_addrs, va_s22.activate_conds, va_get_globals(va_s22), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22), va_get_reg(EBX, va_s22));  // line 199 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b48, va_s48 := va_lemma_STRglobal(va_b22, va_s22, va_sM, G_EEHCIs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(EBX));
  ghost var globals1 := va_get_globals(va_s48);
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIINFOUpdateReservedField(va_get_globals(va_old_s),
    globals1, va_get_reg(EAX, va_s48), va_get_reg(EDX, va_s48) + va_get_reg(EDI, va_s48),
    va_get_reg(EBX, va_s48));
  ghost var new_globals2 := global_write_word(va_get_globals(va_s48), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48), va_get_reg(ECX, va_s48));
  ghost var new_this2 := va_s48.(wk_mstate := va_s48.wk_mstate.(globals := new_globals2));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s48),
    new_globals2);
  assert global_read_fullval(new_globals2, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s48), G_WimpDrvs_Info());  // line 214 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals2);  // line 218 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfUpdatePIDToExistingPIDs(va_get_globals(va_s48),
    new_globals2, va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48), va_get_reg(ECX, va_s48));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIINFOUpdatePIDField(va_get_globals(va_s48),
    new_globals2, va_get_reg(EAX, va_s48), va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48),
    va_get_reg(ECX, va_s48));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s48,
    new_this2);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s48,
    new_this2);
  assert ins_valid_strglobal_word(va_s48.subjects, va_s48.objects, va_s48.id_mappings,
    va_s48.objs_addrs, va_s48.activate_conds, va_get_globals(va_s48), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48), va_get_reg(ECX, va_s48));  // line 227 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b67, va_s67 := va_lemma_STRglobal(va_b48, va_s48, va_sM, G_EEHCIs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIINFOUpdatePIDField(globals1,
    va_get_globals(va_s67), va_get_reg(EAX, va_s67), va_get_reg(EDX, va_s67) + va_get_reg(ESI,
    va_s67), va_get_reg(ECX, va_s67));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s67);
  assert va_get_reg(ESP, va_s67) == orig_esp;  // line 236 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b71, va_s71 := va_lemma_POP_Reg1ToReg6(va_b67, va_s67, va_sM);
  ghost var va_b72, va_s72 := va_lemma_POP_OneReg(va_b71, va_s71, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s72);
  va_sM := va_lemma_empty(va_s72, va_sM);
}
//--
//-- _eehci_info_update_slot_to_invalid_pid

function method{:opaque} va_code__eehci_info_update_slot_to_invalid_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX),
    G_EEHCIs_Info()), va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP),
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 *
    ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_op_word_reg(EAX)),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Info_ENTRY_Reserved_BytesOffset)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI), va_const_word(G_EEHCI_INFO_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_EEHCIs_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(EBX)), va_CCons(va_code_STRglobal(G_EEHCIs_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(ESI), va_op_word_reg(ECX)), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma__eehci_info_update_slot_to_invalid_pid(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__eehci_info_update_slot_to_invalid_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    eehci_valid_slot_id(slot)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    EECHI_DoNotRefAnyUSBTD(va_get_globals(va_s0), slot)
  requires var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); pid == PID_INVALID
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    reserved:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); eehci_info_only_change_slot_newvalue(va_get_globals(va_s0),
    va_get_globals(va_sM), slot, reserved, pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code__eehci_info_update_slot_to_invalid_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var orig_esp := va_get_reg(ESP, va_s10);
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDX), G_EEHCIs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDI),
    va_op_word_reg(EAX));
  Lemma_NatMul_Ineq_4var(va_get_reg(EAX, va_s16), EEHCI_Info_ENTRY_SZ, eEHCI_INSTANCE_NUM,
    EEHCI_Info_ENTRY_SZ);
  assert isUInt32(va_get_reg(EAX, va_s16) * EEHCI_Info_ENTRY_SZ);  // line 319 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b19, va_s19 := va_lemma_MUL_Reg_32BitsResult(va_b16, va_s16, va_sM,
    va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ));
  ghost var va_b20, va_s20 := va_lemma_MOV_ToReg(va_b19, va_s19, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_ADD(va_b20, va_s20, va_sM, va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Info_ENTRY_Reserved_BytesOffset));
  ghost var va_b22, va_s22 := va_lemma_ADD(va_b21, va_s21, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_INFO_ENTRY_PID_BytesOffset));
  assert 0 <= va_get_reg(EAX, va_s22) < eEHCI_INSTANCE_NUM;  // line 326 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var offset := va_get_reg(EAX, va_s22) * EEHCI_Info_ENTRY_SZ;
  Lemma_NatMul_Ineq_NoEqualRight(va_get_reg(EAX, va_s22), eEHCI_INSTANCE_NUM, EEHCI_Info_ENTRY_SZ);
  assert 0 <= offset < eEHCI_INSTANCE_NUM * EEHCI_Info_ENTRY_SZ;  // line 329 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_NTimesUInt32IsStillAligned(va_get_reg(EAX, va_s22), EEHCI_Info_ENTRY_SZ);
  assert WordAligned(va_get_reg(EAX, va_s22) * EEHCI_Info_ENTRY_SZ);  // line 332 column 5 of file .\dev/usb2/eehci_info.vad
  assert ValidGlobalOffset(G_EEHCIs_Info(), offset);  // line 333 column 5 of file .\dev/usb2/eehci_info.vad
  assert forall usbtd_reg_id:int :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS ==>
    eehci_mem_get_usbtd_reg(va_get_globals(va_old_s), va_get_reg(EAX, va_s22), usbtd_reg_id) ==
    USBTD_SlotID_INVALID;  // line 335 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var new_globals := global_write_word(va_get_globals(va_s22), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22), va_get_reg(EBX, va_s22));
  ghost var new_this := va_s22.(wk_mstate := va_s22.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s22),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s22), G_WimpDrvs_Info());  // line 344 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 348 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfUpdateReservedFieldOnly(va_get_globals(va_s22),
    new_globals, va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22), va_get_reg(EBX, va_s22));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIINFOUpdateReservedField(va_get_globals(va_s22),
    new_globals, va_get_reg(EAX, va_s22), va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22),
    va_get_reg(EBX, va_s22));
  Lemma_EEHCIDoNotRefUSBTDs_IfSoBeforeAndGEEHCIINFOUpdateReservedField(va_get_globals(va_s22),
    new_globals, va_get_reg(EAX, va_s22), va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22),
    va_get_reg(EBX, va_s22));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s22,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s22,
    new_this);
  assert ins_valid_strglobal_word(va_s22.subjects, va_s22.objects, va_s22.id_mappings,
    va_s22.objs_addrs, va_s22.activate_conds, va_get_globals(va_s22), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s22) + va_get_reg(EDI, va_s22), va_get_reg(EBX, va_s22));  // line 359 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b48, va_s48 := va_lemma_STRglobal(va_b22, va_s22, va_sM, G_EEHCIs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(EBX));
  ghost var globals1 := va_get_globals(va_s48);
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIINFOUpdateReservedField(va_get_globals(va_old_s),
    globals1, va_get_reg(EAX, va_s48), va_get_reg(EDX, va_s48) + va_get_reg(EDI, va_s48),
    va_get_reg(EBX, va_s48));
  ghost var new_globals2 := global_write_word(va_get_globals(va_s48), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48), va_get_reg(ECX, va_s48));
  ghost var new_this2 := va_s48.(wk_mstate := va_s48.wk_mstate.(globals := new_globals2));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s48),
    new_globals2);
  assert global_read_fullval(new_globals2, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s48), G_WimpDrvs_Info());  // line 374 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals2);  // line 378 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfUpdatePIDToExistingPIDs(va_get_globals(va_s48),
    new_globals2, va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48), va_get_reg(ECX, va_s48));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s48),
    new_globals2);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIINFOUpdatePIDField(va_get_globals(va_s48),
    new_globals2, va_get_reg(EAX, va_s48), va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48),
    va_get_reg(ECX, va_s48));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s48,
    new_this2);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s48,
    new_this2);
  assert ins_valid_strglobal_word(va_s48.subjects, va_s48.objects, va_s48.id_mappings,
    va_s48.objs_addrs, va_s48.activate_conds, va_get_globals(va_s48), G_EEHCIs_Info(),
    va_get_reg(EDX, va_s48) + va_get_reg(ESI, va_s48), va_get_reg(ECX, va_s48));  // line 387 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b67, va_s67 := va_lemma_STRglobal(va_b48, va_s48, va_sM, G_EEHCIs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIINFOUpdatePIDField(globals1,
    va_get_globals(va_s67), va_get_reg(EAX, va_s67), va_get_reg(EDX, va_s67) + va_get_reg(ESI,
    va_s67), va_get_reg(ECX, va_s67));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s67);
  assert va_get_reg(ESP, va_s67) == orig_esp;  // line 396 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b71, va_s71 := va_lemma_POP_Reg1ToReg6(va_b67, va_s67, va_sM);
  ghost var va_b72, va_s72 := va_lemma_POP_OneReg(va_b71, va_s71, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s72);
  va_sM := va_lemma_empty(va_s72, va_sM);
}
//--
//-- eehci_check_slot_id

function method{:opaque} va_code_eehci_check_slot_id(slot_id:va_operand_reg,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_IfElse(va_cmp_ge(va_coerce_reg_to_cmp(slot_id), va_const_cmp(0)),
    va_Block(va_CCons(va_IfElse(va_cmp_lt(va_coerce_reg_to_cmp(slot_id),
    va_const_cmp(eEHCI_INSTANCE_NUM)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(TRUE)), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))
}

lemma va_lemma_eehci_check_slot_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot_id:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_check_slot_id(slot_id, ret), va_s0, va_sN)
  requires va_is_src_reg(slot_id, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires slot_id != ret
  requires ret == Reg1
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> eehci_valid_slot_id(va_eval_reg(va_sM, slot_id))
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_eehci_check_slot_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_s2, va_c2, va_b2 := va_lemma_block(va_b1, va_s0, va_sM);
  ghost var va_cond_c2, va_s3:va_state := va_lemma_ifElse(va_get_ifCond(va_c2),
    va_get_ifTrue(va_c2), va_get_ifFalse(va_c2), va_s0, va_s2);
  if (va_cond_c2)
  {
    ghost var va_b4 := va_get_block(va_get_ifTrue(va_c2));
    ghost var va_s5, va_c5, va_b5 := va_lemma_block(va_b4, va_s3, va_s2);
    ghost var va_cond_c5, va_s6:va_state := va_lemma_ifElse(va_get_ifCond(va_c5),
      va_get_ifTrue(va_c5), va_get_ifFalse(va_c5), va_s3, va_s5);
    if (va_cond_c5)
    {
      ghost var va_b7 := va_get_block(va_get_ifTrue(va_c5));
      ghost var va_b8, va_s8 := va_lemma_MOV_ToReg(va_b7, va_s6, va_s5, ret, va_const_word(TRUE));
      va_s5 := va_lemma_empty(va_s8, va_s5);
    }
    else
    {
      ghost var va_b9 := va_get_block(va_get_ifFalse(va_c5));
      ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s6, va_s5, ret,
        va_const_word(FALSE));
      va_s5 := va_lemma_empty(va_s10, va_s5);
    }
    va_s2 := va_lemma_empty(va_s5, va_s2);
  }
  else
  {
    ghost var va_b11 := va_get_block(va_get_ifFalse(va_c2));
    ghost var va_b12, va_s12 := va_lemma_MOV_ToReg(va_b11, va_s3, va_s2, ret, va_const_word(FALSE));
    va_s2 := va_lemma_empty(va_s12, va_s2);
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- eehci_info_get_pid

function method{:opaque} va_code_eehci_info_get_pid(slot:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_EEHCIs_Info()),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_coerce_reg_to_word(slot)),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI), va_const_word(G_EEHCI_INFO_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_EEHCIs_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_info_get_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_info_get_pid(slot), va_s0, va_sN)
  requires va_is_src_reg(slot, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires slot == Reg1
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires eehci_valid_slot_id(va_eval_reg(va_s0, slot))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_info_get_pid(va_get_globals(va_s0), va_eval_reg(va_s0, slot)) == WS_PartitionID(pid)
  ensures  va_eval_reg(va_sM, slot) == va_eval_reg(va_s0, slot)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_eehci_info_get_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_WordAligned();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b4, va_s4, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b9, va_s9 := va_lemma_PUSH_OneReg(va_b8, va_s8, va_sM, va_op_reg_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDX),
    G_EEHCIs_Info());
  ghost var va_b11, va_s11 := va_lemma_MOV_ToReg(va_b10, va_s10, va_sM, va_op_reg_reg(EDI),
    va_coerce_reg_to_word(slot));
  Lemma_NatMul_Ineq_4var(va_eval_reg(va_s11, slot), EEHCI_Info_ENTRY_SZ, eEHCI_INSTANCE_NUM,
    EEHCI_Info_ENTRY_SZ);
  assert isUInt32(va_eval_reg(va_s11, slot) * EEHCI_Info_ENTRY_SZ);  // line 498 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_EEHCI_INFO_ENTRY_PID_BytesOffset));
  assert 0 <= va_eval_reg(va_s15, slot) < eEHCI_INSTANCE_NUM;  // line 503 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var offset := va_eval_reg(va_s15, slot) * EEHCI_Info_ENTRY_SZ;
  Lemma_NatMul_Ineq_NoEqualRight(va_eval_reg(va_s15, slot), eEHCI_INSTANCE_NUM,
    EEHCI_Info_ENTRY_SZ);
  assert 0 <= offset < eEHCI_INSTANCE_NUM * EEHCI_Info_ENTRY_SZ;  // line 506 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_NTimesUInt32IsStillAligned(va_eval_reg(va_s15, slot), EEHCI_Info_ENTRY_SZ);
  assert WordAligned(va_eval_reg(va_s15, slot) * EEHCI_Info_ENTRY_SZ);  // line 509 column 5 of file .\dev/usb2/eehci_info.vad
  assert ValidGlobalOffset(G_EEHCIs_Info(), offset);  // line 510 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b23, va_s23 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(EAX),
    G_EEHCIs_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b24, va_s24 := va_lemma_Store(va_b23, va_s23, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b25, va_s25 := va_lemma_POP_OneReg(va_b24, va_s24, va_sM, va_op_reg_reg(EAX));
  ghost var va_b26, va_s26 := va_lemma_POP_TwoRegs(va_b25, va_s25, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b27, va_s27 := va_lemma_POP_OneReg(va_b26, va_s26, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s27, va_sM);
}
//--
//-- eehci_find_slot_in_partition

function method{:opaque} va_code_eehci_find_slot_in_partition():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(eEHCI_INSTANCE_NUM -
    1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))))),
    va_CNil()))), va_CNil()))))))), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(eEHCI_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_eehci_find_slot_in_partition(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_find_slot_in_partition(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    result_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((ret == TRUE ==>
    eehci_valid_slot_id(result_slot)) && (ret == TRUE ==> eehci_info_get_pid(va_get_globals(va_s0),
    result_slot) == WS_PartitionID(pid))) && (ret == FALSE ==> (forall i:word ::
    eehci_valid_slot_id(i) ==> eehci_info_get_pid(va_get_globals(va_s0), i) != WS_PartitionID(pid)))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space) && va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_find_slot_in_partition();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var begin_state := va_s9;
  ghost var orig_ebp := va_get_reg(EBP, va_s9);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_pid := va_get_reg(EDI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_PUSH_VOID(va_b15, va_s15, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b17, va_s17 := va_lemma_eehci_info_get_pid(va_b16, va_s16, va_sM,
    va_op_reg_reg(EAX));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b19, va_s19 := va_lemma_POP_VOID(va_b18, va_s18, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_s20, va_c20, va_b20 := va_lemma_block(va_b19, va_s19, va_sM);
  ghost var va_cond_c20, va_s21:va_state := va_lemma_ifElse(va_get_ifCond(va_c20),
    va_get_ifTrue(va_c20), va_get_ifFalse(va_c20), va_s19, va_s20);
  if (va_cond_c20)
  {
    ghost var va_b22 := va_get_block(va_get_ifTrue(va_c20));
    ghost var va_b23, va_s23 := va_lemma_MOV_ToReg(va_b22, va_s21, va_s20, va_op_reg_reg(EDX),
      va_const_word(FALSE));
    ghost var va_b24, va_s24 := va_lemma_MOV_ToReg(va_b23, va_s23, va_s20, va_op_reg_reg(ECX),
      va_const_word(TRUE));
    va_s20 := va_lemma_empty(va_s24, va_s20);
  }
  else
  {
    ghost var va_b25 := va_get_block(va_get_ifFalse(va_c20));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s21, va_s20, va_op_reg_reg(EDX),
      va_const_word(TRUE));
    ghost var va_b27, va_s27 := va_lemma_MOV_ToReg(va_b26, va_s26, va_s20, va_op_reg_reg(ECX),
      va_const_word(FALSE));
    va_s20 := va_lemma_empty(va_s27, va_s20);
  }
  ghost var va_s28, va_c28, va_b28 := va_lemma_block(va_b20, va_s20, va_sM);
  ghost var va_n29:int, va_sW29:va_state := va_lemma_while(va_get_whileCond(va_c28),
    va_get_whileBody(va_c28), va_s20, va_s28);
  while (va_n29 > 0)
    invariant va_whileInv(va_get_whileCond(va_c28), va_get_whileBody(va_c28), va_n29, va_sW29,
      va_s28)
    invariant va_get_ok(va_sW29)
    invariant 0 <= va_get_reg(EAX, va_sW29) <= eEHCI_INSTANCE_NUM
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) <
      eEHCI_INSTANCE_NUM
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) != in_pid ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && eehci_valid_slot_id(j) ==> eehci_info_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: eehci_valid_slot_id(j) ==> eehci_info_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) == in_pid ||
      va_get_reg(EAX, va_sW29) == eEHCI_INSTANCE_NUM - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) == in_pid ==>
      eehci_valid_slot_id(va_get_reg(EAX, va_sW29)) && eehci_info_get_pid(va_get_globals(va_old_s),
      va_get_reg(EAX, va_sW29)) == WS_PartitionID(in_pid)
    invariant va_get_reg(ESP, va_sW29) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW29.wk_mstate.m,
      va_get_reg(ESP, va_sW29))
    invariant va_get_reg(ESI, va_sW29) == va_get_reg(ESI, va_old_s)
    invariant va_get_reg(EBP, va_sW29) == orig_ebp
    invariant va_get_reg(EDI, va_sW29) == in_pid
    invariant va_get_globals(va_sW29) == va_get_globals(va_old_s)
    invariant state_equal_except_mstate(va_old_s, va_sW29)
    invariant va_state_eq(va_sW29, va_update_reg(EDI, va_sW29, va_update_reg(ESI, va_sW29,
      va_update_reg(EDX, va_sW29, va_update_reg(ECX, va_sW29, va_update_reg(EBX, va_sW29,
      va_update_reg(EAX, va_sW29, va_update_mem(va_sW29, va_update_reg(EBP, va_sW29,
      va_update_reg(ESP, va_sW29, va_update_ok(va_sW29, va_s0)))))))))))
    decreases eEHCI_INSTANCE_NUM - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH_VOID(va_b31, va_s29, va_sW30, 1 * ARCH_WORD_BYTES);
    ghost var va_b33, va_s33 := va_lemma_eehci_info_get_pid(va_b32, va_s32, va_sW30,
      va_op_reg_reg(EAX));
    ghost var va_b34, va_s34 := va_lemma_Load(va_b33, va_s33, va_sW30, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b35, va_s35 := va_lemma_POP_VOID(va_b34, va_s34, va_sW30, 1 * ARCH_WORD_BYTES);
    ghost var va_s36, va_c36, va_b36 := va_lemma_block(va_b35, va_s35, va_sW30);
    ghost var va_cond_c36, va_s37:va_state := va_lemma_ifElse(va_get_ifCond(va_c36),
      va_get_ifTrue(va_c36), va_get_ifFalse(va_c36), va_s35, va_s36);
    if (va_cond_c36)
    {
      ghost var va_b38 := va_get_block(va_get_ifTrue(va_c36));
      ghost var va_b39, va_s39 := va_lemma_MOV_ToReg(va_b38, va_s37, va_s36, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b39, va_s39, va_s36, va_op_reg_reg(ECX),
        va_const_word(TRUE));
      va_s36 := va_lemma_empty(va_s40, va_s36);
    }
    else
    {
      ghost var va_b41 := va_get_block(va_get_ifFalse(va_c36));
      ghost var va_s42, va_c42, va_b42 := va_lemma_block(va_b41, va_s37, va_s36);
      ghost var va_cond_c42, va_s43:va_state := va_lemma_ifElse(va_get_ifCond(va_c42),
        va_get_ifTrue(va_c42), va_get_ifFalse(va_c42), va_s37, va_s42);
      if (va_cond_c42)
      {
        ghost var va_b44 := va_get_block(va_get_ifTrue(va_c42));
        ghost var va_b45, va_s45 := va_lemma_MOV_ToReg(va_b44, va_s43, va_s42, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        ghost var va_b46, va_s46 := va_lemma_MOV_ToReg(va_b45, va_s45, va_s42, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s42 := va_lemma_empty(va_s46, va_s42);
      }
      else
      {
        ghost var va_b47 := va_get_block(va_get_ifFalse(va_c42));
        ghost var va_b48, va_s48 := va_lemma_ADD(va_b47, va_s43, va_s42, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b49, va_s49 := va_lemma_MOV_ToReg(va_b48, va_s48, va_s42, va_op_reg_reg(EDX),
          va_const_word(TRUE));
        ghost var va_b50, va_s50 := va_lemma_MOV_ToReg(va_b49, va_s49, va_s42, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s42 := va_lemma_empty(va_s50, va_s42);
      }
      va_s36 := va_lemma_empty(va_s42, va_s36);
    }
    va_sW30 := va_lemma_empty(va_s36, va_sW30);
    va_sW29 := va_sW30;
    va_n29 := va_n29 - 1;
  }
  va_s28 := va_lemma_whileFalse(va_get_whileCond(va_c28), va_get_whileBody(va_c28), va_sW29,
    va_s28);
  ghost var va_s51, va_c51, va_b51 := va_lemma_block(va_b28, va_s28, va_sM);
  ghost var va_cond_c51, va_s52:va_state := va_lemma_ifElse(va_get_ifCond(va_c51),
    va_get_ifTrue(va_c51), va_get_ifFalse(va_c51), va_s28, va_s51);
  if (va_cond_c51)
  {
    ghost var va_b53 := va_get_block(va_get_ifTrue(va_c51));
    ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s54, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    va_s51 := va_lemma_empty(va_s55, va_s51);
  }
  else
  {
    ghost var va_b56 := va_get_block(va_get_ifFalse(va_c51));
    assert va_get_reg(EAX, va_s52) == eEHCI_INSTANCE_NUM - 1;  // line 674 column 9 of file .\dev/usb2/eehci_info.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 675 column 9 of file .\dev/usb2/eehci_info.vad
    ghost var va_b59, va_s59 := va_lemma_Store(va_b56, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s59, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(eEHCI_SlotID_EMPTY));
    va_s51 := va_lemma_empty(va_s60, va_s51);
  }
  ghost var va_b61, va_s61 := va_lemma_POP_Reg1ToReg6(va_b51, va_s51, va_sM);
  ghost var va_b62, va_s62 := va_lemma_POP_OneReg(va_b61, va_s61, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s62, va_sM);
}
//--
//-- eehci_find_slot_not_in_partition

function method{:opaque} va_code_eehci_find_slot_not_in_partition():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(eEHCI_INSTANCE_NUM -
    1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))))),
    va_CNil()))), va_CNil()))))))), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(eEHCI_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_eehci_find_slot_not_in_partition(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_find_slot_not_in_partition(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    result_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((ret == TRUE ==>
    eehci_valid_slot_id(result_slot)) && (ret == TRUE ==> eehci_info_get_pid(va_get_globals(va_s0),
    result_slot) != WS_PartitionID(pid))) && (ret == FALSE ==> (forall i:word ::
    eehci_valid_slot_id(i) ==> eehci_info_get_pid(va_get_globals(va_s0), i) == WS_PartitionID(pid)))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space) && va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_find_slot_not_in_partition();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var begin_state := va_s9;
  ghost var orig_ebp := va_get_reg(EBP, va_s9);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_pid := va_get_reg(EDI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_PUSH_VOID(va_b15, va_s15, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b17, va_s17 := va_lemma_eehci_info_get_pid(va_b16, va_s16, va_sM,
    va_op_reg_reg(EAX));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b19, va_s19 := va_lemma_POP_VOID(va_b18, va_s18, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_s20, va_c20, va_b20 := va_lemma_block(va_b19, va_s19, va_sM);
  ghost var va_cond_c20, va_s21:va_state := va_lemma_ifElse(va_get_ifCond(va_c20),
    va_get_ifTrue(va_c20), va_get_ifFalse(va_c20), va_s19, va_s20);
  if (va_cond_c20)
  {
    ghost var va_b22 := va_get_block(va_get_ifTrue(va_c20));
    ghost var va_b23, va_s23 := va_lemma_MOV_ToReg(va_b22, va_s21, va_s20, va_op_reg_reg(EDX),
      va_const_word(FALSE));
    ghost var va_b24, va_s24 := va_lemma_MOV_ToReg(va_b23, va_s23, va_s20, va_op_reg_reg(ECX),
      va_const_word(TRUE));
    va_s20 := va_lemma_empty(va_s24, va_s20);
  }
  else
  {
    ghost var va_b25 := va_get_block(va_get_ifFalse(va_c20));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s21, va_s20, va_op_reg_reg(EDX),
      va_const_word(TRUE));
    ghost var va_b27, va_s27 := va_lemma_MOV_ToReg(va_b26, va_s26, va_s20, va_op_reg_reg(ECX),
      va_const_word(FALSE));
    va_s20 := va_lemma_empty(va_s27, va_s20);
  }
  ghost var va_s28, va_c28, va_b28 := va_lemma_block(va_b20, va_s20, va_sM);
  ghost var va_n29:int, va_sW29:va_state := va_lemma_while(va_get_whileCond(va_c28),
    va_get_whileBody(va_c28), va_s20, va_s28);
  while (va_n29 > 0)
    invariant va_whileInv(va_get_whileCond(va_c28), va_get_whileBody(va_c28), va_n29, va_sW29,
      va_s28)
    invariant va_get_ok(va_sW29)
    invariant 0 <= va_get_reg(EAX, va_sW29) <= eEHCI_INSTANCE_NUM
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) <
      eEHCI_INSTANCE_NUM
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) == in_pid ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && eehci_valid_slot_id(j) ==> eehci_info_get_pid(va_get_globals(va_old_s), j) ==
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: eehci_valid_slot_id(j) ==> eehci_info_get_pid(va_get_globals(va_old_s), j) ==
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) != in_pid ||
      va_get_reg(EAX, va_sW29) == eEHCI_INSTANCE_NUM - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) != in_pid ==>
      eehci_valid_slot_id(va_get_reg(EAX, va_sW29)) && eehci_info_get_pid(va_get_globals(va_old_s),
      va_get_reg(EAX, va_sW29)) != WS_PartitionID(in_pid)
    invariant va_get_reg(ESP, va_sW29) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW29.wk_mstate.m,
      va_get_reg(ESP, va_sW29))
    invariant va_get_reg(ESI, va_sW29) == va_get_reg(ESI, va_old_s)
    invariant va_get_reg(EBP, va_sW29) == orig_ebp
    invariant va_get_reg(EDI, va_sW29) == in_pid
    invariant va_get_globals(va_sW29) == va_get_globals(va_old_s)
    invariant state_equal_except_mstate(va_old_s, va_sW29)
    invariant !(interrupts_enabled(va_get_sreg(EFLAGS, va_sW29)))
    invariant va_state_eq(va_sW29, va_update_reg(EDI, va_sW29, va_update_reg(ESI, va_sW29,
      va_update_reg(EDX, va_sW29, va_update_reg(ECX, va_sW29, va_update_reg(EBX, va_sW29,
      va_update_reg(EAX, va_sW29, va_update_mem(va_sW29, va_update_reg(EBP, va_sW29,
      va_update_reg(ESP, va_sW29, va_update_ok(va_sW29, va_s0)))))))))))
    decreases eEHCI_INSTANCE_NUM - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH_VOID(va_b31, va_s29, va_sW30, 1 * ARCH_WORD_BYTES);
    ghost var va_b33, va_s33 := va_lemma_eehci_info_get_pid(va_b32, va_s32, va_sW30,
      va_op_reg_reg(EAX));
    ghost var va_b34, va_s34 := va_lemma_Load(va_b33, va_s33, va_sW30, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b35, va_s35 := va_lemma_POP_VOID(va_b34, va_s34, va_sW30, 1 * ARCH_WORD_BYTES);
    ghost var va_s36, va_c36, va_b36 := va_lemma_block(va_b35, va_s35, va_sW30);
    ghost var va_cond_c36, va_s37:va_state := va_lemma_ifElse(va_get_ifCond(va_c36),
      va_get_ifTrue(va_c36), va_get_ifFalse(va_c36), va_s35, va_s36);
    if (va_cond_c36)
    {
      ghost var va_b38 := va_get_block(va_get_ifTrue(va_c36));
      ghost var va_b39, va_s39 := va_lemma_MOV_ToReg(va_b38, va_s37, va_s36, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b39, va_s39, va_s36, va_op_reg_reg(ECX),
        va_const_word(TRUE));
      va_s36 := va_lemma_empty(va_s40, va_s36);
    }
    else
    {
      ghost var va_b41 := va_get_block(va_get_ifFalse(va_c36));
      ghost var va_s42, va_c42, va_b42 := va_lemma_block(va_b41, va_s37, va_s36);
      ghost var va_cond_c42, va_s43:va_state := va_lemma_ifElse(va_get_ifCond(va_c42),
        va_get_ifTrue(va_c42), va_get_ifFalse(va_c42), va_s37, va_s42);
      if (va_cond_c42)
      {
        ghost var va_b44 := va_get_block(va_get_ifTrue(va_c42));
        ghost var va_b45, va_s45 := va_lemma_MOV_ToReg(va_b44, va_s43, va_s42, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        ghost var va_b46, va_s46 := va_lemma_MOV_ToReg(va_b45, va_s45, va_s42, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s42 := va_lemma_empty(va_s46, va_s42);
      }
      else
      {
        ghost var va_b47 := va_get_block(va_get_ifFalse(va_c42));
        ghost var va_b48, va_s48 := va_lemma_ADD(va_b47, va_s43, va_s42, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b49, va_s49 := va_lemma_MOV_ToReg(va_b48, va_s48, va_s42, va_op_reg_reg(EDX),
          va_const_word(TRUE));
        ghost var va_b50, va_s50 := va_lemma_MOV_ToReg(va_b49, va_s49, va_s42, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s42 := va_lemma_empty(va_s50, va_s42);
      }
      va_s36 := va_lemma_empty(va_s42, va_s36);
    }
    va_sW30 := va_lemma_empty(va_s36, va_sW30);
    va_sW29 := va_sW30;
    va_n29 := va_n29 - 1;
  }
  va_s28 := va_lemma_whileFalse(va_get_whileCond(va_c28), va_get_whileBody(va_c28), va_sW29,
    va_s28);
  ghost var va_s51, va_c51, va_b51 := va_lemma_block(va_b28, va_s28, va_sM);
  ghost var va_cond_c51, va_s52:va_state := va_lemma_ifElse(va_get_ifCond(va_c51),
    va_get_ifTrue(va_c51), va_get_ifFalse(va_c51), va_s28, va_s51);
  if (va_cond_c51)
  {
    ghost var va_b53 := va_get_block(va_get_ifTrue(va_c51));
    assert va_get_reg(EBP, va_s52) == orig_ebp;  // line 833 column 9 of file .\dev/usb2/eehci_info.vad
    ghost var va_b55, va_s55 := va_lemma_Store(va_b53, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s55, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    va_s51 := va_lemma_empty(va_s56, va_s51);
  }
  else
  {
    ghost var va_b57 := va_get_block(va_get_ifFalse(va_c51));
    assert va_get_reg(EBP, va_s52) == orig_ebp;  // line 839 column 9 of file .\dev/usb2/eehci_info.vad
    assert va_get_reg(EAX, va_s52) == eEHCI_INSTANCE_NUM - 1;  // line 840 column 9 of file .\dev/usb2/eehci_info.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 841 column 9 of file .\dev/usb2/eehci_info.vad
    ghost var va_b61, va_s61 := va_lemma_Store(va_b57, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s61, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(eEHCI_SlotID_EMPTY));
    va_s51 := va_lemma_empty(va_s62, va_s51);
  }
  ghost var va_b63, va_s63 := va_lemma_POP_Reg1ToReg6(va_b51, va_s51, va_sM);
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b63, va_s63, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s64);
  va_sM := va_lemma_empty(va_s64, va_sM);
}
//--
//-- _eehci_info_get_reserved

function method{:opaque} va_code__eehci_info_get_reserved(slot:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_EEHCIs_Info()),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_coerce_reg_to_word(slot)),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Info_ENTRY_Reserved_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_EEHCIs_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma__eehci_info_get_reserved(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__eehci_info_get_reserved(slot), va_s0, va_sN)
  requires va_is_src_reg(slot, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires slot == Reg1
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires eehci_valid_slot_id(va_eval_reg(va_s0, slot))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var v:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_info_get_reserved(va_get_globals(va_s0), va_eval_reg(va_s0, slot)) == v
  ensures  va_eval_reg(va_sM, slot) == va_eval_reg(va_s0, slot)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code__eehci_info_get_reserved();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_WordAligned();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b4, va_s4, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b9, va_s9 := va_lemma_PUSH_OneReg(va_b8, va_s8, va_sM, va_op_reg_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDX),
    G_EEHCIs_Info());
  ghost var va_b11, va_s11 := va_lemma_MOV_ToReg(va_b10, va_s10, va_sM, va_op_reg_reg(EDI),
    va_coerce_reg_to_word(slot));
  Lemma_NatMul_Ineq_4var(va_eval_reg(va_s11, slot), EEHCI_Info_ENTRY_SZ, eEHCI_INSTANCE_NUM,
    EEHCI_Info_ENTRY_SZ);
  assert isUInt32(va_eval_reg(va_s11, slot) * EEHCI_Info_ENTRY_SZ);  // line 916 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(EEHCI_Info_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Info_ENTRY_Reserved_BytesOffset));
  assert 0 <= va_eval_reg(va_s15, slot) < eEHCI_INSTANCE_NUM;  // line 921 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var offset := va_eval_reg(va_s15, slot) * EEHCI_Info_ENTRY_SZ;
  Lemma_NatMul_Ineq_NoEqualRight(va_eval_reg(va_s15, slot), eEHCI_INSTANCE_NUM,
    EEHCI_Info_ENTRY_SZ);
  assert 0 <= offset < eEHCI_INSTANCE_NUM * EEHCI_Info_ENTRY_SZ;  // line 924 column 5 of file .\dev/usb2/eehci_info.vad
  Lemma_NTimesUInt32IsStillAligned(va_eval_reg(va_s15, slot), EEHCI_Info_ENTRY_SZ);
  assert WordAligned(va_eval_reg(va_s15, slot) * EEHCI_Info_ENTRY_SZ);  // line 927 column 5 of file .\dev/usb2/eehci_info.vad
  assert ValidGlobalOffset(G_EEHCIs_Info(), offset);  // line 928 column 5 of file .\dev/usb2/eehci_info.vad
  ghost var va_b23, va_s23 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(EAX),
    G_EEHCIs_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b24, va_s24 := va_lemma_Store(va_b23, va_s23, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b25, va_s25 := va_lemma_POP_OneReg(va_b24, va_s24, va_sM, va_op_reg_reg(EAX));
  ghost var va_b26, va_s26 := va_lemma_POP_TwoRegs(va_b25, va_s25, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b27, va_s27 := va_lemma_POP_OneReg(va_b26, va_s26, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s27, va_sM);
}
//--
