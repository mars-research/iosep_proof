include "../../ins/x86/ins_wrapper.gen.dfy"
include "..\\..\\wk_ops_commons.dfy"
include "usb_def.dfy"
include "eehci.s.dfy"
include "eehci_info.i.dfy"
include "usb_tds.i.dfy"
include "usb_pdev.i.dfy"
include "eehci_mem.i.dfy"
include "usb_tds_ops\\usb_tds_checks.i.dfy"
//-- eehci_check_usbtd_reg_id

function method{:opaque} va_code_eehci_check_usbtd_reg_id(usbtd_reg_id:va_operand_reg,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_IfElse(va_cmp_ge(va_coerce_reg_to_cmp(usbtd_reg_id), va_const_cmp(0)),
    va_Block(va_CCons(va_IfElse(va_cmp_lt(va_coerce_reg_to_cmp(usbtd_reg_id),
    va_const_cmp(eEHCI_USBTD_SlotID_NUMS)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(TRUE)), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))
}

lemma va_lemma_eehci_check_usbtd_reg_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  usbtd_reg_id:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_check_usbtd_reg_id(usbtd_reg_id, ret), va_s0, va_sN)
  requires va_is_src_reg(usbtd_reg_id, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires usbtd_reg_id != ret
  requires ret == Reg1
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> 0 <= va_eval_reg(va_sM, usbtd_reg_id) <
    eEHCI_USBTD_SlotID_NUMS
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_eehci_check_usbtd_reg_id();
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
//-- eehci_mem_read_id

function method{:opaque} va_code_eehci_mem_read_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_EEHCI_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma_eehci_mem_read_id(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_mem_read_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    val:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_mem_get_eehci_id(va_get_globals(va_s0), slot) == val
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_mem_read_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 109 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset));
  lemma_DistinctGlobals();
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_EEHCI_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- eehci_write_config

function method{:opaque} va_code_eehci_write_config():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_write_config(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_write_config(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    eehci_mem_get_config_reg(va_get_globals(va_sM), slot) == new_v && (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_eehci_write_config();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 194 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var new_globals := global_write_word(va_get_globals(va_s16), G_EEHCI_MEM(), va_get_reg(EBX,
    va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  ghost var new_this := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s16), G_WimpDrvs_Info());  // line 207 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 211 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIConfig(va_get_globals(va_s16),
    new_globals, slot, va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_EEHCI_MEM(),
    va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));  // line 220 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_EEHCI_MEM(),
    va_op_reg_reg(EBX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s33));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_TwoRegs(va_b33, va_s33, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b37, va_s37 := va_lemma_POP_OneReg(va_b36, va_s36, va_sM, va_op_reg_reg(EBX));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- eehci_read_config

function method{:opaque} va_code_eehci_read_config():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ECX), G_EEHCI_MEM(), va_op_reg_reg(EBX),
    va_op_word_reg(ESI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_read_config(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_read_config(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    val:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_mem_get_config_reg(va_get_globals(va_s0), slot) == val
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_read_config();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 296 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI));
  ghost var va_b17, va_s17 := va_lemma_Store(va_b16, va_s16, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ECX));
  ghost var va_b18, va_s18 := va_lemma_POP_TwoRegs(va_b17, va_s17, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(EBX));
  ghost var va_b20, va_s20 := va_lemma_POP_OneReg(va_b19, va_s19, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s20, va_sM);
}
//--
//-- eehci_write_status

function method{:opaque} va_code_eehci_write_status():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_write_status(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_write_status(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    eehci_mem_get_status_reg(va_get_globals(va_sM), slot) == new_v && (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_eehci_write_status();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 379 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var new_globals := global_write_word(va_get_globals(va_s16), G_EEHCI_MEM(), va_get_reg(EBX,
    va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  ghost var new_this := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s16), G_WimpDrvs_Info());  // line 392 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 396 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIStatus(va_get_globals(va_s16),
    new_globals, slot, va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_EEHCI_MEM(),
    va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));  // line 405 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_EEHCI_MEM(),
    va_op_reg_reg(EBX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s33));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_TwoRegs(va_b33, va_s33, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b37, va_s37 := va_lemma_POP_OneReg(va_b36, va_s36, va_sM, va_op_reg_reg(EBX));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- eehci_read_status

function method{:opaque} va_code_eehci_read_status():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ECX), G_EEHCI_MEM(), va_op_reg_reg(EBX),
    va_op_word_reg(ESI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_read_status(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_read_status(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    val:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_mem_get_status_reg(va_get_globals(va_s0), slot) == val
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_read_status();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 481 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI));
  ghost var va_b17, va_s17 := va_lemma_Store(va_b16, va_s16, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ECX));
  ghost var va_b18, va_s18 := va_lemma_POP_TwoRegs(va_b17, va_s17, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(EBX));
  ghost var va_b20, va_s20 := va_lemma_POP_OneReg(va_b19, va_s19, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s20, va_sM);
}
//--
//-- eehci_write_intr_enable

function method{:opaque} va_code_eehci_write_intr_enable():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_write_intr_enable(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_write_intr_enable(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); new_v == eEHCI_Intr_Disable
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    eehci_mem_get_intr_enable_reg(va_get_globals(va_sM), slot) == new_v && (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_eehci_write_intr_enable();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 567 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var new_globals := global_write_word(va_get_globals(va_s16), G_EEHCI_MEM(), va_get_reg(EBX,
    va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  ghost var new_this := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s16), G_WimpDrvs_Info());  // line 580 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 584 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIIntrEnable(va_get_globals(va_s16),
    new_globals, slot, va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_EEHCI_MEM(),
    va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));  // line 593 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_EEHCI_MEM(),
    va_op_reg_reg(EBX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s33));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_TwoRegs(va_b33, va_s33, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b37, va_s37 := va_lemma_POP_OneReg(va_b36, va_s36, va_sM, va_op_reg_reg(EBX));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- eehci_read_intr_enable

function method{:opaque} va_code_eehci_read_intr_enable():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ECX), G_EEHCI_MEM(), va_op_reg_reg(EBX),
    va_op_word_reg(ESI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_read_intr_enable(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_read_intr_enable(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    val:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_mem_get_intr_enable_reg(va_get_globals(va_s0), slot) == val
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_read_intr_enable();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 669 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI));
  ghost var va_b17, va_s17 := va_lemma_Store(va_b16, va_s16, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ECX));
  ghost var va_b18, va_s18 := va_lemma_POP_TwoRegs(va_b17, va_s17, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(EBX));
  ghost var va_b20, va_s20 := va_lemma_POP_OneReg(va_b19, va_s19, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s20, va_sM);
}
//--
//-- eehci_write_intr_target

function method{:opaque} va_code_eehci_write_intr_target():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_write_intr_target(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_write_intr_target(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    eehci_mem_get_intr_target_reg(va_get_globals(va_sM), slot) == new_v && (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_eehci_write_intr_target();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 752 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var new_globals := global_write_word(va_get_globals(va_s16), G_EEHCI_MEM(), va_get_reg(EBX,
    va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  ghost var new_this := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s16), G_WimpDrvs_Info());  // line 765 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 769 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIIntrTarget(va_get_globals(va_s16),
    new_globals, slot, va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_EEHCI_MEM(),
    va_get_reg(EBX, va_s16) + va_get_reg(ESI, va_s16), va_get_reg(ECX, va_s16));  // line 778 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_EEHCI_MEM(),
    va_op_reg_reg(EBX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s33));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_TwoRegs(va_b33, va_s33, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b37, va_s37 := va_lemma_POP_OneReg(va_b36, va_s36, va_sM, va_op_reg_reg(EBX));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- eehci_read_intr_target

function method{:opaque} va_code_eehci_read_intr_target():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ECX), G_EEHCI_MEM(), va_op_reg_reg(EBX),
    va_op_word_reg(ESI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_eehci_read_intr_target(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_read_intr_target(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    val:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_mem_get_intr_target_reg(va_get_globals(va_s0), slot) == val
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_read_intr_target();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 854 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI));
  ghost var va_b17, va_s17 := va_lemma_Store(va_b16, va_s16, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ECX));
  ghost var va_b18, va_s18 := va_lemma_POP_TwoRegs(va_b17, va_s17, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(EBX));
  ghost var va_b20, va_s20 := va_lemma_POP_OneReg(va_b19, va_s19, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s20, va_sM);
}
//--
//-- eehci_write_usbtd_slot

function method{:opaque} va_code_eehci_write_usbtd_slot():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ECX), va_const_word(UINT32_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI), va_op_word_reg(ECX)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma_eehci_write_usbtd_slot(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_write_usbtd_slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    eehci_valid_slot_id(slot) && eehci_is_active_wimp_eehci(va_get_globals(va_s0), slot)
  requires var usbtd_reg_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
  requires var eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); ((((new_usbtd_slot_id == USBTD_SlotID_INVALID ||
    usbtd_map_valid_slot_id(new_usbtd_slot_id)) && (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==>
    (var usbtd_idword := usbtd_map_get_idword(va_get_globals(va_s0), new_usbtd_slot_id);
    usbtd_idword != USBTD_ID_INVALID))) && (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (var
    usbtd_flags := usbtd_map_get_flags(va_get_globals(va_s0), new_usbtd_slot_id); usbtd_flags ==
    SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))) &&
    (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (var eehci_pid :=
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot); var usbtd_pid :=
    usbtd_map_get_pid(va_get_globals(va_s0), new_usbtd_slot_id); eehci_pid == usbtd_pid))) &&
    (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> usbtd_slot_valid_busid(va_get_globals(va_s0),
    new_usbtd_slot_id) && (var eehci_busid:uint16 :=
    usb_parse_eehci_id(eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot)).bus_id; var
    usbtd_busid:uint16 := usbtd_map_get_busid(va_get_globals(va_s0), new_usbtd_slot_id);
    eehci_busid == usbtd_busid))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    usbtd_reg_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); eehci_mem_get_usbtd_reg(va_get_globals(va_sM), slot, usbtd_reg_id) == new_v
    && (var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES; va_get_globals(va_sM)
    == global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_eehci_write_usbtd_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EBX),
    G_EEHCI_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(ESI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 971 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(ESI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var usbtd_slot := va_get_reg(ECX, va_s16);
  Lemma_NatMul_Ineq_4var(usbtd_slot, UINT32_BYTES, eEHCI_USBTD_SlotID_NUMS, UINT32_BYTES);
  assert isUInt32(usbtd_slot * UINT32_BYTES);  // line 978 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b20, va_s20 := va_lemma_MUL_Reg_32BitsResult(va_b16, va_s16, va_sM,
    va_op_reg_reg(ECX), va_const_word(UINT32_BYTES));
  ghost var va_b21, va_s21 := va_lemma_ADD(va_b20, va_s20, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(ECX));
  ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var new_globals := global_write_word(va_get_globals(va_s22), G_EEHCI_MEM(), va_get_reg(EBX,
    va_s22) + va_get_reg(ESI, va_s22), va_get_reg(ECX, va_s22));
  ghost var new_this := va_s22.(wk_mstate := va_s22.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s22),
    new_globals);
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s22), G_WimpDrvs_Info());  // line 991 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  assert WK_WimpDrvs_ValidGlobalVarValues(new_globals);  // line 995 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s22),
    new_globals);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg(va_get_globals(va_s22), new_globals,
    slot, usbtd_slot, va_get_reg(EBX, va_s22) + va_get_reg(ESI, va_s22), va_get_reg(ECX, va_s22));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s22,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s22,
    new_this);
  assert ins_valid_strglobal_word(va_s22.subjects, va_s22.objects, va_s22.id_mappings,
    va_s22.objs_addrs, va_s22.activate_conds, va_get_globals(va_s22), G_EEHCI_MEM(),
    va_get_reg(EBX, va_s22) + va_get_reg(ESI, va_s22), va_get_reg(ECX, va_s22));  // line 1004 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b39, va_s39 := va_lemma_STRglobal(va_b22, va_s22, va_sM, G_EEHCI_MEM(),
    va_op_reg_reg(EBX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s39));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s39);
  ghost var va_b42, va_s42 := va_lemma_POP_TwoRegs(va_b39, va_s39, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b43, va_s43 := va_lemma_POP_OneReg(va_b42, va_s42, va_sM, va_op_reg_reg(EBX));
  ghost var va_b44, va_s44 := va_lemma_POP_OneReg(va_b43, va_s43, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s44, va_sM);
}
//--
//-- eehci_read_usbtd_slot

function method{:opaque} va_code_eehci_read_usbtd_slot():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_EEHCI_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI), va_const_word(eEHCI_INSTANCE_BYTES)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(ECX), va_const_word(UINT32_BYTES)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI), va_op_word_reg(ECX)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EDX), G_EEHCI_MEM(), va_op_reg_reg(EBX),
    va_op_word_reg(ESI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma_eehci_read_usbtd_slot(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_read_usbtd_slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    eEHCI_INSTANCE_NUM
  requires var usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); 0 <= usbtd_slot_id < eEHCI_USBTD_SlotID_NUMS
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var val:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    eehci_mem_get_usbtd_reg(va_get_globals(va_s0), slot, usbtd_slot_id) == val
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_eehci_read_usbtd_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b11, va_s11 := va_lemma_PUSH_TwoRegs(va_b10, va_s10, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(ECX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(EBX), G_EEHCI_MEM());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, eEHCI_INSTANCE_BYTES, eEHCI_INSTANCE_NUM, eEHCI_INSTANCE_BYTES);
  assert isUInt32(slot * eEHCI_INSTANCE_BYTES);  // line 1087 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(eEHCI_INSTANCE_BYTES));
  ghost var va_b18, va_s18 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b19, va_s19 := va_lemma_ADD(va_b18, va_s18, va_sM, va_op_word_reg(ESI),
    va_const_word(G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset));
  ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var usbtd_slot := va_get_reg(ECX, va_s20);
  Lemma_NatMul_Ineq_4var(usbtd_slot, UINT32_BYTES, eEHCI_USBTD_SlotID_NUMS, UINT32_BYTES);
  assert isUInt32(usbtd_slot * UINT32_BYTES);  // line 1095 column 5 of file .\dev/usb2/eehci_mem_utils.vad
  ghost var va_b24, va_s24 := va_lemma_MUL_Reg_32BitsResult(va_b20, va_s20, va_sM,
    va_op_reg_reg(ECX), va_const_word(UINT32_BYTES));
  ghost var va_b25, va_s25 := va_lemma_ADD(va_b24, va_s24, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(ECX));
  ghost var va_b26, va_s26 := va_lemma_LDRglobal(va_b25, va_s25, va_sM, va_op_word_reg(EDX),
    G_EEHCI_MEM(), va_op_reg_reg(EBX), va_op_word_reg(ESI));
  ghost var va_b27, va_s27 := va_lemma_Store(va_b26, va_s26, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDX));
  ghost var va_b28, va_s28 := va_lemma_POP_TwoRegs(va_b27, va_s27, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(ECX));
  ghost var va_b29, va_s29 := va_lemma_POP_TwoRegs(va_b28, va_s28, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b30, va_s30 := va_lemma_POP_OneReg(va_b29, va_s29, va_sM, va_op_reg_reg(EBX));
  ghost var va_b31, va_s31 := va_lemma_POP_OneReg(va_b30, va_s30, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s31, va_sM);
}
//--
//-- eehci_mem_usbtd_reg_find_nonempty_slot

function method{:opaque} va_code_eehci_mem_usbtd_reg_find_nonempty_slot(eehci_slot:va_operand_reg,
  result_slot:va_operand_reg, ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_const_word(0)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_coerce_reg_to_word(eehci_slot)),
    va_CCons(va_code_eehci_read_usbtd_slot(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_const_cmp(USBTD_SlotID_INVALID)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_coerce_reg_to_word(eehci_slot)),
    va_CCons(va_code_eehci_read_usbtd_slot(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_const_cmp(USBTD_SlotID_INVALID)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(eEHCI_USBTD_SlotID_NUMS
    - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EDI), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))))),
    va_CNil()))), va_CNil())))))))), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX),
    va_const_cmp(USBTD_SlotID_INVALID)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(TRUE)), va_CCons(va_code_MOV_ToReg(result_slot, va_op_word_reg(EDI)),
    va_CNil()))), va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(result_slot, va_const_word(0)), va_CNil())))),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)), va_CNil())))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_eehci_mem_usbtd_reg_find_nonempty_slot(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state, eehci_slot:va_operand_reg, result_slot:va_operand_reg,
  ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_mem_usbtd_reg_find_nonempty_slot(eehci_slot,
    result_slot, ret), va_s0, va_sN)
  requires va_is_src_reg(eehci_slot, va_s0)
  requires va_is_dst_reg(result_slot, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires eehci_slot == Reg1
  requires result_slot == Reg2
  requires ret == Reg3
  requires var stack_req_space := 2 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES + 8 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
  requires eehci_valid_slot_id(va_eval_reg(va_s0, eehci_slot))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> 0 <= va_eval_reg(va_sM, result_slot) <
    eEHCI_USBTD_SlotID_NUMS
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> eehci_mem_get_usbtd_reg(va_get_globals(va_s0),
    va_eval_reg(va_s0, eehci_slot), va_eval_reg(va_sM, result_slot)) != USBTD_SlotID_INVALID
  ensures  va_eval_reg(va_sM, ret) == FALSE ==> EECHI_DoNotRefAnyUSBTD(va_get_globals(va_s0),
    va_eval_reg(va_s0, eehci_slot))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_update_operand_reg(result_slot, va_sM,
    va_s0)))))))))))))
{
  reveal_va_code_eehci_mem_usbtd_reg_find_nonempty_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b6, va_s6 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var begin_state := va_s6;
  ghost var in_eehci_slot := va_eval_reg(va_s6, eehci_slot);
  ghost var va_b9, va_s9 := va_lemma_MOV_ToReg(va_b6, va_s6, va_sM, va_op_reg_reg(EDI),
    va_const_word(0));
  ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b11, va_s11 := va_lemma_PUSH(va_b10, va_s10, va_sM, va_op_word_reg(EDI));
  ghost var va_b12, va_s12 := va_lemma_PUSH(va_b11, va_s11, va_sM,
    va_coerce_reg_to_word(eehci_slot));
  ghost var va_b13, va_s13 := va_lemma_eehci_read_usbtd_slot(va_b12, va_s12, va_sM);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b15, va_s15 := va_lemma_POP_VOID(va_b14, va_s14, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s16, va_c16, va_b16 := va_lemma_block(va_b15, va_s15, va_sM);
  ghost var va_cond_c16, va_s17:va_state := va_lemma_ifElse(va_get_ifCond(va_c16),
    va_get_ifTrue(va_c16), va_get_ifFalse(va_c16), va_s15, va_s16);
  if (va_cond_c16)
  {
    ghost var va_b18 := va_get_block(va_get_ifTrue(va_c16));
    ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b18, va_s17, va_s16, va_op_reg_reg(EDX),
      va_const_word(FALSE));
    ghost var va_b20, va_s20 := va_lemma_MOV_ToReg(va_b19, va_s19, va_s16, va_op_reg_reg(ECX),
      va_const_word(TRUE));
    va_s16 := va_lemma_empty(va_s20, va_s16);
  }
  else
  {
    ghost var va_b21 := va_get_block(va_get_ifFalse(va_c16));
    ghost var va_b22, va_s22 := va_lemma_MOV_ToReg(va_b21, va_s17, va_s16, va_op_reg_reg(EDX),
      va_const_word(TRUE));
    ghost var va_b23, va_s23 := va_lemma_MOV_ToReg(va_b22, va_s22, va_s16, va_op_reg_reg(ECX),
      va_const_word(FALSE));
    va_s16 := va_lemma_empty(va_s23, va_s16);
  }
  ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b16, va_s16, va_sM);
  ghost var va_n25:int, va_sW25:va_state := va_lemma_while(va_get_whileCond(va_c24),
    va_get_whileBody(va_c24), va_s16, va_s24);
  while (va_n25 > 0)
    invariant va_whileInv(va_get_whileCond(va_c24), va_get_whileBody(va_c24), va_n25, va_sW25,
      va_s24)
    invariant va_get_ok(va_sW25)
    invariant va_eval_reg(va_sW25, eehci_slot) == in_eehci_slot
    invariant 0 <= va_get_reg(EDI, va_sW25) <= eEHCI_USBTD_SlotID_NUMS
    invariant va_get_reg(EDX, va_sW25) == TRUE ==> 0 <= va_get_reg(EDI, va_sW25) <
      eEHCI_USBTD_SlotID_NUMS
    invariant va_get_reg(EDX, va_sW25) == TRUE ==> va_get_reg(ECX, va_sW25) == FALSE
    invariant va_get_reg(EBX, va_sW25) == USBTD_SlotID_INVALID ==> va_get_reg(ECX, va_sW25) == FALSE
    invariant va_get_reg(ECX, va_sW25) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EDI,
      va_sW25) && 0 <= j < eEHCI_USBTD_SlotID_NUMS ==>
      eehci_mem_get_usbtd_reg(va_get_globals(va_old_s), va_eval_reg(va_sW25, eehci_slot), j) ==
      USBTD_SlotID_INVALID)
    invariant va_get_reg(EDX, va_sW25) != TRUE && va_get_reg(ECX, va_sW25) == FALSE ==> (forall
      j:uint32 :: 0 <= j < eEHCI_USBTD_SlotID_NUMS ==>
      eehci_mem_get_usbtd_reg(va_get_globals(va_old_s), va_eval_reg(va_sW25, eehci_slot), j) ==
      USBTD_SlotID_INVALID)
    invariant va_get_reg(EDX, va_sW25) != TRUE ==> va_get_reg(EBX, va_sW25) != USBTD_SlotID_INVALID
      || va_get_reg(EDI, va_sW25) == eEHCI_USBTD_SlotID_NUMS - 1
    invariant va_get_reg(EDX, va_sW25) != TRUE && va_get_reg(EBX, va_sW25) != USBTD_SlotID_INVALID
      ==> 0 <= va_get_reg(EDI, va_sW25) < eEHCI_USBTD_SlotID_NUMS &&
      eehci_mem_get_usbtd_reg(va_get_globals(va_old_s), va_eval_reg(va_sW25, eehci_slot),
      va_get_reg(EDI, va_sW25)) != USBTD_SlotID_INVALID
    invariant va_get_reg(ESP, va_sW25) == va_get_reg(ESP, va_old_s) - 2 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW25.wk_mstate.m,
      va_get_reg(ESP, va_sW25))
    invariant va_get_reg(ESI, va_sW25) == va_get_reg(ESI, va_old_s)
    invariant va_get_reg(EBP, va_sW25) == va_get_reg(EBP, va_old_s)
    invariant va_get_globals(va_sW25) == va_get_globals(va_old_s)
    invariant state_equal_except_mstate(va_old_s, va_sW25)
    invariant va_state_eq(va_sW25, va_update_reg(EBP, va_sW25, va_update_reg(ESI, va_sW25,
      va_update_reg(EDI, va_sW25, va_update_reg(EDX, va_sW25, va_update_mem(va_sW25,
      va_update_reg(ESP, va_sW25, va_update_reg(ECX, va_sW25, va_update_reg(EBX, va_sW25,
      va_update_reg(EAX, va_sW25, va_update_ok(va_sW25, va_update_operand_reg(ret, va_sW25,
      va_update_operand_reg(result_slot, va_sW25, va_s0)))))))))))))
    decreases eEHCI_USBTD_SlotID_NUMS - va_get_reg(EDI, va_sW25), va_get_reg(EDX, va_sW25)
  {
    ghost var va_s25:va_state, va_sW26:va_state := va_lemma_whileTrue(va_get_whileCond(va_c24),
      va_get_whileBody(va_c24), va_n25, va_sW25, va_s24);
    ghost var va_b27 := va_get_block(va_get_whileBody(va_c24));
    ghost var va_b28, va_s28 := va_lemma_PUSH(va_b27, va_s25, va_sW26, va_op_word_reg(EDI));
    ghost var va_b29, va_s29 := va_lemma_PUSH(va_b28, va_s28, va_sW26,
      va_coerce_reg_to_word(eehci_slot));
    ghost var va_b30, va_s30 := va_lemma_eehci_read_usbtd_slot(va_b29, va_s29, va_sW26);
    ghost var va_b31, va_s31 := va_lemma_Load(va_b30, va_s30, va_sW26, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b32, va_s32 := va_lemma_POP_VOID(va_b31, va_s31, va_sW26, 2 * ARCH_WORD_BYTES);
    ghost var va_s33, va_c33, va_b33 := va_lemma_block(va_b32, va_s32, va_sW26);
    ghost var va_cond_c33, va_s34:va_state := va_lemma_ifElse(va_get_ifCond(va_c33),
      va_get_ifTrue(va_c33), va_get_ifFalse(va_c33), va_s32, va_s33);
    if (va_cond_c33)
    {
      ghost var va_b35 := va_get_block(va_get_ifTrue(va_c33));
      ghost var va_b36, va_s36 := va_lemma_MOV_ToReg(va_b35, va_s34, va_s33, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      ghost var va_b37, va_s37 := va_lemma_MOV_ToReg(va_b36, va_s36, va_s33, va_op_reg_reg(ECX),
        va_const_word(TRUE));
      va_s33 := va_lemma_empty(va_s37, va_s33);
    }
    else
    {
      ghost var va_b38 := va_get_block(va_get_ifFalse(va_c33));
      ghost var va_s39, va_c39, va_b39 := va_lemma_block(va_b38, va_s34, va_s33);
      ghost var va_cond_c39, va_s40:va_state := va_lemma_ifElse(va_get_ifCond(va_c39),
        va_get_ifTrue(va_c39), va_get_ifFalse(va_c39), va_s34, va_s39);
      if (va_cond_c39)
      {
        ghost var va_b41 := va_get_block(va_get_ifTrue(va_c39));
        ghost var va_b42, va_s42 := va_lemma_MOV_ToReg(va_b41, va_s40, va_s39, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        ghost var va_b43, va_s43 := va_lemma_MOV_ToReg(va_b42, va_s42, va_s39, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s39 := va_lemma_empty(va_s43, va_s39);
      }
      else
      {
        ghost var va_b44 := va_get_block(va_get_ifFalse(va_c39));
        ghost var va_b45, va_s45 := va_lemma_ADD(va_b44, va_s40, va_s39, va_op_word_reg(EDI),
          va_const_word(1));
        ghost var va_b46, va_s46 := va_lemma_MOV_ToReg(va_b45, va_s45, va_s39, va_op_reg_reg(EDX),
          va_const_word(TRUE));
        ghost var va_b47, va_s47 := va_lemma_MOV_ToReg(va_b46, va_s46, va_s39, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s39 := va_lemma_empty(va_s47, va_s39);
      }
      va_s33 := va_lemma_empty(va_s39, va_s33);
    }
    va_sW26 := va_lemma_empty(va_s33, va_sW26);
    va_sW25 := va_sW26;
    va_n25 := va_n25 - 1;
  }
  va_s24 := va_lemma_whileFalse(va_get_whileCond(va_c24), va_get_whileBody(va_c24), va_sW25,
    va_s24);
  ghost var va_s48, va_c48, va_b48 := va_lemma_block(va_b24, va_s24, va_sM);
  ghost var va_cond_c48, va_s49:va_state := va_lemma_ifElse(va_get_ifCond(va_c48),
    va_get_ifTrue(va_c48), va_get_ifFalse(va_c48), va_s24, va_s48);
  if (va_cond_c48)
  {
    ghost var va_b50 := va_get_block(va_get_ifTrue(va_c48));
    ghost var va_b51, va_s51 := va_lemma_MOV_ToReg(va_b50, va_s49, va_s48, ret,
      va_const_word(TRUE));
    ghost var va_b52, va_s52 := va_lemma_MOV_ToReg(va_b51, va_s51, va_s48, result_slot,
      va_op_word_reg(EDI));
    va_s48 := va_lemma_empty(va_s52, va_s48);
  }
  else
  {
    ghost var va_b53 := va_get_block(va_get_ifFalse(va_c48));
    assert va_get_reg(EDI, va_s49) == eEHCI_USBTD_SlotID_NUMS - 1;  // line 1252 column 9 of file .\dev/usb2/eehci_mem_utils.vad
    assert va_get_reg(ECX, va_s49) == FALSE;  // line 1253 column 9 of file .\dev/usb2/eehci_mem_utils.vad
    ghost var va_b56, va_s56 := va_lemma_MOV_ToReg(va_b53, va_s49, va_s48, ret,
      va_const_word(FALSE));
    ghost var va_b57, va_s57 := va_lemma_MOV_ToReg(va_b56, va_s56, va_s48, result_slot,
      va_const_word(0));
    va_s48 := va_lemma_empty(va_s57, va_s48);
  }
  ghost var va_b58, va_s58 := va_lemma_POP_TwoRegs(va_b48, va_s48, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  va_sM := va_lemma_empty(va_s58, va_sM);
}
//--
//-- eehci_mem_slot_by_id

function method{:opaque} va_code_eehci_mem_slot_by_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_eehci_mem_read_id(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_eehci_mem_read_id(),
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
    ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 10} va_lemma_eehci_mem_slot_by_id(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_eehci_mem_slot_by_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    result_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((ret == TRUE ==>
    eehci_valid_slot_id(result_slot)) && (ret == TRUE ==>
    eehci_mem_get_eehci_id(va_get_globals(va_s0), result_slot) == id)) && (ret == FALSE ==> (forall
    i:word :: eehci_valid_slot_id(i) ==> eehci_mem_get_eehci_id(va_get_globals(va_s0), i) != id))
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
  reveal_va_code_eehci_mem_slot_by_id();
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
  ghost var in_id := va_get_reg(EDI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EAX));
  ghost var va_b17, va_s17 := va_lemma_eehci_mem_read_id(va_b16, va_s16, va_sM);
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
    invariant va_get_reg(EBX, va_sW29) != in_id ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && eehci_valid_slot_id(j) ==> eehci_mem_get_eehci_id(va_get_globals(va_old_s), j) !=
      in_id)
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: eehci_valid_slot_id(j) ==> eehci_mem_get_eehci_id(va_get_globals(va_old_s), j) !=
      in_id)
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) == in_id ||
      va_get_reg(EAX, va_sW29) == eEHCI_INSTANCE_NUM - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) == in_id ==>
      eehci_valid_slot_id(va_get_reg(EAX, va_sW29)) &&
      eehci_mem_get_eehci_id(va_get_globals(va_old_s), va_get_reg(EAX, va_sW29)) == in_id
    invariant va_get_reg(ESP, va_sW29) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW29.wk_mstate.m,
      va_get_reg(ESP, va_sW29))
    invariant va_get_reg(ESI, va_sW29) == va_get_reg(ESI, va_old_s)
    invariant va_get_reg(EBP, va_sW29) == orig_ebp
    invariant va_get_reg(EDI, va_sW29) == in_id
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
    ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s29, va_sW30, va_op_word_reg(EAX));
    ghost var va_b33, va_s33 := va_lemma_eehci_mem_read_id(va_b32, va_s32, va_sW30);
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
    assert va_get_reg(EAX, va_s52) == eEHCI_INSTANCE_NUM - 1;  // line 1414 column 9 of file .\dev/usb2/eehci_mem_utils.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 1415 column 9 of file .\dev/usb2/eehci_mem_utils.vad
    ghost var va_b59, va_s59 := va_lemma_Store(va_b56, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s59, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
    va_s51 := va_lemma_empty(va_s60, va_s51);
  }
  ghost var va_b61, va_s61 := va_lemma_POP_Reg1ToReg6(va_b51, va_s51, va_sM);
  ghost var va_b62, va_s62 := va_lemma_POP_OneReg(va_b61, va_s61, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s62, va_sM);
}
//--
