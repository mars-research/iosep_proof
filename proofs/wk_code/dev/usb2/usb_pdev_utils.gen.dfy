include "../../ins/x86/ins_wrapper.gen.dfy"
include "usb_def.dfy"
include "usb_pdev.s.dfy"
include "usb_pdev_utils.i.dfy"
include "usb_pdev_validstate.i.dfy"
include "..\\..\\drv\\public\\wimpdrv_lemmas.i.dfy"
//-- usbpdev_is_empty_addr

function method{:opaque} va_code_usbpdev_is_empty_addr(tmp_v_high:va_operand_reg,
  tmp_v_low:va_operand_reg, result:va_operand_reg):va_code
{
  va_Block(va_CCons(va_IfElse(va_cmp_eq(va_coerce_reg_to_cmp(tmp_v_low),
    va_const_cmp(WimpUSBPDev_ADDR_EMPTY_LOW)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_coerce_reg_to_cmp(tmp_v_high),
    va_const_cmp(WimpUSBPDev_ADDR_EMPTY_HIGH)), va_Block(va_CCons(va_code_MOV_ToReg(result,
    va_const_word(TRUE)), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(result,
    va_const_word(FALSE)), va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(result,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))
}

lemma va_lemma_usbpdev_is_empty_addr(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  tmp_v_high:va_operand_reg, tmp_v_low:va_operand_reg, result:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_is_empty_addr(tmp_v_high, tmp_v_low, result), va_s0,
    va_sN)
  requires va_is_src_reg(tmp_v_high, va_s0)
  requires va_is_src_reg(tmp_v_low, va_s0)
  requires va_is_dst_reg(result, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires tmp_v_high != OReg(ESP)
  requires tmp_v_high != OReg(EBP)
  requires tmp_v_low != OReg(ESP)
  requires tmp_v_low != OReg(EBP)
  requires result != OReg(ESP)
  requires result != OReg(EBP)
  requires result != tmp_v_high
  requires result != tmp_v_low
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, result) == TRUE <==> va_eval_reg(va_sM, tmp_v_high) ==
    WimpUSBPDev_ADDR_EMPTY_HIGH && va_eval_reg(va_sM, tmp_v_low) == WimpUSBPDev_ADDR_EMPTY_LOW
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(result, va_sM, va_s0)))
{
  reveal_va_code_usbpdev_is_empty_addr();
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
      ghost var va_b8, va_s8 := va_lemma_MOV_ToReg(va_b7, va_s6, va_s5, result,
        va_const_word(TRUE));
      va_s5 := va_lemma_empty(va_s8, va_s5);
    }
    else
    {
      ghost var va_b9 := va_get_block(va_get_ifFalse(va_c5));
      ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s6, va_s5, result,
        va_const_word(FALSE));
      va_s5 := va_lemma_empty(va_s10, va_s5);
    }
    va_s2 := va_lemma_empty(va_s5, va_s2);
  }
  else
  {
    ghost var va_b11 := va_get_block(va_get_ifFalse(va_c2));
    ghost var va_b12, va_s12 := va_lemma_MOV_ToReg(va_b11, va_s3, va_s2, result,
      va_const_word(FALSE));
    va_s2 := va_lemma_empty(va_s12, va_s2);
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- usbpdev_get_id

function method{:opaque} va_code_usbpdev_get_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset)),
    va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_WimpUSBPDev_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EAX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(ESI)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI),
    va_op_reg_reg(EAX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma va_lemma_usbpdev_get_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_get_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var low:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var high:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbpdev_get_addr(va_get_globals(va_s0), slot) == UInt64_FromTwoUInt32s(high, low)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbpdev_get_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDX),
    G_WimpUSBPDev_Info());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_Info_ENTRY_SZ, WimpUSBPDev_Info_ENTRIES,
    WimpUSBPDev_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_Info_ENTRY_SZ);  // line 100 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_Info_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EAX),
    va_op_word_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_ADD(va_b16, va_s16, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset));
  ghost var va_b18, va_s18 := va_lemma_ADD(va_b17, va_s17, va_sM, va_op_word_reg(EAX),
    va_const_word(WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset));
  lemma_DistinctGlobals();
  ghost var va_b20, va_s20 := va_lemma_LDRglobal(va_b18, va_s18, va_sM, va_op_word_reg(ESI),
    G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_Store(va_b20, va_s20, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b22, va_s22 := va_lemma_LDRglobal(va_b21, va_s21, va_sM, va_op_word_reg(ESI),
    G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EAX));
  ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s22, va_sM, va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b23, va_s23, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EAX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
//-- usbpdev_get_pid

function method{:opaque} va_code_usbpdev_get_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_PID_ByteOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_WimpUSBPDev_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbpdev_get_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_get_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var pid:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    usbpdev_get_pid(va_get_globals(va_s0), slot) == WS_PartitionID(pid)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbpdev_get_pid();
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
    G_WimpUSBPDev_Info());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_Info_ENTRY_SZ, WimpUSBPDev_Info_ENTRIES,
    WimpUSBPDev_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_Info_ENTRY_SZ);  // line 177 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_Info_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_PID_ByteOffset));
  lemma_DistinctGlobals();
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbpdev_get_update_flag

function method{:opaque} va_code_usbpdev_get_update_flag():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_WimpUSBPDev_Info(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbpdev_get_update_flag(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_get_update_flag(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var flag:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    usbpdev_get_updateflag(va_get_globals(va_s0), slot) == flag
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbpdev_get_update_flag();
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
    G_WimpUSBPDev_Info());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_Info_ENTRY_SZ, WimpUSBPDev_Info_ENTRIES,
    WimpUSBPDev_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_Info_ENTRY_SZ);  // line 250 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_Info_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset));
  lemma_DistinctGlobals();
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbpdev_set_pid_to_invalid

function method{:opaque} va_code_usbpdev_set_pid_to_invalid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_PID_ByteOffset)),
    va_CCons(va_code_STRglobal(G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbpdev_set_pid_to_invalid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_set_pid_to_invalid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot)
  requires var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); new_pid == PID_INVALID && (forall usbpdev_id:Dev_ID ::
    WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbpdev_get_pid(va_get_globals(va_sM), in_slot) == WS_PartitionID(new_pid)
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + in_slot * WimpUSBPDev_Info_ENTRY_SZ +
    WimpUSBPDev_Info_ENTRY_PID_ByteOffset; is_gvar_valid_addr(G_WimpUSBPDev_Info(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_WimpUSBPDev_Info(), vaddr,
    new_pid)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbpdev_set_pid_to_invalid();
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
    G_WimpUSBPDev_Info());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_Info_ENTRY_SZ, WimpUSBPDev_Info_ENTRIES,
    WimpUSBPDev_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_Info_ENTRY_SZ);  // line 346 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_Info_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_PID_ByteOffset));
  lemma_DistinctGlobals();
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_WimpUSBPDev_Info(),
    tmp_addr1, va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s16), new_globals1,
    slot, WimpUSBPDev_Info_ENTRY_PID_ByteOffset, va_get_reg(ESI, va_s16));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_NewPIDIsInvalid(va_get_globals(va_s16),
    new_globals1, slot, va_get_reg(ESI, va_s16));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingPIDField(va_get_globals(va_s16),
    new_globals1, slot, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingPIDField_NewPIDIsInvalid(va_s16, new_this1,
    slot, va_get_reg(ESI, va_s16));
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_WimpUSBPDev_Info(),
    tmp_addr1, va_get_reg(ESI, va_s16));  // line 371 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingUSBPDevIsNotAssociatedWithAnyUSBTD(va_get_globals(va_old_s),
    va_get_globals(va_s33), slot);
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_OneReg(va_b33, va_s33, va_sM, va_op_reg_reg(ESI));
  ghost var va_b37, va_s37 := va_lemma_POP_TwoRegs(va_b36, va_s36, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- usbpdev_set_pid_to_valid

function method{:opaque} va_code_usbpdev_set_pid_to_valid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_PID_ByteOffset)),
    va_CCons(va_code_STRglobal(G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbpdev_set_pid_to_valid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_set_pid_to_valid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    (usbpdev_valid_slot_id(slot) && !(usbpdev_get_addr_low(va_get_globals(va_s0), slot) ==
    WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(va_get_globals(va_s0), slot) ==
    WimpUSBPDev_ADDR_EMPTY_HIGH)) && (var usbpdev_addr_raw:uint64 :=
    usbpdev_get_addr(va_get_globals(va_s0), slot); usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
    (var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw); usbpdev_addr in
    usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0))))
  requires var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); WS_PartitionID(new_pid) in pids_parse_g_wimp_pids(va_get_globals(va_s0)) &&
    (forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbpdev_get_pid(va_get_globals(va_sM), in_slot) == WS_PartitionID(new_pid)
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + in_slot * WimpUSBPDev_Info_ENTRY_SZ +
    WimpUSBPDev_Info_ENTRY_PID_ByteOffset; is_gvar_valid_addr(G_WimpUSBPDev_Info(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_WimpUSBPDev_Info(), vaddr,
    new_pid)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbpdev_set_pid_to_valid();
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
    G_WimpUSBPDev_Info());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_Info_ENTRY_SZ, WimpUSBPDev_Info_ENTRIES,
    WimpUSBPDev_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_Info_ENTRY_SZ);  // line 476 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_Info_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_PID_ByteOffset));
  lemma_DistinctGlobals();
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_WimpUSBPDev_Info(),
    tmp_addr1, va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s16), new_globals1,
    slot, WimpUSBPDev_Info_ENTRY_PID_ByteOffset, va_get_reg(ESI, va_s16));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_USBPDevAddrIsNotInvalid(va_get_globals(va_s16),
    new_globals1, slot, va_get_reg(ESI, va_s16));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingPIDField(va_get_globals(va_s16),
    new_globals1, slot, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingPIDField_NewPIDIsValid(va_s16, new_this1,
    slot, va_get_reg(ESI, va_s16));
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_WimpUSBPDev_Info(),
    tmp_addr1, va_get_reg(ESI, va_s16));  // line 501 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingUSBPDevIsNotAssociatedWithAnyUSBTD(va_get_globals(va_old_s),
    va_get_globals(va_s33), slot);
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_OneReg(va_b33, va_s33, va_sM, va_op_reg_reg(ESI));
  ghost var va_b37, va_s37 := va_lemma_POP_TwoRegs(va_b36, va_s36, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- usbpdev_set_addr

function method{:opaque} va_code_usbpdev_set_addr():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EAX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset)),
    va_CCons(va_code_STRglobal(G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Slot_UpdateFlag_Updating)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_op_word_reg(ECX)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset)),
    va_CCons(va_code_STRglobal(G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_op_word_reg(ECX)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset)),
    va_CCons(va_code_STRglobal(G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(EAX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_op_word_reg(ECX)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset)),
    va_CCons(va_code_STRglobal(G_WimpUSBPDev_Info(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Slot_UpdateFlag_Complete)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 30} va_lemma_usbpdev_set_addr(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_set_addr(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot)
  requires var new_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var new_addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_id:uint64 := UInt64_FromTwoUInt32s(new_addr_high,
    new_addr_low); usb_is_usbpdev_addr_valid(new_id)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var new_addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var old_pid := usbpdev_get_pid(va_get_globals(va_s0), slot);
    (new_addr_low == WimpUSBPDev_ADDR_EMPTY_LOW && new_addr_high == WimpUSBPDev_ADDR_EMPTY_HIGH ==>
    old_pid == WS_PartitionID(PID_INVALID)) && (old_pid != WS_PartitionID(PID_INVALID) ==> (var
    usbpdev_addr_raw:uint64 := UInt64_FromTwoUInt32s(new_addr_high, new_addr_low); var
    usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw); usbpdev_addr in
    usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0))))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), slot)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var new_addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); forall i:uint32 :: ((usbpdev_valid_slot_id(i) && i != slot) &&
    usbpdev_get_updateflag(va_get_globals(va_s0), i) == WimpUSBPDev_Slot_UpdateFlag_Complete) &&
    !(usbpdev_get_addr_low(va_get_globals(va_s0), i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
    usbpdev_get_addr_high(va_get_globals(va_s0), i) == WimpUSBPDev_ADDR_EMPTY_HIGH) ==>
    usbpdev_get_addr_low(va_get_globals(va_s0), i) != new_addr_low ||
    usbpdev_get_addr_high(va_get_globals(va_s0), i) != new_addr_high
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var new_addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_id:uint64 := UInt64_FromTwoUInt32s(new_addr_high,
    new_addr_low); var old_pid:word := usbpdev_get_pid(va_get_globals(va_s0), in_slot).v;
    (usbpdev_get_addr(va_get_globals(va_sM), in_slot) == new_id &&
    usbpdev_get_updateflag(va_get_globals(va_sM), in_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete)
    && usbpdev_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM), in_slot, new_addr_low,
    new_addr_high, old_pid, WimpUSBPDev_Slot_UpdateFlag_Complete)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_usbpdev_set_addr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b11, va_s11 := va_lemma_PUSH_TwoRegs(va_b10, va_s10, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_PUSH_TwoRegs(va_b11, va_s11, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(ECX));
  ghost var old_globals := va_get_globals(va_s12);
  ghost var va_b14, va_s14 := va_lemma_LDRglobaladdr_ToReg(va_b12, va_s12, va_sM,
    va_op_reg_reg(EDX), G_WimpUSBPDev_Info());
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s16, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s17);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_Info_ENTRY_SZ, WimpUSBPDev_Info_ENTRIES,
    WimpUSBPDev_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_Info_ENTRY_SZ);  // line 631 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b21, va_s21 := va_lemma_MUL_Reg_32BitsResult(va_b17, va_s17, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_Info_ENTRY_SZ));
  ghost var va_b22, va_s22 := va_lemma_MOV_ToReg(va_b21, va_s21, va_sM, va_op_reg_reg(ECX),
    va_op_word_reg(EDI));
  ghost var va_b23, va_s23 := va_lemma_ADD(va_b22, va_s22, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset));
  lemma_DistinctGlobals();
  ghost var tmp_addr1 := va_get_reg(EDX, va_s23) + va_get_reg(EDI, va_s23);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s23), G_WimpUSBPDev_Info(),
    tmp_addr1, WimpUSBPDev_Slot_UpdateFlag_Updating);
  ghost var new_this1 := va_s23.(wk_mstate := va_s23.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s23),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s23),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s23),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s23),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s23),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s23),
    new_globals1);
  Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s23), new_globals1,
    slot, WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset, WimpUSBPDev_Slot_UpdateFlag_Updating);
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_get_globals(va_s23),
    new_globals1, slot, WimpUSBPDev_Slot_UpdateFlag_Updating);
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_get_globals(va_s23),
    new_globals1, slot);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s23,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_s23,
    new_this1, slot);
  assert ins_valid_strglobal_word(va_s23.subjects, va_s23.objects, va_s23.id_mappings,
    va_s23.objs_addrs, va_s23.activate_conds, va_get_globals(va_s23), G_WimpUSBPDev_Info(),
    tmp_addr1, WimpUSBPDev_Slot_UpdateFlag_Updating);  // line 659 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b40, va_s40 := va_lemma_STRglobal(va_b23, va_s23, va_sM, G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_const_word(WimpUSBPDev_Slot_UpdateFlag_Updating));
  ghost var globals1 := va_get_globals(va_s40);
  assert globals1 == global_write_word(old_globals, G_WimpUSBPDev_Info(), tmp_addr1,
    WimpUSBPDev_Slot_UpdateFlag_Updating);  // line 664 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b43, va_s43 := va_lemma_MOV_ToReg(va_b40, va_s40, va_sM, va_op_reg_reg(EDI),
    va_op_word_reg(ECX));
  ghost var va_b44, va_s44 := va_lemma_ADD(va_b43, va_s43, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset));
  lemma_DistinctGlobals();
  ghost var tmp_addr2 := va_get_reg(EDX, va_s44) + va_get_reg(EDI, va_s44);
  ghost var new_globals2 := global_write_word(va_get_globals(va_s44), G_WimpUSBPDev_Info(),
    tmp_addr2, va_get_reg(ESI, va_s44));
  ghost var new_this2 := va_s44.(wk_mstate := va_s44.wk_mstate.(globals := new_globals2));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s44),
    new_globals2);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s44),
    new_globals2);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s44),
    new_globals2);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s44),
    new_globals2);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s44),
    new_globals2);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s44),
    new_globals2);
  Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s44), new_globals2,
    slot, WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset, va_get_reg(ESI, va_s44));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingLowAddrField(va_get_globals(va_s44),
    new_globals2, slot, va_get_reg(ESI, va_s44));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingLowIDField_UnderFlagUpdating(va_get_globals(va_s44),
    new_globals2, slot, va_get_reg(ESI, va_s44));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s44,
    new_this2);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingLowAddrField(va_s44, new_this2, slot,
    va_get_reg(ESI, va_s44));
  assert ins_valid_strglobal_word(va_s44.subjects, va_s44.objects, va_s44.id_mappings,
    va_s44.objs_addrs, va_s44.activate_conds, va_get_globals(va_s44), G_WimpUSBPDev_Info(),
    tmp_addr2, va_get_reg(ESI, va_s44));  // line 689 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b61, va_s61 := va_lemma_STRglobal(va_b44, va_s44, va_sM, G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  ghost var globals2 := va_get_globals(va_s61);
  assert globals2 == global_write_word(globals1, G_WimpUSBPDev_Info(), tmp_addr2, va_get_reg(ESI,
    va_s61));  // line 694 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b64, va_s64 := va_lemma_MOV_ToReg(va_b61, va_s61, va_sM, va_op_reg_reg(EDI),
    va_op_word_reg(ECX));
  ghost var va_b65, va_s65 := va_lemma_ADD(va_b64, va_s64, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset));
  lemma_DistinctGlobals();
  ghost var tmp_addr3 := va_get_reg(EDX, va_s65) + va_get_reg(EDI, va_s65);
  ghost var new_globals3 := global_write_word(va_get_globals(va_s65), G_WimpUSBPDev_Info(),
    tmp_addr3, va_get_reg(EAX, va_s65));
  ghost var new_this3 := va_s65.(wk_mstate := va_s65.wk_mstate.(globals := new_globals3));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s65),
    new_globals3);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s65),
    new_globals3);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s65),
    new_globals3);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s65),
    new_globals3);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s65),
    new_globals3);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s65),
    new_globals3);
  Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s65), new_globals3,
    slot, WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset, va_get_reg(EAX, va_s65));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingHighAddrField(va_get_globals(va_s65),
    new_globals3, slot, va_get_reg(EAX, va_s65));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingHighIDField_UnderFlagUpdating(va_get_globals(va_s65),
    new_globals3, slot, va_get_reg(EAX, va_s65));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s65,
    new_this3);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingHighAddrField(va_s65, new_this3, slot,
    va_get_reg(EAX, va_s65));
  assert ins_valid_strglobal_word(va_s65.subjects, va_s65.objects, va_s65.id_mappings,
    va_s65.objs_addrs, va_s65.activate_conds, va_get_globals(va_s65), G_WimpUSBPDev_Info(),
    tmp_addr3, va_get_reg(EAX, va_s65));  // line 719 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b82, va_s82 := va_lemma_STRglobal(va_b65, va_s65, va_sM, G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(EAX));
  ghost var globals3 := va_get_globals(va_s82);
  assert globals3 == global_write_word(globals2, G_WimpUSBPDev_Info(), tmp_addr3, va_get_reg(EAX,
    va_s82));  // line 724 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  forall i:uint32
    | 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
    ensures p_usbpdev_slot_equal(va_get_globals(va_old_s), va_get_globals(va_s82), i)
  {
    Lemma_p_usbpdev_slot_equal_transitive(va_get_globals(va_old_s), new_globals1, new_globals2, i);
    Lemma_p_usbpdev_slot_equal_transitive(va_get_globals(va_old_s), new_globals2, new_globals3, i);
  }
  Lemma_usbpdev_no_matched_addr_IfOtherUSBPDevSlotsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s82), slot, va_get_reg(ESI, va_s82), va_get_reg(EAX, va_s82));
  ghost var va_b87, va_s87 := va_lemma_MOV_ToReg(va_b82, va_s82, va_sM, va_op_reg_reg(EDI),
    va_op_word_reg(ECX));
  ghost var va_b88, va_s88 := va_lemma_ADD(va_b87, va_s87, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset));
  lemma_DistinctGlobals();
  ghost var tmp_addr4 := va_get_reg(EDX, va_s88) + va_get_reg(EDI, va_s88);
  ghost var new_globals4 := global_write_word(va_get_globals(va_s88), G_WimpUSBPDev_Info(),
    tmp_addr4, WimpUSBPDev_Slot_UpdateFlag_Complete);
  ghost var new_this4 := va_s88.(wk_mstate := va_s88.wk_mstate.(globals := new_globals4));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s88),
    new_globals4);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s88),
    new_globals4);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s88),
    new_globals4);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s88),
    new_globals4);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s88),
    new_globals4);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s88),
    new_globals4);
  Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s88), new_globals4,
    slot, WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset, WimpUSBPDev_Slot_UpdateFlag_Complete);
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField_WriteToUpdateComplete(va_get_globals(va_s88),
    new_globals4, slot, WimpUSBPDev_Slot_UpdateFlag_Complete);
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingUpdateFlagField_WriteToComplete(va_get_globals(va_s88),
    new_globals4, slot);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s88,
    new_this4);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingUpdateFlagField_WriteToUpdateComplete(va_s88,
    new_this4, slot);
  assert ins_valid_strglobal_word(va_s88.subjects, va_s88.objects, va_s88.id_mappings,
    va_s88.objs_addrs, va_s88.activate_conds, va_get_globals(va_s88), G_WimpUSBPDev_Info(),
    tmp_addr4, WimpUSBPDev_Slot_UpdateFlag_Complete);  // line 759 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b105, va_s105 := va_lemma_STRglobal(va_b88, va_s88, va_sM, G_WimpUSBPDev_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_const_word(WimpUSBPDev_Slot_UpdateFlag_Complete));
  assert va_get_globals(va_s105) == global_write_word(globals3, G_WimpUSBPDev_Info(), tmp_addr4,
    WimpUSBPDev_Slot_UpdateFlag_Complete);  // line 763 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  reveal_p_usbpdev_slot_equal();
  forall i:uint32
    | 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
    ensures p_usbpdev_slot_equal(va_get_globals(va_old_s), va_get_globals(va_s105), i)
  {
    Lemma_p_usbpdev_slot_equal_transitive(va_get_globals(va_old_s), globals3,
      va_get_globals(va_s105), i);
  }
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingUSBPDevIsNotAssociatedWithAnyUSBTD(va_get_globals(va_old_s),
    va_get_globals(va_s105), slot);
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s105);
  Lemma_usbpdev_set_id_ProveProperty2(old_globals, globals1, globals2, globals3,
    va_get_globals(va_s105), slot, va_get_reg(ESI, va_s105), va_get_reg(EAX, va_s105));
  ghost var va_b112, va_s112 := va_lemma_POP_TwoRegs(va_b105, va_s105, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(ECX));
  ghost var va_b113, va_s113 := va_lemma_POP_TwoRegs(va_b112, va_s112, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EAX));
  ghost var va_b114, va_s114 := va_lemma_POP_TwoRegs(va_b113, va_s113, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b115, va_s115 := va_lemma_POP_OneReg(va_b114, va_s114, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s115, va_sM);
}
//--
//-- usbpdev_find_slot_by_id

function method{:opaque} va_code_usbpdev_find_slot_by_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbpdev_get_id(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)), va_CNil()))),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CNil()))), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdev_get_id(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(WimpUSBPDev_Info_ENTRIES
    - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CNil())), va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(WimpUSBPDev_Info_ENTRIES - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil()))))))))), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX),
    va_op_cmp_reg(ESI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))
}

lemma{:timeLimitMultiplier 20} va_lemma_usbpdev_find_slot_by_id(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_find_slot_by_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 7 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    result_slot:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((ret == TRUE ==> usbpdev_valid_slot_id(result_slot)) && (ret == TRUE ==>
    usbpdev_get_addr_low(va_get_globals(va_s0), result_slot) == addr_low &&
    usbpdev_get_addr_high(va_get_globals(va_s0), result_slot) == addr_high)) && (ret == FALSE ==>
    (forall i:word :: usbpdev_valid_slot_id(i) ==> !(usbpdev_get_addr_low(va_get_globals(va_s0), i)
    == addr_low && usbpdev_get_addr_high(va_get_globals(va_s0), i) == addr_high)))
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_usbpdev_find_slot_by_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var found_slot;
  ghost var begin_state := va_s10;
  ghost var orig_ebp := va_get_reg(EBP, va_s10);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var in_id_low := va_get_reg(EDI, va_s15);
  ghost var in_id_high := va_get_reg(ESI, va_s15);
  ghost var va_b18, va_s18 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b18, va_s18, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b20, va_s20 := va_lemma_PUSH_VOID(va_b19, va_s19, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sM, va_op_word_reg(EAX));
  ghost var va_b22, va_s22 := va_lemma_usbpdev_get_id(va_b21, va_s21, va_sM);
  ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s26, va_c26, va_b26 := va_lemma_block(va_b25, va_s25, va_sM);
  ghost var va_cond_c26, va_s27:va_state := va_lemma_ifElse(va_get_ifCond(va_c26),
    va_get_ifTrue(va_c26), va_get_ifFalse(va_c26), va_s25, va_s26);
  if (va_cond_c26)
  {
    ghost var va_b28 := va_get_block(va_get_ifTrue(va_c26));
    ghost var va_s29, va_c29, va_b29 := va_lemma_block(va_b28, va_s27, va_s26);
    ghost var va_cond_c29, va_s30:va_state := va_lemma_ifElse(va_get_ifCond(va_c29),
      va_get_ifTrue(va_c29), va_get_ifFalse(va_c29), va_s27, va_s29);
    if (va_cond_c29)
    {
      ghost var va_b31 := va_get_block(va_get_ifTrue(va_c29));
      ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s30, va_s29, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      found_slot := TRUE;
      va_s29 := va_lemma_empty(va_s32, va_s29);
    }
    else
    {
      ghost var va_b34 := va_get_block(va_get_ifFalse(va_c29));
      ghost var va_b35, va_s35 := va_lemma_MOV_ToReg(va_b34, va_s30, va_s29, va_op_reg_reg(EDX),
        va_const_word(TRUE));
      found_slot := FALSE;
      va_s29 := va_lemma_empty(va_s35, va_s29);
    }
    va_s26 := va_lemma_empty(va_s29, va_s26);
  }
  else
  {
    ghost var va_b37 := va_get_block(va_get_ifFalse(va_c26));
    ghost var va_b38, va_s38 := va_lemma_MOV_ToReg(va_b37, va_s27, va_s26, va_op_reg_reg(EDX),
      va_const_word(TRUE));
    found_slot := FALSE;
    va_s26 := va_lemma_empty(va_s38, va_s26);
  }
  ghost var va_s40, va_c40, va_b40 := va_lemma_block(va_b26, va_s26, va_sM);
  ghost var va_n41:int, va_sW41:va_state := va_lemma_while(va_get_whileCond(va_c40),
    va_get_whileBody(va_c40), va_s26, va_s40);
  while (va_n41 > 0)
    invariant va_whileInv(va_get_whileCond(va_c40), va_get_whileBody(va_c40), va_n41, va_sW41,
      va_s40)
    invariant va_get_ok(va_sW41)
    invariant 0 <= va_get_reg(EAX, va_sW41) <= WimpUSBPDev_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW41) == TRUE ==> 0 <= va_get_reg(EAX, va_sW41) <
      WimpUSBPDev_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW41) == TRUE ==> found_slot == FALSE
    invariant !(va_get_reg(EBX, va_sW41) == in_id_low && va_get_reg(ECX, va_sW41) == in_id_high)
      ==> found_slot == FALSE
    invariant found_slot == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX, va_sW41) &&
      usbpdev_valid_slot_id(j) ==> !(usbpdev_get_addr_low(va_get_globals(va_old_s), j) == in_id_low
      && usbpdev_get_addr_high(va_get_globals(va_old_s), j) == in_id_high))
    invariant va_get_reg(EDX, va_sW41) != TRUE && found_slot == FALSE ==> (forall j:uint32 ::
      usbpdev_valid_slot_id(j) ==> !(usbpdev_get_addr_low(va_get_globals(va_old_s), j) == in_id_low
      && usbpdev_get_addr_high(va_get_globals(va_old_s), j) == in_id_high))
    invariant va_get_reg(EDX, va_sW41) != TRUE ==> (va_get_reg(EBX, va_sW41) == in_id_low &&
      va_get_reg(ECX, va_sW41) == in_id_high) || va_get_reg(EAX, va_sW41) ==
      WimpUSBPDev_Info_ENTRIES - 1
    invariant va_get_reg(EDX, va_sW41) != TRUE && (va_get_reg(EBX, va_sW41) == in_id_low &&
      va_get_reg(ECX, va_sW41) == in_id_high) ==> (usbpdev_valid_slot_id(va_get_reg(EAX, va_sW41))
      && usbpdev_get_addr_low(va_get_globals(va_old_s), va_get_reg(EAX, va_sW41)) == in_id_low) &&
      usbpdev_get_addr_high(va_get_globals(va_old_s), va_get_reg(EAX, va_sW41)) == in_id_high
    invariant va_get_reg(ESP, va_sW41) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW41.wk_mstate.m,
      va_get_reg(ESP, va_sW41))
    invariant va_get_reg(EBP, va_sW41) == orig_ebp
    invariant va_get_reg(EDI, va_sW41) == in_id_low
    invariant va_get_reg(ESI, va_sW41) == in_id_high
    invariant va_get_globals(va_sW41) == va_get_globals(va_old_s)
    invariant state_equal_except_mstate(va_old_s, va_sW41)
    invariant va_state_eq(va_sW41, va_update_reg(EDI, va_sW41, va_update_reg(ESI, va_sW41,
      va_update_reg(EDX, va_sW41, va_update_reg(ECX, va_sW41, va_update_reg(EBX, va_sW41,
      va_update_reg(EAX, va_sW41, va_update_mem(va_sW41, va_update_reg(EBP, va_sW41,
      va_update_reg(ESP, va_sW41, va_update_ok(va_sW41, va_s0)))))))))))
    decreases WimpUSBPDev_Info_ENTRIES - va_get_reg(EAX, va_sW41), va_get_reg(EDX, va_sW41)
  {
    ghost var va_s41:va_state, va_sW42:va_state := va_lemma_whileTrue(va_get_whileCond(va_c40),
      va_get_whileBody(va_c40), va_n41, va_sW41, va_s40);
    ghost var va_b43 := va_get_block(va_get_whileBody(va_c40));
    ghost var va_b44, va_s44 := va_lemma_PUSH_VOID(va_b43, va_s41, va_sW42, 1 * ARCH_WORD_BYTES);
    ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_sW42, va_op_word_reg(EAX));
    ghost var va_b46, va_s46 := va_lemma_usbpdev_get_id(va_b45, va_s45, va_sW42);
    ghost var va_b47, va_s47 := va_lemma_Load(va_b46, va_s46, va_sW42, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b48, va_s48 := va_lemma_Load(va_b47, va_s47, va_sW42, va_op_word_reg(ECX),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_sW42, 2 * ARCH_WORD_BYTES);
    ghost var va_s50, va_c50, va_b50 := va_lemma_block(va_b49, va_s49, va_sW42);
    ghost var va_cond_c50, va_s51:va_state := va_lemma_ifElse(va_get_ifCond(va_c50),
      va_get_ifTrue(va_c50), va_get_ifFalse(va_c50), va_s49, va_s50);
    if (va_cond_c50)
    {
      ghost var va_b52 := va_get_block(va_get_ifTrue(va_c50));
      ghost var va_s53, va_c53, va_b53 := va_lemma_block(va_b52, va_s51, va_s50);
      ghost var va_cond_c53, va_s54:va_state := va_lemma_ifElse(va_get_ifCond(va_c53),
        va_get_ifTrue(va_c53), va_get_ifFalse(va_c53), va_s51, va_s53);
      if (va_cond_c53)
      {
        ghost var va_b55 := va_get_block(va_get_ifTrue(va_c53));
        ghost var va_b56, va_s56 := va_lemma_MOV_ToReg(va_b55, va_s54, va_s53, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        found_slot := TRUE;
        va_s53 := va_lemma_empty(va_s56, va_s53);
      }
      else
      {
        ghost var va_b58 := va_get_block(va_get_ifFalse(va_c53));
        ghost var va_s59, va_c59, va_b59 := va_lemma_block(va_b58, va_s54, va_s53);
        ghost var va_cond_c59, va_s60:va_state := va_lemma_ifElse(va_get_ifCond(va_c59),
          va_get_ifTrue(va_c59), va_get_ifFalse(va_c59), va_s54, va_s59);
        if (va_cond_c59)
        {
          ghost var va_b61 := va_get_block(va_get_ifTrue(va_c59));
          ghost var va_b62, va_s62 := va_lemma_MOV_ToReg(va_b61, va_s60, va_s59,
            va_op_reg_reg(EDX), va_const_word(FALSE));
          found_slot := FALSE;
          va_s59 := va_lemma_empty(va_s62, va_s59);
        }
        else
        {
          ghost var va_b64 := va_get_block(va_get_ifFalse(va_c59));
          ghost var va_b65, va_s65 := va_lemma_ADD(va_b64, va_s60, va_s59, va_op_word_reg(EAX),
            va_const_word(1));
          ghost var va_b66, va_s66 := va_lemma_MOV_ToReg(va_b65, va_s65, va_s59,
            va_op_reg_reg(EDX), va_const_word(TRUE));
          found_slot := FALSE;
          va_s59 := va_lemma_empty(va_s66, va_s59);
        }
        va_s53 := va_lemma_empty(va_s59, va_s53);
      }
      va_s50 := va_lemma_empty(va_s53, va_s50);
    }
    else
    {
      ghost var va_b68 := va_get_block(va_get_ifFalse(va_c50));
      ghost var va_s69, va_c69, va_b69 := va_lemma_block(va_b68, va_s51, va_s50);
      ghost var va_cond_c69, va_s70:va_state := va_lemma_ifElse(va_get_ifCond(va_c69),
        va_get_ifTrue(va_c69), va_get_ifFalse(va_c69), va_s51, va_s69);
      if (va_cond_c69)
      {
        ghost var va_b71 := va_get_block(va_get_ifTrue(va_c69));
        ghost var va_b72, va_s72 := va_lemma_MOV_ToReg(va_b71, va_s70, va_s69, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        found_slot := FALSE;
        va_s69 := va_lemma_empty(va_s72, va_s69);
      }
      else
      {
        ghost var va_b74 := va_get_block(va_get_ifFalse(va_c69));
        ghost var va_b75, va_s75 := va_lemma_ADD(va_b74, va_s70, va_s69, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b76, va_s76 := va_lemma_MOV_ToReg(va_b75, va_s75, va_s69, va_op_reg_reg(EDX),
          va_const_word(TRUE));
        found_slot := FALSE;
        va_s69 := va_lemma_empty(va_s76, va_s69);
      }
      va_s50 := va_lemma_empty(va_s69, va_s50);
    }
    va_sW42 := va_lemma_empty(va_s50, va_sW42);
    va_sW41 := va_sW42;
    va_n41 := va_n41 - 1;
  }
  va_s40 := va_lemma_whileFalse(va_get_whileCond(va_c40), va_get_whileBody(va_c40), va_sW41,
    va_s40);
  ghost var va_s78, va_c78, va_b78 := va_lemma_block(va_b40, va_s40, va_sM);
  ghost var va_cond_c78, va_s79:va_state := va_lemma_ifElse(va_get_ifCond(va_c78),
    va_get_ifTrue(va_c78), va_get_ifFalse(va_c78), va_s40, va_s78);
  if (va_cond_c78)
  {
    ghost var va_b80 := va_get_block(va_get_ifTrue(va_c78));
    ghost var va_s81, va_c81, va_b81 := va_lemma_block(va_b80, va_s79, va_s78);
    ghost var va_cond_c81, va_s82:va_state := va_lemma_ifElse(va_get_ifCond(va_c81),
      va_get_ifTrue(va_c81), va_get_ifFalse(va_c81), va_s79, va_s81);
    if (va_cond_c81)
    {
      ghost var va_b83 := va_get_block(va_get_ifTrue(va_c81));
      ghost var va_b84, va_s84 := va_lemma_Store(va_b83, va_s82, va_s81, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b85, va_s85 := va_lemma_Store(va_b84, va_s84, va_s81, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(EAX));
      va_s81 := va_lemma_empty(va_s85, va_s81);
    }
    else
    {
      ghost var va_b86 := va_get_block(va_get_ifFalse(va_c81));
      assert va_get_reg(EAX, va_s82) == WimpUSBPDev_Info_ENTRIES - 1;  // line 976 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      assert found_slot == FALSE;  // line 977 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      ghost var va_b89, va_s89 := va_lemma_Store(va_b86, va_s82, va_s81, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b90, va_s90 := va_lemma_Store(va_b89, va_s89, va_s81, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
      va_s81 := va_lemma_empty(va_s90, va_s81);
    }
    va_s78 := va_lemma_empty(va_s81, va_s78);
  }
  else
  {
    ghost var va_b91 := va_get_block(va_get_ifFalse(va_c78));
    assert va_get_reg(EAX, va_s79) == WimpUSBPDev_Info_ENTRIES - 1;  // line 985 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    assert found_slot == FALSE;  // line 986 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    ghost var va_b94, va_s94 := va_lemma_Store(va_b91, va_s79, va_s78, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b95, va_s95 := va_lemma_Store(va_b94, va_s94, va_s78, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
    va_s78 := va_lemma_empty(va_s95, va_s78);
  }
  ghost var va_b96, va_s96 := va_lemma_POP_Reg1ToReg6(va_b78, va_s78, va_sM);
  ghost var va_b97, va_s97 := va_lemma_POP_OneReg(va_b96, va_s96, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s97, va_sM);
}
//--
//-- usbpdev_check_slot_id

function method{:opaque} va_code_usbpdev_check_slot_id(slot_id:va_operand_reg,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_IfElse(va_cmp_ge(va_coerce_reg_to_cmp(slot_id), va_const_cmp(0)),
    va_Block(va_CCons(va_IfElse(va_cmp_lt(va_coerce_reg_to_cmp(slot_id),
    va_const_cmp(WimpUSBPDev_Info_ENTRIES)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(TRUE)), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))
}

lemma va_lemma_usbpdev_check_slot_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot_id:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_check_slot_id(slot_id, ret), va_s0, va_sN)
  requires va_is_src_reg(slot_id, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires slot_id != ret
  requires ret == Reg1
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> usbpdev_valid_slot_id(va_eval_reg(va_sM, slot_id))
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_usbpdev_check_slot_id();
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
//-- usbpdev_check_dev_addr

function method{:opaque} va_code_usbpdev_check_dev_addr(addr_high:va_operand_reg,
  addr_low:va_operand_reg, ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_MOV_ToReg(ret, va_coerce_reg_to_word(addr_high)),
    va_CCons(va_code_SHR(va_coerce_reg_to_word(ret),
    va_const_word(USBPDevAddr_Reserved1_RightShiftBits)),
    va_CCons(va_code_AND(va_coerce_reg_to_word(ret), va_const_word(USBPDevAddr_Reserved1_MASK)),
    va_CCons(va_IfElse(va_cmp_eq(va_coerce_reg_to_cmp(ret),
    va_const_cmp(USBPDevAddr_Reserved1_Val)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_coerce_reg_to_word(addr_low)), va_CCons(va_code_SHR(va_coerce_reg_to_word(ret),
    va_const_word(USBPDevAddr_Reserved2_RightShiftBits)),
    va_CCons(va_code_AND(va_coerce_reg_to_word(ret), va_const_word(USBPDevAddr_Reserved2_MASK)),
    va_CCons(va_IfElse(va_cmp_eq(va_coerce_reg_to_cmp(ret),
    va_const_cmp(USBPDevAddr_Reserved2_Val)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_coerce_reg_to_word(addr_low)), va_CCons(va_code_SHR(va_coerce_reg_to_word(ret),
    va_const_word(USBPDevAddr_HUB_Addr_RightShiftBits)),
    va_CCons(va_code_AND(va_coerce_reg_to_word(ret), va_const_word(USB_ADDR_MASK)),
    va_CCons(va_IfElse(va_cmp_ne(va_coerce_reg_to_cmp(ret), va_const_cmp(0)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_coerce_reg_to_word(addr_low)),
    va_CCons(va_code_AND(va_coerce_reg_to_word(ret), va_const_word(USB_ADDR_MASK)),
    va_CCons(va_IfElse(va_cmp_ne(va_coerce_reg_to_cmp(ret), va_const_cmp(0)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(TRUE)), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil())))),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil()))))),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil()))))),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil())))))
}

lemma va_lemma_usbpdev_check_dev_addr(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  addr_high:va_operand_reg, addr_low:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_check_dev_addr(addr_high, addr_low, ret), va_s0, va_sN)
  requires va_is_src_reg(addr_high, va_s0)
  requires va_is_src_reg(addr_low, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires addr_high == Reg3
  requires addr_low == Reg2
  requires ret == Reg1
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var usbpdev_id:uint64 := UInt64_FromTwoUInt32s(va_eval_reg(va_sM, addr_high),
    va_eval_reg(va_sM, addr_low)); va_eval_reg(va_sM, ret) == TRUE ==>
    usb_is_usbpdev_addr_valid(usbpdev_id)
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_usbpdev_check_dev_addr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_usb_is_usbpdev_addr_valid();
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b1, va_s0, va_sM, ret,
    va_coerce_reg_to_word(addr_high));
  ghost var va_b4, va_s4 := va_lemma_SHR(va_b3, va_s3, va_sM, va_coerce_reg_to_word(ret),
    va_const_word(USBPDevAddr_Reserved1_RightShiftBits));
  ghost var va_b5, va_s5 := va_lemma_AND(va_b4, va_s4, va_sM, va_coerce_reg_to_word(ret),
    va_const_word(USBPDevAddr_Reserved1_MASK));
  ghost var va_s6, va_c6, va_b6 := va_lemma_block(va_b5, va_s5, va_sM);
  ghost var va_cond_c6, va_s7:va_state := va_lemma_ifElse(va_get_ifCond(va_c6),
    va_get_ifTrue(va_c6), va_get_ifFalse(va_c6), va_s5, va_s6);
  if (va_cond_c6)
  {
    ghost var va_b8 := va_get_block(va_get_ifTrue(va_c6));
    ghost var va_b9, va_s9 := va_lemma_MOV_ToReg(va_b8, va_s7, va_s6, ret,
      va_coerce_reg_to_word(addr_low));
    ghost var va_b10, va_s10 := va_lemma_SHR(va_b9, va_s9, va_s6, va_coerce_reg_to_word(ret),
      va_const_word(USBPDevAddr_Reserved2_RightShiftBits));
    ghost var va_b11, va_s11 := va_lemma_AND(va_b10, va_s10, va_s6, va_coerce_reg_to_word(ret),
      va_const_word(USBPDevAddr_Reserved2_MASK));
    ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s11, va_s6);
    ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
      va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s11, va_s12);
    if (va_cond_c12)
    {
      ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
      ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s13, va_s12, ret,
        va_coerce_reg_to_word(addr_low));
      ghost var va_b16, va_s16 := va_lemma_SHR(va_b15, va_s15, va_s12, va_coerce_reg_to_word(ret),
        va_const_word(USBPDevAddr_HUB_Addr_RightShiftBits));
      ghost var va_b17, va_s17 := va_lemma_AND(va_b16, va_s16, va_s12, va_coerce_reg_to_word(ret),
        va_const_word(USB_ADDR_MASK));
      ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s12);
      ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
        va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
      if (va_cond_c18)
      {
        ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
        ghost var va_b21, va_s21 := va_lemma_MOV_ToReg(va_b20, va_s19, va_s18, ret,
          va_coerce_reg_to_word(addr_low));
        ghost var va_b22, va_s22 := va_lemma_AND(va_b21, va_s21, va_s18,
          va_coerce_reg_to_word(ret), va_const_word(USB_ADDR_MASK));
        ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_s18);
        ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
          va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
        if (va_cond_c23)
        {
          ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
          ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s24, va_s23, ret,
            va_const_word(TRUE));
          va_s23 := va_lemma_empty(va_s26, va_s23);
        }
        else
        {
          ghost var va_b27 := va_get_block(va_get_ifFalse(va_c23));
          ghost var va_b28, va_s28 := va_lemma_MOV_ToReg(va_b27, va_s24, va_s23, ret,
            va_const_word(FALSE));
          va_s23 := va_lemma_empty(va_s28, va_s23);
        }
        va_s18 := va_lemma_empty(va_s23, va_s18);
      }
      else
      {
        ghost var va_b29 := va_get_block(va_get_ifFalse(va_c18));
        ghost var va_b30, va_s30 := va_lemma_MOV_ToReg(va_b29, va_s19, va_s18, ret,
          va_const_word(FALSE));
        va_s18 := va_lemma_empty(va_s30, va_s18);
      }
      va_s12 := va_lemma_empty(va_s18, va_s12);
    }
    else
    {
      ghost var va_b31 := va_get_block(va_get_ifFalse(va_c12));
      ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s13, va_s12, ret,
        va_const_word(FALSE));
      va_s12 := va_lemma_empty(va_s32, va_s12);
    }
    va_s6 := va_lemma_empty(va_s12, va_s6);
  }
  else
  {
    ghost var va_b33 := va_get_block(va_get_ifFalse(va_c6));
    ghost var va_b34, va_s34 := va_lemma_MOV_ToReg(va_b33, va_s7, va_s6, ret, va_const_word(FALSE));
    va_s6 := va_lemma_empty(va_s34, va_s6);
  }
  va_sM := va_lemma_empty(va_s6, va_sM);
}
//--
//-- usbpdev_find_slot_in_partition

function method{:opaque} va_code_usbpdev_find_slot_in_partition():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdev_get_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdev_get_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(WimpUSBPDev_Info_ENTRIES
    - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))))),
    va_CNil()))), va_CNil()))))))), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_usbpdev_find_slot_in_partition(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_find_slot_in_partition(), va_s0, va_sN)
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
    usbpdev_valid_slot_id(result_slot)) && (ret == TRUE ==> usbpdev_get_pid(va_get_globals(va_s0),
    result_slot) == WS_PartitionID(pid))) && (ret == FALSE ==> (forall i:word ::
    usbpdev_valid_slot_id(i) ==> usbpdev_get_pid(va_get_globals(va_s0), i) != WS_PartitionID(pid)))
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
  reveal_va_code_usbpdev_find_slot_in_partition();
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
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EAX));
  ghost var va_b17, va_s17 := va_lemma_usbpdev_get_pid(va_b16, va_s16, va_sM);
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
    invariant 0 <= va_get_reg(EAX, va_sW29) <= WimpUSBPDev_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) <
      WimpUSBPDev_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) != in_pid ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && usbpdev_valid_slot_id(j) ==> usbpdev_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: usbpdev_valid_slot_id(j) ==> usbpdev_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) == in_pid ||
      va_get_reg(EAX, va_sW29) == WimpUSBPDev_Info_ENTRIES - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) == in_pid ==>
      usbpdev_valid_slot_id(va_get_reg(EAX, va_sW29)) && usbpdev_get_pid(va_get_globals(va_old_s),
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
    decreases WimpUSBPDev_Info_ENTRIES - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s29, va_sW30, va_op_word_reg(EAX));
    ghost var va_b33, va_s33 := va_lemma_usbpdev_get_pid(va_b32, va_s32, va_sW30);
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
    assert va_get_reg(EAX, va_s52) == WimpUSBPDev_Info_ENTRIES - 1;  // line 1252 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 1253 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    ghost var va_b59, va_s59 := va_lemma_Store(va_b56, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s59, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
    va_s51 := va_lemma_empty(va_s60, va_s51);
  }
  ghost var va_b61, va_s61 := va_lemma_POP_Reg1ToReg6(va_b51, va_s51, va_sM);
  ghost var va_b62, va_s62 := va_lemma_POP_OneReg(va_b61, va_s61, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s62, va_sM);
}
//--
//-- usbpdev_find_slot_not_in_partition

function method{:opaque} va_code_usbpdev_find_slot_not_in_partition():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdev_get_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdev_get_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(WimpUSBPDev_Info_ENTRIES
    - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))))),
    va_CNil()))), va_CNil()))))))), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_usbpdev_find_slot_not_in_partition(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdev_find_slot_not_in_partition(), va_s0, va_sN)
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
    usbpdev_valid_slot_id(result_slot)) && (ret == TRUE ==> usbpdev_get_pid(va_get_globals(va_s0),
    result_slot) != WS_PartitionID(pid))) && (ret == FALSE ==> (forall i:word ::
    usbpdev_valid_slot_id(i) ==> usbpdev_get_pid(va_get_globals(va_s0), i) == WS_PartitionID(pid)))
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
  reveal_va_code_usbpdev_find_slot_not_in_partition();
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
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EAX));
  ghost var va_b17, va_s17 := va_lemma_usbpdev_get_pid(va_b16, va_s16, va_sM);
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
    invariant 0 <= va_get_reg(EAX, va_sW29) <= WimpUSBPDev_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) <
      WimpUSBPDev_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) == in_pid ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && usbpdev_valid_slot_id(j) ==> usbpdev_get_pid(va_get_globals(va_old_s), j) ==
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: usbpdev_valid_slot_id(j) ==> usbpdev_get_pid(va_get_globals(va_old_s), j) ==
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) != in_pid ||
      va_get_reg(EAX, va_sW29) == WimpUSBPDev_Info_ENTRIES - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) != in_pid ==>
      usbpdev_valid_slot_id(va_get_reg(EAX, va_sW29)) && usbpdev_get_pid(va_get_globals(va_old_s),
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
    decreases WimpUSBPDev_Info_ENTRIES - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s29, va_sW30, va_op_word_reg(EAX));
    ghost var va_b33, va_s33 := va_lemma_usbpdev_get_pid(va_b32, va_s32, va_sW30);
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
    assert va_get_reg(EBP, va_s52) == orig_ebp;  // line 1411 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    ghost var va_b55, va_s55 := va_lemma_Store(va_b53, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s55, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    va_s51 := va_lemma_empty(va_s56, va_s51);
  }
  else
  {
    ghost var va_b57 := va_get_block(va_get_ifFalse(va_c51));
    assert va_get_reg(EBP, va_s52) == orig_ebp;  // line 1417 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    assert va_get_reg(EAX, va_s52) == WimpUSBPDev_Info_ENTRIES - 1;  // line 1418 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 1419 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    ghost var va_b61, va_s61 := va_lemma_Store(va_b57, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s61, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
    va_s51 := va_lemma_empty(va_s62, va_s51);
  }
  ghost var va_b63, va_s63 := va_lemma_POP_Reg1ToReg6(va_b51, va_s51, va_sM);
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b63, va_s63, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s64);
  va_sM := va_lemma_empty(va_s64, va_sM);
}
//--
//-- usbpdevlist_get_id

function method{:opaque} va_code_usbpdevlist_get_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpUSBPDev_DevList()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpUSBPDev_DevList_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_DevList_ENTRY_LowAddr_ByteOffset)),
    va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(WimpUSBPDev_DevList_ENTRY_HighAddr_ByteOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_WimpUSBPDev_DevList(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_WimpUSBPDev_DevList(),
    va_op_reg_reg(EDX), va_op_word_reg(EAX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(ESI)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI),
    va_op_reg_reg(EAX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma va_lemma_usbpdevlist_get_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdevlist_get_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdevlist_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var low:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var high:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbpdevlist_get_addr(va_get_globals(va_s0), slot) == UInt64_FromTwoUInt32s(high, low)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbpdevlist_get_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDX),
    G_WimpUSBPDev_DevList());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, WimpUSBPDev_DevList_ENTRY_SZ, WimpUSBPDev_DevList_ENTRIES,
    WimpUSBPDev_DevList_ENTRY_SZ);
  assert isUInt32(slot * WimpUSBPDev_DevList_ENTRY_SZ);  // line 1495 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpUSBPDev_DevList_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EAX),
    va_op_word_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_ADD(va_b16, va_s16, va_sM, va_op_word_reg(EDI),
    va_const_word(WimpUSBPDev_DevList_ENTRY_LowAddr_ByteOffset));
  ghost var va_b18, va_s18 := va_lemma_ADD(va_b17, va_s17, va_sM, va_op_word_reg(EAX),
    va_const_word(WimpUSBPDev_DevList_ENTRY_HighAddr_ByteOffset));
  lemma_DistinctGlobals();
  ghost var va_b20, va_s20 := va_lemma_LDRglobal(va_b18, va_s18, va_sM, va_op_word_reg(ESI),
    G_WimpUSBPDev_DevList(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_Store(va_b20, va_s20, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b22, va_s22 := va_lemma_LDRglobal(va_b21, va_s21, va_sM, va_op_word_reg(ESI),
    G_WimpUSBPDev_DevList(), va_op_reg_reg(EDX), va_op_word_reg(EAX));
  ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s22, va_sM, va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b23, va_s23, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EAX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
//-- usbpdevlist_find_slot_by_id

function method{:opaque} va_code_usbpdevlist_find_slot_by_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbpdevlist_get_id(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)), va_CNil()))),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CNil()))), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdevlist_get_id(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(WimpUSBPDev_DevList_ENTRIES - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(WimpUSBPDev_DevList_ENTRIES - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil()))))))))), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX),
    va_op_cmp_reg(ESI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))
}

lemma{:timeLimitMultiplier 20} va_lemma_usbpdevlist_find_slot_by_id(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdevlist_find_slot_by_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 7 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    result_slot:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((ret == TRUE ==> usbpdevlist_valid_slot_id(result_slot)) && (ret == TRUE ==>
    usbpdevlist_get_addr_low(va_get_globals(va_s0), result_slot) == addr_low &&
    usbpdevlist_get_addr_high(va_get_globals(va_s0), result_slot) == addr_high)) && (ret == FALSE
    ==> (forall i:word :: usbpdevlist_valid_slot_id(i) ==>
    !(usbpdevlist_get_addr_low(va_get_globals(va_s0), i) == addr_low &&
    usbpdevlist_get_addr_high(va_get_globals(va_s0), i) == addr_high)))
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_usbpdevlist_find_slot_by_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var found_slot;
  ghost var begin_state := va_s10;
  ghost var orig_ebp := va_get_reg(EBP, va_s10);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var in_id_low := va_get_reg(EDI, va_s15);
  ghost var in_id_high := va_get_reg(ESI, va_s15);
  ghost var va_b18, va_s18 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b18, va_s18, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b20, va_s20 := va_lemma_PUSH_VOID(va_b19, va_s19, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sM, va_op_word_reg(EAX));
  ghost var va_b22, va_s22 := va_lemma_usbpdevlist_get_id(va_b21, va_s21, va_sM);
  ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s26, va_c26, va_b26 := va_lemma_block(va_b25, va_s25, va_sM);
  ghost var va_cond_c26, va_s27:va_state := va_lemma_ifElse(va_get_ifCond(va_c26),
    va_get_ifTrue(va_c26), va_get_ifFalse(va_c26), va_s25, va_s26);
  if (va_cond_c26)
  {
    ghost var va_b28 := va_get_block(va_get_ifTrue(va_c26));
    ghost var va_s29, va_c29, va_b29 := va_lemma_block(va_b28, va_s27, va_s26);
    ghost var va_cond_c29, va_s30:va_state := va_lemma_ifElse(va_get_ifCond(va_c29),
      va_get_ifTrue(va_c29), va_get_ifFalse(va_c29), va_s27, va_s29);
    if (va_cond_c29)
    {
      ghost var va_b31 := va_get_block(va_get_ifTrue(va_c29));
      ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s30, va_s29, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      found_slot := TRUE;
      va_s29 := va_lemma_empty(va_s32, va_s29);
    }
    else
    {
      ghost var va_b34 := va_get_block(va_get_ifFalse(va_c29));
      ghost var va_b35, va_s35 := va_lemma_MOV_ToReg(va_b34, va_s30, va_s29, va_op_reg_reg(EDX),
        va_const_word(TRUE));
      found_slot := FALSE;
      va_s29 := va_lemma_empty(va_s35, va_s29);
    }
    va_s26 := va_lemma_empty(va_s29, va_s26);
  }
  else
  {
    ghost var va_b37 := va_get_block(va_get_ifFalse(va_c26));
    ghost var va_b38, va_s38 := va_lemma_MOV_ToReg(va_b37, va_s27, va_s26, va_op_reg_reg(EDX),
      va_const_word(TRUE));
    found_slot := FALSE;
    va_s26 := va_lemma_empty(va_s38, va_s26);
  }
  ghost var va_s40, va_c40, va_b40 := va_lemma_block(va_b26, va_s26, va_sM);
  ghost var va_n41:int, va_sW41:va_state := va_lemma_while(va_get_whileCond(va_c40),
    va_get_whileBody(va_c40), va_s26, va_s40);
  while (va_n41 > 0)
    invariant va_whileInv(va_get_whileCond(va_c40), va_get_whileBody(va_c40), va_n41, va_sW41,
      va_s40)
    invariant va_get_ok(va_sW41)
    invariant 0 <= va_get_reg(EAX, va_sW41) <= WimpUSBPDev_DevList_ENTRIES
    invariant va_get_reg(EDX, va_sW41) == TRUE ==> 0 <= va_get_reg(EAX, va_sW41) <
      WimpUSBPDev_DevList_ENTRIES
    invariant va_get_reg(EDX, va_sW41) == TRUE ==> found_slot == FALSE
    invariant !(va_get_reg(EBX, va_sW41) == in_id_low && va_get_reg(ECX, va_sW41) == in_id_high)
      ==> found_slot == FALSE
    invariant found_slot == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX, va_sW41) &&
      usbpdevlist_valid_slot_id(j) ==> !(usbpdevlist_get_addr_low(va_get_globals(va_old_s), j) ==
      in_id_low && usbpdevlist_get_addr_high(va_get_globals(va_old_s), j) == in_id_high))
    invariant va_get_reg(EDX, va_sW41) != TRUE && found_slot == FALSE ==> (forall j:uint32 ::
      usbpdevlist_valid_slot_id(j) ==> !(usbpdevlist_get_addr_low(va_get_globals(va_old_s), j) ==
      in_id_low && usbpdevlist_get_addr_high(va_get_globals(va_old_s), j) == in_id_high))
    invariant va_get_reg(EDX, va_sW41) != TRUE ==> (va_get_reg(EBX, va_sW41) == in_id_low &&
      va_get_reg(ECX, va_sW41) == in_id_high) || va_get_reg(EAX, va_sW41) ==
      WimpUSBPDev_DevList_ENTRIES - 1
    invariant va_get_reg(EDX, va_sW41) != TRUE && (va_get_reg(EBX, va_sW41) == in_id_low &&
      va_get_reg(ECX, va_sW41) == in_id_high) ==> (usbpdevlist_valid_slot_id(va_get_reg(EAX,
      va_sW41)) && usbpdevlist_get_addr_low(va_get_globals(va_old_s), va_get_reg(EAX, va_sW41)) ==
      in_id_low) && usbpdevlist_get_addr_high(va_get_globals(va_old_s), va_get_reg(EAX, va_sW41))
      == in_id_high
    invariant va_get_reg(ESP, va_sW41) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW41.wk_mstate.m,
      va_get_reg(ESP, va_sW41))
    invariant va_get_reg(EBP, va_sW41) == orig_ebp
    invariant va_get_reg(EDI, va_sW41) == in_id_low
    invariant va_get_reg(ESI, va_sW41) == in_id_high
    invariant va_get_globals(va_sW41) == va_get_globals(va_old_s)
    invariant state_equal_except_mstate(va_old_s, va_sW41)
    invariant va_state_eq(va_sW41, va_update_reg(EDI, va_sW41, va_update_reg(ESI, va_sW41,
      va_update_reg(EDX, va_sW41, va_update_reg(ECX, va_sW41, va_update_reg(EBX, va_sW41,
      va_update_reg(EAX, va_sW41, va_update_mem(va_sW41, va_update_reg(EBP, va_sW41,
      va_update_reg(ESP, va_sW41, va_update_ok(va_sW41, va_s0)))))))))))
    decreases WimpUSBPDev_DevList_ENTRIES - va_get_reg(EAX, va_sW41), va_get_reg(EDX, va_sW41)
  {
    ghost var va_s41:va_state, va_sW42:va_state := va_lemma_whileTrue(va_get_whileCond(va_c40),
      va_get_whileBody(va_c40), va_n41, va_sW41, va_s40);
    ghost var va_b43 := va_get_block(va_get_whileBody(va_c40));
    ghost var va_b44, va_s44 := va_lemma_PUSH_VOID(va_b43, va_s41, va_sW42, 1 * ARCH_WORD_BYTES);
    ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_sW42, va_op_word_reg(EAX));
    ghost var va_b46, va_s46 := va_lemma_usbpdevlist_get_id(va_b45, va_s45, va_sW42);
    ghost var va_b47, va_s47 := va_lemma_Load(va_b46, va_s46, va_sW42, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b48, va_s48 := va_lemma_Load(va_b47, va_s47, va_sW42, va_op_word_reg(ECX),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_sW42, 2 * ARCH_WORD_BYTES);
    ghost var va_s50, va_c50, va_b50 := va_lemma_block(va_b49, va_s49, va_sW42);
    ghost var va_cond_c50, va_s51:va_state := va_lemma_ifElse(va_get_ifCond(va_c50),
      va_get_ifTrue(va_c50), va_get_ifFalse(va_c50), va_s49, va_s50);
    if (va_cond_c50)
    {
      ghost var va_b52 := va_get_block(va_get_ifTrue(va_c50));
      ghost var va_s53, va_c53, va_b53 := va_lemma_block(va_b52, va_s51, va_s50);
      ghost var va_cond_c53, va_s54:va_state := va_lemma_ifElse(va_get_ifCond(va_c53),
        va_get_ifTrue(va_c53), va_get_ifFalse(va_c53), va_s51, va_s53);
      if (va_cond_c53)
      {
        ghost var va_b55 := va_get_block(va_get_ifTrue(va_c53));
        ghost var va_b56, va_s56 := va_lemma_MOV_ToReg(va_b55, va_s54, va_s53, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        found_slot := TRUE;
        va_s53 := va_lemma_empty(va_s56, va_s53);
      }
      else
      {
        ghost var va_b58 := va_get_block(va_get_ifFalse(va_c53));
        ghost var va_s59, va_c59, va_b59 := va_lemma_block(va_b58, va_s54, va_s53);
        ghost var va_cond_c59, va_s60:va_state := va_lemma_ifElse(va_get_ifCond(va_c59),
          va_get_ifTrue(va_c59), va_get_ifFalse(va_c59), va_s54, va_s59);
        if (va_cond_c59)
        {
          ghost var va_b61 := va_get_block(va_get_ifTrue(va_c59));
          ghost var va_b62, va_s62 := va_lemma_MOV_ToReg(va_b61, va_s60, va_s59,
            va_op_reg_reg(EDX), va_const_word(FALSE));
          found_slot := FALSE;
          va_s59 := va_lemma_empty(va_s62, va_s59);
        }
        else
        {
          ghost var va_b64 := va_get_block(va_get_ifFalse(va_c59));
          ghost var va_b65, va_s65 := va_lemma_ADD(va_b64, va_s60, va_s59, va_op_word_reg(EAX),
            va_const_word(1));
          ghost var va_b66, va_s66 := va_lemma_MOV_ToReg(va_b65, va_s65, va_s59,
            va_op_reg_reg(EDX), va_const_word(TRUE));
          found_slot := FALSE;
          va_s59 := va_lemma_empty(va_s66, va_s59);
        }
        va_s53 := va_lemma_empty(va_s59, va_s53);
      }
      va_s50 := va_lemma_empty(va_s53, va_s50);
    }
    else
    {
      ghost var va_b68 := va_get_block(va_get_ifFalse(va_c50));
      ghost var va_s69, va_c69, va_b69 := va_lemma_block(va_b68, va_s51, va_s50);
      ghost var va_cond_c69, va_s70:va_state := va_lemma_ifElse(va_get_ifCond(va_c69),
        va_get_ifTrue(va_c69), va_get_ifFalse(va_c69), va_s51, va_s69);
      if (va_cond_c69)
      {
        ghost var va_b71 := va_get_block(va_get_ifTrue(va_c69));
        ghost var va_b72, va_s72 := va_lemma_MOV_ToReg(va_b71, va_s70, va_s69, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        found_slot := FALSE;
        va_s69 := va_lemma_empty(va_s72, va_s69);
      }
      else
      {
        ghost var va_b74 := va_get_block(va_get_ifFalse(va_c69));
        ghost var va_b75, va_s75 := va_lemma_ADD(va_b74, va_s70, va_s69, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b76, va_s76 := va_lemma_MOV_ToReg(va_b75, va_s75, va_s69, va_op_reg_reg(EDX),
          va_const_word(TRUE));
        found_slot := FALSE;
        va_s69 := va_lemma_empty(va_s76, va_s69);
      }
      va_s50 := va_lemma_empty(va_s69, va_s50);
    }
    va_sW42 := va_lemma_empty(va_s50, va_sW42);
    va_sW41 := va_sW42;
    va_n41 := va_n41 - 1;
  }
  va_s40 := va_lemma_whileFalse(va_get_whileCond(va_c40), va_get_whileBody(va_c40), va_sW41,
    va_s40);
  ghost var va_s78, va_c78, va_b78 := va_lemma_block(va_b40, va_s40, va_sM);
  ghost var va_cond_c78, va_s79:va_state := va_lemma_ifElse(va_get_ifCond(va_c78),
    va_get_ifTrue(va_c78), va_get_ifFalse(va_c78), va_s40, va_s78);
  if (va_cond_c78)
  {
    ghost var va_b80 := va_get_block(va_get_ifTrue(va_c78));
    ghost var va_s81, va_c81, va_b81 := va_lemma_block(va_b80, va_s79, va_s78);
    ghost var va_cond_c81, va_s82:va_state := va_lemma_ifElse(va_get_ifCond(va_c81),
      va_get_ifTrue(va_c81), va_get_ifFalse(va_c81), va_s79, va_s81);
    if (va_cond_c81)
    {
      ghost var va_b83 := va_get_block(va_get_ifTrue(va_c81));
      ghost var va_b84, va_s84 := va_lemma_Store(va_b83, va_s82, va_s81, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b85, va_s85 := va_lemma_Store(va_b84, va_s84, va_s81, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(EAX));
      va_s81 := va_lemma_empty(va_s85, va_s81);
    }
    else
    {
      ghost var va_b86 := va_get_block(va_get_ifFalse(va_c81));
      assert va_get_reg(EAX, va_s82) == WimpUSBPDev_DevList_ENTRIES - 1;  // line 1708 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      assert found_slot == FALSE;  // line 1709 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      ghost var va_b89, va_s89 := va_lemma_Store(va_b86, va_s82, va_s81, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b90, va_s90 := va_lemma_Store(va_b89, va_s89, va_s81, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
      va_s81 := va_lemma_empty(va_s90, va_s81);
    }
    va_s78 := va_lemma_empty(va_s81, va_s78);
  }
  else
  {
    ghost var va_b91 := va_get_block(va_get_ifFalse(va_c78));
    assert va_get_reg(EAX, va_s79) == WimpUSBPDev_DevList_ENTRIES - 1;  // line 1717 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    assert found_slot == FALSE;  // line 1718 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    ghost var va_b94, va_s94 := va_lemma_Store(va_b91, va_s79, va_s78, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b95, va_s95 := va_lemma_Store(va_b94, va_s94, va_s78, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
    va_s78 := va_lemma_empty(va_s95, va_s78);
  }
  ghost var va_b96, va_s96 := va_lemma_POP_Reg1ToReg6(va_b78, va_s78, va_sM);
  ghost var va_b97, va_s97 := va_lemma_POP_OneReg(va_b96, va_s96, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s97, va_sM);
}
//--
//-- usbpdevlist_clear_all_devices

function method{:opaque} va_code_usbpdevlist_clear_all_devices():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_While(va_cmp_lt(va_op_cmp_reg(EAX),
    va_const_cmp(WimpUSBPDev_DevList_ENTRIES)), va_Block(va_CCons(va_code_PUSH_VOID(1 *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbpdevlist_get_id(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbpdev_is_empty_addr(va_op_reg_reg(ECX), va_op_reg_reg(EBX),
    va_op_reg_reg(ESI)), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_CALL_USBPDev_Clear(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CNil()))))))), va_Block(va_CNil())), va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(1)), va_CNil()))))))))))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))
}

lemma{:timeLimitMultiplier 30} va_lemma_usbpdevlist_clear_all_devices(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbpdevlist_clear_all_devices(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 6 *
    ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0));
    var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH,
    WimpUSBPDev_ADDR_EMPTY_LOW); usb_is_usbpdev_addr_valid(empty_addr) && (forall addr:USBPDev_Addr
    :: addr in all_non_empty_addrs ==> (var dev_id := Map_USBPDevAddr_ToDevID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, addr); dev_id in va_s0.subjects.usbpdevs))
  ensures  var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0));
    usbpdev_clear_multi_non_mstate_relationship(va_s0, va_sM, all_non_empty_addrs)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_objects(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_usbpdevlist_clear_all_devices();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var begin_state := va_s8;
  ghost var orig_ebp := va_get_reg(EBP, va_s8);
  ghost var va_b11, va_s11 := va_lemma_MOV_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
  Lemma_usbpdevlist_clear_all_devices_ProveAllAddrsMapToExistingUSBPDevs(va_s11);
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b11, va_s11, va_sM);
  ghost var va_n15:int, va_sW15:va_state := va_lemma_while(va_get_whileCond(va_c14),
    va_get_whileBody(va_c14), va_s11, va_s14);
  while (va_n15 > 0)
    invariant va_whileInv(va_get_whileCond(va_c14), va_get_whileBody(va_c14), va_n15, va_sW15,
      va_s14)
    invariant va_get_ok(va_sW15)
    invariant 0 <= va_get_reg(EAX, va_sW15) <= WimpUSBPDev_DevList_ENTRIES
    invariant va_get_reg(EAX, va_sW15) == 0 ==> state_equal_except_mstate(va_old_s, va_sW15)
    invariant global_read_fullval(va_get_globals(va_old_s), G_WimpUSBPDev_DevList()) ==
      global_read_fullval(va_get_globals(va_sW15), G_WimpUSBPDev_DevList())
    invariant va_get_reg(EAX, va_sW15) != 0 ==> (var previous_non_empty_addrs :=
      usbpdevlist_get_non_empty_addrs_until_slot(va_get_globals(va_old_s), va_get_reg(EAX, va_sW15)
      - 1); usbpdev_clear_multi_non_mstate_relationship(va_old_s, va_sW15,
      previous_non_empty_addrs))
    invariant va_get_reg(ESP, va_sW15) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW15.wk_mstate.m,
      va_get_reg(ESP, va_sW15))
    invariant va_get_reg(EBP, va_sW15) == orig_ebp
    invariant va_get_globals(va_sW15) == va_get_globals(va_old_s)
    invariant va_sW15.wk_mstate.sregs == va_old_s.wk_mstate.sregs
    invariant InstSaneState(va_sW15)
    invariant va_state_eq(va_sW15, va_update_reg(EBP, va_sW15, va_update_reg(ESP, va_sW15,
      va_update_reg(EDI, va_sW15, va_update_reg(ESI, va_sW15, va_update_reg(EDX, va_sW15,
      va_update_reg(ECX, va_sW15, va_update_reg(EBX, va_sW15, va_update_reg(EAX, va_sW15,
      va_update_objects(va_sW15, va_update_mem(va_sW15, va_update_ok(va_sW15, va_s0))))))))))))
    decreases WimpUSBPDev_DevList_ENTRIES - va_get_reg(EAX, va_sW15)
  {
    ghost var va_s15:va_state, va_sW16:va_state := va_lemma_whileTrue(va_get_whileCond(va_c14),
      va_get_whileBody(va_c14), va_n15, va_sW15, va_s14);
    ghost var va_b17 := va_get_block(va_get_whileBody(va_c14));
    ghost var beginwhile_this := va_s15;
    assert va_get_reg(EAX, va_s15) < WimpUSBPDev_DevList_ENTRIES;  // line 1824 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    ghost var va_b20, va_s20 := va_lemma_PUSH_VOID(va_b17, va_s15, va_sW16, 1 * ARCH_WORD_BYTES);
    ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sW16, va_op_word_reg(EAX));
    ghost var va_b22, va_s22 := va_lemma_usbpdevlist_get_id(va_b21, va_s21, va_sW16);
    ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_sW16, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_sW16, va_op_word_reg(ECX),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_sW16, 2 * ARCH_WORD_BYTES);
    ghost var va_b26, va_s26 := va_lemma_usbpdev_is_empty_addr(va_b25, va_s25, va_sW16,
      va_op_reg_reg(ECX), va_op_reg_reg(EBX), va_op_reg_reg(ESI));
    ghost var va_s27, va_c27, va_b27 := va_lemma_block(va_b26, va_s26, va_sW16);
    ghost var va_cond_c27, va_s28:va_state := va_lemma_ifElse(va_get_ifCond(va_c27),
      va_get_ifTrue(va_c27), va_get_ifFalse(va_c27), va_s26, va_s27);
    if (va_cond_c27)
    {
      ghost var va_b29 := va_get_block(va_get_ifTrue(va_c27));
      ghost var usbpdev_addr := UInt64_FromTwoUInt32s(va_get_reg(ECX, va_s28), va_get_reg(EBX,
        va_s28));
      Lemma_USBPDevAddr_NonEmptyAddrRawParseToNonEmptyAddr(usbpdev_addr);
      ghost var va_b32, va_s32 := va_lemma_PUSH_Reg1ToReg6(va_b29, va_s28, va_s27);
      ghost var va_b33, va_s33 := va_lemma_PUSH(va_b32, va_s32, va_s27, va_op_word_reg(ECX));
      ghost var va_b34, va_s34 := va_lemma_PUSH(va_b33, va_s33, va_s27, va_op_word_reg(EBX));
      ghost var this1 := va_s34;
      ghost var in_high := va_get_reg(ECX, va_s34);
      ghost var in_low := va_get_reg(EBX, va_s34);
      ghost var in_addr := usb_parse_usbpdev_addr(UInt64_FromTwoUInt32s(in_high, in_low));
      Lemma_usbpdevlist_clear_all_devices_ProveNonEmptyAddrMapsToExistingUSBPDev(this1,
        va_get_reg(EAX, va_s34));
      assert Map_USBPDevAddr_ToDevID(this1.subjects, this1.objects, this1.id_mappings, in_addr) in
        this1.subjects.usbpdevs;  // line 1849 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      ghost var va_b41, va_s41 := va_lemma_CALL_USBPDev_Clear(va_b34, va_s34, va_s27);
      ghost var this2 := va_s41;
      ghost var va_b43, va_s43 := va_lemma_POP_VOID(va_b41, va_s41, va_s27, 2 * ARCH_WORD_BYTES);
      ghost var va_b44, va_s44 := va_lemma_POP_Reg1ToReg6(va_b43, va_s43, va_s27);
      ghost var addr:USBPDev_Addr := usb_parse_usbpdev_addr(UInt64_FromTwoUInt32s(va_get_reg(ECX,
        va_s44), va_get_reg(EBX, va_s44)));
      assert addr == in_addr;  // line 1858 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      assert usbpdev_clear_non_mstate_relationship(this1, this2, addr);  // line 1859 column 13 of file .\dev/usb2/usb_pdev_utils.vad
      va_s27 := va_lemma_empty(va_s44, va_s27);
    }
    else
    {
      ghost var va_b48 := va_get_block(va_get_ifFalse(va_c27));
      va_s27 := va_lemma_empty(va_s28, va_s27);
    }
    ghost var beforeadd_this := va_s27;
    ghost var va_b50, va_s50 := va_lemma_ADD(va_b27, va_s27, va_sW16, va_op_word_reg(EAX),
      va_const_word(1));
    ghost var endwhile_this := va_s50;
    if (va_get_reg(ESI, va_s50) == TRUE)
    {
      if (va_get_reg(EAX, va_s50) - 1 != 0)
      {
        Lemma_usbpdevlist_clear_all_devices_PropertiesOfI_IfIIsNot0(va_get_reg(EAX, va_s50) - 1);
        Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsTrueAndIIsNot0(va_old_s,
          beginwhile_this, endwhile_this, va_get_reg(EAX, va_s50) - 1);
      }
      else
      {
        Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsTrueAndIIs0(va_old_s,
          beginwhile_this, endwhile_this, va_get_reg(EAX, va_s50) - 1);
      }
    }
    else
    {
      if (va_get_reg(EAX, va_s50) - 1 != 0)
      {
        Lemma_usbpdevlist_clear_all_devices_PropertiesOfI_IfIIsNot0(va_get_reg(EAX, va_s50) - 1);
        Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsFalseAndIIsNot0(va_old_s,
          beginwhile_this, endwhile_this, va_get_reg(EAX, va_s50) - 1);
      }
      else
      {
        Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsFalseAndIIs0(va_old_s,
          beginwhile_this, endwhile_this, va_get_reg(EAX, va_s50) - 1);
      }
    }
    ghost var next_previous_non_empty_addrs :=
      usbpdevlist_get_non_empty_addrs_until_slot(va_get_globals(va_old_s), va_get_reg(EAX, va_s50)
      - 1);
    assert usbpdev_clear_multi_non_mstate_relationship(va_old_s, va_s50,
      next_previous_non_empty_addrs);  // line 1893 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    assert va_get_reg(EAX, va_s50) != 0;  // line 1894 column 9 of file .\dev/usb2/usb_pdev_utils.vad
    Lemma_modify_regs_objects_stateeq(beginwhile_this, endwhile_this);
    va_sW16 := va_lemma_empty(va_s50, va_sW16);
    va_sW15 := va_sW16;
    va_n15 := va_n15 - 1;
  }
  va_s14 := va_lemma_whileFalse(va_get_whileCond(va_c14), va_get_whileBody(va_c14), va_sW15,
    va_s14);
  ghost var outloop_this := va_s14;
  assert usbpdevlist_get_non_empty_addrs_until_slot(va_get_globals(va_old_s),
    WimpUSBPDev_DevList_ENTRIES - 1) ==
    usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_old_s));  // line 1902 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_old_s));
  assert usbpdev_clear_multi_non_mstate_relationship(va_old_s, outloop_this, all_non_empty_addrs); 
    // line 1905 column 5 of file .\dev/usb2/usb_pdev_utils.vad
  ghost var va_b61, va_s61 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b62, va_s62 := va_lemma_POP_OneReg(va_b61, va_s61, va_sM, va_op_reg_reg(EBP));
  Lemma_usbpdevlist_clear_all_devices_ProveProperty1(va_old_s, outloop_this, va_s62,
    all_non_empty_addrs);
  va_sM := va_lemma_empty(va_s62, va_sM);
}
//--
// Function: Return all FDs owned by the set of USBPDevs
function method USBPDev_OwnedFDs(s:state, dev_ids:set<Dev_ID>) : (result:set<FD_ID>)
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires forall id :: id in dev_ids ==> id in s.subjects.usbpdevs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && WSM_DoOwnObj(s.subjects, dev_id.sid, id.oid))
    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in s.subjects.usbpdevs[dev_id].fd_ids)
    ensures forall dev_id, id :: dev_id in dev_ids && id in WSM_AllFDIDs(s.objects) &&
                    WSM_DoOwnObj(s.subjects, dev_id.sid, id.oid)
                ==> id in result
        // Property 1: Return all owned FDs
    ensures result <= MapGetKeys(s.objects.usbpdev_fds)
    ensures forall dev_id :: dev_id in dev_ids
                ==> s.subjects.usbpdevs[dev_id].fd_ids <= result
        // Property 2: Returned FDs must be owned by a returned USBPDev
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    var ids := set dev_id, id | dev_id in dev_ids && id in WSM_AllFDIDs(s.objects) && WSM_DoOwnObj(s.subjects, dev_id.sid, id.oid) :: id;

    assert WK_ValidObjs_ObjInSubjsMustBeInState(s.subjects, s.objects);
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidSubjs_SubjIDs();

    ids
}

// Function: Return all DOs owned by the set of USBPDevs
function method USBPDev_OwnedDOs(s:state, dev_ids:set<Dev_ID>) : (result:set<DO_ID>)
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires forall id :: id in dev_ids ==> id in s.subjects.usbpdevs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && WSM_DoOwnObj(s.subjects, dev_id.sid, id.oid))
    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in s.subjects.usbpdevs[dev_id].do_ids)
    ensures forall dev_id, id :: dev_id in dev_ids && id in WSM_AllDOIDs(s.objects) &&
                    WSM_DoOwnObj(s.subjects, dev_id.sid, id.oid)
                ==> id in result
        // Property 1: Return all owned DOs
    ensures result <= MapGetKeys(s.objects.usbpdev_dos)
    ensures forall dev_id :: dev_id in dev_ids
                ==> s.subjects.usbpdevs[dev_id].do_ids <= result
        // Property 2: Returned DOs must be owned by a returned USBPDev
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    var ids := set dev_id, id | dev_id in dev_ids && id in WSM_AllDOIDs(s.objects) && WSM_DoOwnObj(s.subjects, dev_id.sid, id.oid) :: id;

    assert WK_ValidObjs_ObjInSubjsMustBeInState(s.subjects, s.objects);
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidSubjs_SubjIDs();

    ids
}

// Predicate: All USBPDevs at <addrs> are cleared, and nothing else outside the machine state is modified
predicate {:opaque} usbpdev_clear_multi_non_mstate_relationship(s1:state, s2:state, addrs:set<USBPDev_Addr>)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs
{
    var t := usbpdev_addrs_to_subjs_fds_dos_ids(s1, addrs);
    var usbpdev_ids:set<Dev_ID> := t.0;
    var usbpdev_fd_ids:set<FD_ID> := t.1;
    var usbpdev_do_ids:set<DO_ID> := t.2;

    // Immutable state variables
    s1.subjects == s2.subjects &&
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&

    // Other objects are unchanged
    s1.objects.os_tds == s2.objects.os_tds &&
    s1.objects.os_fds == s2.objects.os_fds &&
    s1.objects.os_dos == s2.objects.os_dos &&
    s1.objects.eehci_hcoded_tds == s2.objects.eehci_hcoded_tds &&
    s1.objects.eehci_other_tds == s2.objects.eehci_other_tds &&
    s1.objects.eehci_fds == s2.objects.eehci_fds &&
    s1.objects.eehci_dos == s2.objects.eehci_dos &&
    s1.objects.usbtd_tds == s2.objects.usbtd_tds &&
    s1.objects.usbtd_fds == s2.objects.usbtd_fds &&
    s1.objects.usbtd_dos == s2.objects.usbtd_dos &&
    s1.objects.wimpdrv_dos == s2.objects.wimpdrv_dos &&
    s1.objects.usbpdev_tds == s2.objects.usbpdev_tds &&

    // In <usbpdev_fds>, clear the contents of the USBPDev's FDs only
    MapGetKeys(s1.objects.usbpdev_fds) == MapGetKeys(s2.objects.usbpdev_fds) &&
    (
        forall id :: id in s1.objects.usbpdev_fds
            ==> (id in usbpdev_fd_ids ==> WSM_IsFDClearVal(s2.objects.usbpdev_fds, id)) &&
                (id !in usbpdev_fd_ids ==> s1.objects.usbpdev_fds[id] == s2.objects.usbpdev_fds[id])
    ) &&

    // In <usbpdev_dos>, clear the contents of the USBPDev's DOs only
    MapGetKeys(s1.objects.usbpdev_dos) == MapGetKeys(s2.objects.usbpdev_dos) &&
    (
        forall id :: id in s1.objects.usbpdev_dos
            ==> (id in usbpdev_do_ids ==> WSM_IsDOClearVal(s2.objects.usbpdev_dos, id)) &&
                (id !in usbpdev_do_ids ==> s1.objects.usbpdev_dos[id] == s2.objects.usbpdev_dos[id])
    ) &&

    (true)
}

// Function: Given the set of <addrs>, return the USBPDev subject IDs, owned FDs and DOs
function usbpdev_addrs_to_subjs_fds_dos_ids(
    s:state, addrs:set<USBPDev_Addr>
) : (result:(set<Dev_ID>, set<FD_ID>, set<DO_ID>))
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs

    ensures forall dev_id :: dev_id in result.0
                ==> dev_id in s.subjects.usbpdevs
        // Property 1: Returned Dev_IDs must be USBPDev IDs
    ensures forall id :: id in result.1
                ==> id in s.objects.usbpdev_fds
    ensures forall id :: id in result.1
                ==> (exists dev_id :: dev_id in result.0 &&
                            id in s.subjects.usbpdevs[dev_id].fd_ids)
    ensures forall dev_id :: dev_id in result.0
                ==> s.subjects.usbpdevs[dev_id].fd_ids <= result.1
        // Property 2: Returned FDs must be owned by a returned USBPDev
    ensures forall id :: id in result.2
                ==> id in s.objects.usbpdev_dos
    ensures forall id :: id in result.2
                ==> (exists dev_id :: dev_id in result.0 &&
                            id in s.subjects.usbpdevs[dev_id].do_ids)
    ensures forall dev_id :: dev_id in result.0
                ==> s.subjects.usbpdevs[dev_id].do_ids <= result.2
        // Property 3: Returned DOs must be owned by a returned USBPDev
{
    var usbpdev_ids:set<Dev_ID> := set addr | addr in addrs :: Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr);
    var fd_ids:set<FD_ID> := USBPDev_OwnedFDs(s, usbpdev_ids);
    var do_ids:set<DO_ID> := USBPDev_OwnedDOs(s, usbpdev_ids);

    (usbpdev_ids, fd_ids, do_ids)
}

// Function: Return all USBPDev addresses stored in <g_wimpdevs_devlist> until the slot <until_slot> (including) in
// this global variable
function usbpdevlist_get_addrs_until_slot(globals:globalsmap, until_slot:uint32) : (result:set<USBPDev_Addr>)
    requires WK_ValidGlobalVars_Decls(globals)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals)

    requires 0 <= until_slot < WimpUSBPDev_DevList_ENTRIES

    ensures forall addr :: addr in result
                ==> (exists i:uint32 :: usbpdevlist_valid_slot_id(i) && 
                                0 <= i <= until_slot &&
                                addr == usb_parse_usbpdev_addr(usbpdevlist_get_addr(globals, i)))
    ensures forall i:uint32 :: usbpdevlist_valid_slot_id(i) && 0 <= i <= until_slot
                ==> usb_parse_usbpdev_addr(usbpdevlist_get_addr(globals, i)) in result
        // Property: The result contains all USBPDev addresses stored in <g_wimpdevs_devlist>
{
    set i:uint32 | 0 <= i <= until_slot
          :: (
              var usbpdev_addr_raw := usbpdevlist_get_addr(globals, i);
              usb_parse_usbpdev_addr(usbpdev_addr_raw)
          )
}

// Function: Return all non-empty USBPDev addresses stored in <g_wimpdevs_devlist>
function usbpdevlist_get_non_empty_addrs_until_slot(globals:globalsmap, until_slot:uint32) : (result:set<USBPDev_Addr>)
    requires WK_ValidGlobalVars_Decls(globals)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals)
    requires 0 <= until_slot < WimpUSBPDev_DevList_ENTRIES
{
    var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
    assert usb_is_usbpdev_addr_valid(empty_addr);

    usbpdevlist_get_addrs_until_slot(globals, until_slot) - {usb_parse_usbpdev_addr(empty_addr)}
}
lemma Lemma_usbpdevlist_clear_all_devices_ProveAllAddrsMapToExistingUSBPDevs(s:state)
    requires InstSaneState(s)

    ensures var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr)
        // Properties needed by the following property
    ensures var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s.wk_mstate));
            forall addr :: addr in all_non_empty_addrs
                ==> (
                        var dev_id := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr);
                        dev_id in s.subjects.usbpdevs
                    )
{
    reveal WK_ValidGlobalVarValues_USBPDevList();
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
}

lemma Lemma_usbpdevlist_clear_all_devices_ProveNonEmptyAddrMapsToExistingUSBPDev(s1:state, i:uint32)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)
    requires WK_ValidGlobalState(wkm_get_globals(s1.wk_mstate))
    requires WK_ValidGlobalVarValues_USBPDevList(s1.subjects, s1.id_mappings, wkm_get_globals(s1.wk_mstate))

    requires 0 <= i < WimpUSBPDev_DevList_ENTRIES

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             var s1_globals := wkm_get_globals(s1.wk_mstate);
             var addr_raw := usbpdevlist_get_addr(s1_globals, i);
             usb_is_usbpdev_addr_valid(addr_raw) &&
             var addr := usb_parse_usbpdev_addr(addr_raw);
             addr != usb_parse_usbpdev_addr(empty_addr)
        // Requirement: Properties when tmp1 is false

    ensures var s1_globals := wkm_get_globals(s1.wk_mstate);
            var addr_raw := usbpdevlist_get_addr(s1_globals, i);
            var addr := usb_parse_usbpdev_addr(addr_raw);
            var id := Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr);
            id in s1.subjects.usbpdevs
{
    reveal WK_ValidGlobalVarValues_USBPDevList();
}

lemma Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsTrueAndIIsNot0(old_s:state, s1:state, s2:state, i:uint32)
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)
    requires WK_ValidGlobalState(wkm_get_globals(old_s.wk_mstate))
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(wkm_get_globals(old_s.wk_mstate))
    requires WK_ValidGlobalVarValues_USBPDevList(old_s.subjects, old_s.id_mappings, wkm_get_globals(old_s.wk_mstate))

    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s1.wk_mstate))
    
    requires 0 < i < WimpUSBPDev_DevList_ENTRIES

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), (i - 1));
             (forall addr :: addr in previous_non_empty_addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), (i - 1));
             (forall addr :: addr in previous_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs)
        // Requirement: Utility invariant needed by the following invariant
    requires var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), (i - 1));
             usbpdev_clear_multi_non_mstate_relationship(old_s, s1, previous_non_empty_addrs)
        // Requirement: Known invariant 1 at the beginning of the iteration

    requires wkm_get_globals(s1.wk_mstate) == wkm_get_globals(s2.wk_mstate)
    requires state_equal_except_mstate(s1, s2);
        // Requirement: Properties between s1 and s2
    requires var s1_globals := wkm_get_globals(s1.wk_mstate);
             usbpdevlist_get_addr_high(s1_globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH &&
             usbpdevlist_get_addr_low(s1_globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW
        // Requirement: Properties when tmp1 is true
    requires global_read_fullval(wkm_get_globals(old_s.wk_mstate), G_WimpUSBPDev_DevList()) == 
             global_read_fullval(wkm_get_globals(s1.wk_mstate), G_WimpUSBPDev_DevList())
        // Requirement: G_WimpUSBPDev_DevList() is unmodified

    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
             (forall addr :: addr in next_previous_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs) 
        // Proeprties needed by the following property
    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
            usbpdev_clear_multi_non_mstate_relationship(old_s, s2, next_previous_non_empty_addrs)
        // Property: Invariant 1 after this iteration
{
    // Prove utility property
    reveal WK_ValidGlobalVarValues_USBPDevList();
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();

    // Prove Invariant 1
    reveal usbpdev_clear_multi_non_mstate_relationship();
    var old_s_globals := wkm_get_globals(old_s.wk_mstate);
    var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(old_s_globals, (i - 1));
    var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(old_s_globals, i);

    //// Prove set2 == set1 + {cur_addr}
    var set1 := usbpdevlist_get_addrs_until_slot(old_s_globals, (i - 1));
    var set2 := usbpdevlist_get_addrs_until_slot(old_s_globals, i);

    var usbpdev_addr_raw := usbpdevlist_get_addr(old_s_globals, i);
    var cur_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

    assert set2 == set1 + {cur_addr};

    //// Prove cur_addr == usb_parse_usbpdev_addr(empty_addr)
    var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr();
    assert cur_addr == usb_parse_usbpdev_addr(empty_addr);

    //// Prove the post-condition
    assert previous_non_empty_addrs == set1 - {usb_parse_usbpdev_addr(empty_addr)};
    assert next_previous_non_empty_addrs == set2 - {usb_parse_usbpdev_addr(empty_addr)};
     
    assert previous_non_empty_addrs == next_previous_non_empty_addrs;
}

lemma Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsTrueAndIIs0(old_s:state, s1:state, s2:state, i:uint32)
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)
    requires WK_ValidGlobalState(wkm_get_globals(old_s.wk_mstate))
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(wkm_get_globals(old_s.wk_mstate))
    requires WK_ValidGlobalVarValues_USBPDevList(old_s.subjects, old_s.id_mappings, wkm_get_globals(old_s.wk_mstate))

    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s1.wk_mstate))
    
    requires i == 0

    requires state_equal_except_mstate(old_s, s1)
        // Requirement: Known invariant 1 at the beginning of the iteration

    requires wkm_get_globals(s1.wk_mstate) == wkm_get_globals(s2.wk_mstate)
    requires state_equal_except_mstate(s1, s2);
        // Requirement: Properties between s1 and s2
    requires var s1_globals := wkm_get_globals(s1.wk_mstate);
             usbpdevlist_get_addr_high(s1_globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH &&
             usbpdevlist_get_addr_low(s1_globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW
        // Requirement: Properties when tmp1 is true
    requires global_read_fullval(wkm_get_globals(old_s.wk_mstate), G_WimpUSBPDev_DevList()) == 
             global_read_fullval(wkm_get_globals(s1.wk_mstate), G_WimpUSBPDev_DevList())
        // Requirement: G_WimpUSBPDev_DevList() is unmodified

    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
             (forall addr :: addr in next_previous_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs) 
        // Proeprties needed by the following property
    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
            usbpdev_clear_multi_non_mstate_relationship(old_s, s2, next_previous_non_empty_addrs)
        // Property: Invariant 1 after this iteration
{
    // Prove utility property
    reveal WK_ValidGlobalVarValues_USBPDevList();
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();

    // Prove Invariant 1
    reveal usbpdev_clear_multi_non_mstate_relationship();
}

lemma Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsFalseAndIIsNot0(old_s:state, s1:state, s2:state, i:uint32)
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)
    requires WK_ValidGlobalState(wkm_get_globals(old_s.wk_mstate))
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(wkm_get_globals(old_s.wk_mstate))
    requires WK_ValidGlobalVarValues_USBPDevList(old_s.subjects, old_s.id_mappings, wkm_get_globals(old_s.wk_mstate))

    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s1.wk_mstate))
    
    requires 0 < i < WimpUSBPDev_DevList_ENTRIES

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), (i - 1));
             (forall addr :: addr in previous_non_empty_addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), (i - 1));
             (forall addr :: addr in previous_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs)
        // Requirement: Utility invariant needed by the following invariant
    requires var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), (i - 1));
             usbpdev_clear_multi_non_mstate_relationship(old_s, s1, previous_non_empty_addrs)
        // Requirement: Known invariant 1 at the beginning of the iteration

    requires wkm_get_globals(s1.wk_mstate) == wkm_get_globals(s2.wk_mstate)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             var s1_globals := wkm_get_globals(s1.wk_mstate);
             var addr_raw := usbpdevlist_get_addr(s1_globals, i);
             usb_is_usbpdev_addr_valid(addr_raw) &&
             var addr := usb_parse_usbpdev_addr(addr_raw);
             addr != usb_parse_usbpdev_addr(empty_addr) &&
             Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs &&
             usbpdev_clear_non_mstate_relationship(s1, s2, addr);
        // Requirement: Properties when tmp1 is false
    requires global_read_fullval(wkm_get_globals(old_s.wk_mstate), G_WimpUSBPDev_DevList()) == 
             global_read_fullval(wkm_get_globals(s1.wk_mstate), G_WimpUSBPDev_DevList())
        // Requirement: G_WimpUSBPDev_DevList() is unmodified

    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
             (forall addr :: addr in next_previous_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs) 
        // Proeprties needed by the following property
    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
            usbpdev_clear_multi_non_mstate_relationship(old_s, s2, next_previous_non_empty_addrs)
        // Property: Invariant 1 after this iteration
{
    // Prove utility property
    reveal WK_ValidGlobalVarValues_USBPDevList();
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();

    // Prove Invariant 1
    reveal usbpdev_clear_multi_non_mstate_relationship();
    var old_s_globals := wkm_get_globals(old_s.wk_mstate);
    var previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(old_s_globals, (i - 1));
    var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(old_s_globals, i);


    //// Prove set2 == set1 + {cur_addr}
    var s1_globals := wkm_get_globals(s1.wk_mstate);
    var set1 := usbpdevlist_get_addrs_until_slot(old_s_globals, (i - 1));
    var set2 := usbpdevlist_get_addrs_until_slot(old_s_globals, i);

    var usbpdev_addr_raw := usbpdevlist_get_addr(old_s_globals, i);
    assert usbpdev_addr_raw == usbpdevlist_get_addr(s1_globals, i);
    var cur_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
    
    assert set2 == set1 + {cur_addr};
    assert usbpdev_clear_non_mstate_relationship(s1, s2, cur_addr);

    //// Prove the post-condition
    assert next_previous_non_empty_addrs == previous_non_empty_addrs + {cur_addr};
}

lemma Lemma_usbpdevlist_clear_all_devices_ProveInvariant1_WhenTmp1IsFalseAndIIs0(old_s:state, s1:state, s2:state, i:uint32)
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)
    requires WK_ValidGlobalState(wkm_get_globals(old_s.wk_mstate))
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(wkm_get_globals(old_s.wk_mstate))
    requires WK_ValidGlobalVarValues_USBPDevList(old_s.subjects, old_s.id_mappings, wkm_get_globals(old_s.wk_mstate))

    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s1.wk_mstate))
    
    requires i == 0

    requires state_equal_except_mstate(old_s, s1)
        // Requirement: Known invariant 1 at the beginning of the iteration

    requires wkm_get_globals(s1.wk_mstate) == wkm_get_globals(s2.wk_mstate)
    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             var s1_globals := wkm_get_globals(s1.wk_mstate);
             var addr_raw := usbpdevlist_get_addr(s1_globals, i);
             usb_is_usbpdev_addr_valid(addr_raw) &&
             var addr := usb_parse_usbpdev_addr(addr_raw);
             addr != usb_parse_usbpdev_addr(empty_addr) &&
             Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs &&
             usbpdev_clear_non_mstate_relationship(s1, s2, addr);
        // Requirement: Properties when tmp1 is false
    requires global_read_fullval(wkm_get_globals(old_s.wk_mstate), G_WimpUSBPDev_DevList()) == 
             global_read_fullval(wkm_get_globals(s1.wk_mstate), G_WimpUSBPDev_DevList())
        // Requirement: G_WimpUSBPDev_DevList() is unmodified

    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
             (forall addr :: addr in next_previous_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs) 
        // Proeprties needed by the following property
    ensures var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(wkm_get_globals(old_s.wk_mstate), i);
            usbpdev_clear_multi_non_mstate_relationship(old_s, s2, next_previous_non_empty_addrs)
        // Property: Invariant 1 after this iteration
{
    // Prove utility property
    reveal WK_ValidGlobalVarValues_USBPDevList();
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();

    // Prove Invariant 1
    reveal usbpdev_clear_multi_non_mstate_relationship();
    var old_s_globals := wkm_get_globals(old_s.wk_mstate);
    var s1_globals := wkm_get_globals(s1.wk_mstate);

    var next_previous_non_empty_addrs := usbpdevlist_get_non_empty_addrs_until_slot(old_s_globals, i);
    var usbpdev_addr_raw := usbpdevlist_get_addr(old_s_globals, i);
    assert usbpdev_addr_raw == usbpdevlist_get_addr(s1_globals, i);
    var cur_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

    assert next_previous_non_empty_addrs == {cur_addr};
}

lemma Lemma_usbpdevlist_clear_all_devices_ProveProperty1(old_s:state, s1:state, s2:state, addrs:set<USBPDev_Addr>)
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs

    requires usbpdev_clear_multi_non_mstate_relationship(old_s, s1, addrs)
        // Requirement: s1 and old_s fulfills usbpdev_clear_multi_non_mstate_relationship
    requires state_equal_except_mstate(s1, s2)
        // Requirement: Properties between s1 and s2

    ensures usbpdev_clear_multi_non_mstate_relationship(old_s, s2, addrs)
{
    reveal usbpdev_clear_multi_non_mstate_relationship();
}

lemma Lemma_usbpdevlist_clear_all_devices_PropertiesOfI_IfIIsNot0(i:int)
    requires 0 <= i <= WimpUSBPDev_DevList_ENTRIES
    requires i != 0
    requires i < WimpUSBPDev_DevList_ENTRIES
    ensures 0 < i < WimpUSBPDev_DevList_ENTRIES
{
    // Dafny can automatically prove this lemma
}
// Prove the property 2 of <usbpdev_set_addr>
lemma Lemma_usbpdev_set_id_ProveProperty2(
    old_globals:globalsmap, globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, new_globals:globalsmap, 
    slot:word, new_addr_low:word, new_addr_high:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)

    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_gvar_valid_addr(G_WimpUSBPDev_Info(), vaddr)

    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            globals1 == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr, WimpUSBPDev_Slot_UpdateFlag_Updating)
    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
            globals2 == global_write_word(globals1, G_WimpUSBPDev_Info(), vaddr, new_addr_low)
    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
            globals3 == global_write_word(globals2, G_WimpUSBPDev_Info(), vaddr, new_addr_high)
    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            new_globals == global_write_word(globals3, G_WimpUSBPDev_Info(), vaddr, WimpUSBPDev_Slot_UpdateFlag_Complete)

    requires forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
                ==> p_usbpdev_slot_equal(old_globals, globals1, i)
    requires forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
                ==> p_usbpdev_slot_equal(globals1, globals2, i)
    requires forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
                ==> p_usbpdev_slot_equal(globals2, globals3, i)
    requires forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
                ==> p_usbpdev_slot_equal(globals3, new_globals, i)

    ensures var old_pid := usbpdev_get_pid(old_globals, slot).v;
            usbpdev_info_newvalue(old_globals, new_globals, slot, new_addr_low, new_addr_high, old_pid, WimpUSBPDev_Slot_UpdateFlag_Complete);
{
    reveal p_usbpdev_slot_equal();

    // Prove other global variables are unchanged
    forall i:uint32 | usbpdev_valid_slot_id(i) && i != slot
        ensures p_usbpdev_slot_equal(old_globals, new_globals, i)
    {
        // Dafny can automatically prove it
    }
    assert globals_other_gvar_unchanged(old_globals, new_globals, G_WimpUSBPDev_Info());

    // Apply usbpdev_info_newvalue 
    var old_pid := usbpdev_get_pid(old_globals, slot).v;

    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
    var vaddr2 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
    var vaddr3 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
    var vaddr4 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;

    var t_globals1 := global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_addr_low);
    var t_globals2 := global_write_word(t_globals1, G_WimpUSBPDev_Info(), vaddr2, new_addr_high);
    var t_globals3 := global_write_word(t_globals2, G_WimpUSBPDev_Info(), vaddr3, old_pid);
    var t_globals := global_write_word(t_globals3, G_WimpUSBPDev_Info(), vaddr4, WimpUSBPDev_Slot_UpdateFlag_Complete);

    forall i:uint32 | usbpdev_valid_slot_id(i) && i != slot
        ensures p_usbpdev_slot_equal(t_globals, new_globals, i)
    {
        // Dafny can automatically prove it
    }
    assert globals_other_gvar_unchanged(t_globals, new_globals, G_WimpUSBPDev_Info());

    if(!usbpdev_info_newvalue(old_globals, new_globals, slot, new_addr_low, new_addr_high, old_pid, WimpUSBPDev_Slot_UpdateFlag_Complete))
    {
        assert t_globals != new_globals;
        assert global_read_fullval(t_globals, G_WimpUSBPDev_Info()) != global_read_fullval(new_globals, G_WimpUSBPDev_Info());
        
        var i :| usbpdev_valid_slot_id(i) && !p_usbpdev_slot_equal(t_globals, new_globals, i);
        assert i == slot;

        assert false;
    }
}
