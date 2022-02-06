include "../ins/x86/ins_wrapper.gen.dfy"
include "drv.s.dfy"
include "public\\wimpdrv_util_predicates.s.dfy"
include "..\\dev\\usb2\\eehci_info.i.dfy"
include "..\\dev\\usb2\\usb_tds.i.dfy"
include "..\\dev\\usb2\\usb_pdev.i.dfy"
include "drv.i.dfy"
//-- _wimpdrv_slot_get_id_pid
//--
//-- _wimpdrv_update_slot_pid_to_invalid
//--
//-- _wimpdrv_update_slot_pid_to_valid
//--
//-- wimpdrv_check_slotid

function method{:opaque} va_code_wimpdrv_check_slotid(slot_id:va_operand_reg,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_IfElse(va_cmp_ge(va_coerce_reg_to_cmp(slot_id), va_const_cmp(0)),
    va_Block(va_CCons(va_IfElse(va_cmp_lt(va_coerce_reg_to_cmp(slot_id),
    va_const_cmp(WimpDrv_Info_ENTRIES)), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(TRUE)), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))
}

lemma va_lemma_wimpdrv_check_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot_id:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_check_slotid(slot_id, ret), va_s0, va_sN)
  requires va_is_src_reg(slot_id, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires slot_id != ret
  requires ret == Reg1
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> 0 <= va_eval_reg(va_sM, slot_id) <
    WimpDrv_Info_ENTRIES
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_wimpdrv_check_slotid();
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
//-- wimpdrv_ops_get_do_paddr_region

function method{:opaque} va_code_wimpdrv_ops_get_do_paddr_region():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_op_cmp_reg(ECX)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CNil())))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_wimpdrv_ops_get_do_paddr_region(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_do_paddr_region(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var out_do_pbase:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    out_do_pend:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); ret == TRUE ==> wimpdrv_do_get_paddr_base(va_get_globals(va_s0), slot) ==
    out_do_pbase && wimpdrv_do_get_paddr_end(va_get_globals(va_s0), slot) == out_do_pend
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 3 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_do_paddr_region();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 124 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s17), slot);
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b21, va_s21 := va_lemma_LDRglobal(va_b20, va_s20, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_sM);
  ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
    va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
  if (va_cond_c23)
  {
    ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s24, va_s23, va_op_reg_reg(EDX),
      va_op_word_reg(EDI));
    ghost var va_b27, va_s27 := va_lemma_ADD(va_b26, va_s26, va_s23, va_op_word_reg(EDX),
      va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset));
    ghost var va_b28, va_s28 := va_lemma_LDRglobal(va_b27, va_s27, va_s23, va_op_word_reg(EAX),
      G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
    ghost var va_b29, va_s29 := va_lemma_Store(va_b28, va_s28, va_s23, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    ghost var va_b30, va_s30 := va_lemma_MOV_ToReg(va_b29, va_s29, va_s23, va_op_reg_reg(EDX),
      va_op_word_reg(EDI));
    ghost var va_b31, va_s31 := va_lemma_ADD(va_b30, va_s30, va_s23, va_op_word_reg(EDX),
      va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset));
    ghost var va_b32, va_s32 := va_lemma_LDRglobal(va_b31, va_s31, va_s23, va_op_word_reg(EAX),
      G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
    ghost var va_b33, va_s33 := va_lemma_Store(va_b32, va_s32, va_s23, va_op_word_reg(EBP), 3 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    ghost var va_b34, va_s34 := va_lemma_Store(va_b33, va_s33, va_s23, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s23 := va_lemma_empty(va_s34, va_s23);
  }
  else
  {
    ghost var va_b35 := va_get_block(va_get_ifFalse(va_c23));
    ghost var va_b36, va_s36 := va_lemma_Store(va_b35, va_s24, va_s23, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s23 := va_lemma_empty(va_s36, va_s23);
  }
  ghost var va_b37, va_s37 := va_lemma_POP_OneReg(va_b23, va_s23, va_sM, va_op_reg_reg(EAX));
  ghost var va_b38, va_s38 := va_lemma_POP_TwoRegs(va_b37, va_s37, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b39, va_s39 := va_lemma_POP_TwoRegs(va_b38, va_s38, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b40, va_s40 := va_lemma_POP_OneReg(va_b39, va_s39, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s40, va_sM);
}
//--
//-- wimpdrv_ops_get_do_paddr_region_no_check

function method{:opaque} va_code_wimpdrv_ops_get_do_paddr_region_no_check():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EDI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))
}

lemma va_lemma_wimpdrv_ops_get_do_paddr_region_no_check(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_do_paddr_region_no_check(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_do_pbase:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    out_do_pend:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); wimpdrv_do_get_paddr_base(va_get_globals(va_s0), slot) == out_do_pbase &&
    wimpdrv_do_get_paddr_end(va_get_globals(va_s0), slot) == out_do_pend
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_do_paddr_region_no_check();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EDI));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(ESI),
    G_WimpDrvs_Info());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 221 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s15), slot);
  ghost var va_b17, va_s17 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_ADD(va_b17, va_s17, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset));
  ghost var va_b19, va_s19 := va_lemma_LDRglobal(va_b18, va_s18, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b20, va_s20 := va_lemma_Store(va_b19, va_s19, va_sM, va_op_word_reg(EBP), 1 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b21, va_s21 := va_lemma_MOV_ToReg(va_b20, va_s20, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b22, va_s22 := va_lemma_ADD(va_b21, va_s21, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset));
  ghost var va_b23, va_s23 := va_lemma_LDRglobal(va_b22, va_s22, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b24, va_s24 := va_lemma_Store(va_b23, va_s23, va_sM, va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EDI));
  ghost var va_b26, va_s26 := va_lemma_POP_TwoRegs(va_b25, va_s25, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b27, va_s27 := va_lemma_POP_OneReg(va_b26, va_s26, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s27, va_sM);
}
//--
//-- wimpdrv_ops_get_pid

function method{:opaque} va_code_wimpdrv_ops_get_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_op_cmp_reg(ECX)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDX), va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CNil())))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma_wimpdrv_ops_get_pid(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var out_pid:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), slot) == WS_PartitionID(out_pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 306 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s17), slot);
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b21, va_s21 := va_lemma_LDRglobal(va_b20, va_s20, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_sM);
  ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
    va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
  if (va_cond_c23)
  {
    ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s24, va_s23, va_op_reg_reg(EDX),
      va_op_word_reg(EDI));
    ghost var va_b27, va_s27 := va_lemma_ADD(va_b26, va_s26, va_s23, va_op_word_reg(EDX),
      va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset));
    ghost var va_b28, va_s28 := va_lemma_LDRglobal(va_b27, va_s27, va_s23, va_op_word_reg(EAX),
      G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
    ghost var va_b29, va_s29 := va_lemma_Store(va_b28, va_s28, va_s23, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    ghost var va_b30, va_s30 := va_lemma_Store(va_b29, va_s29, va_s23, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s23 := va_lemma_empty(va_s30, va_s23);
  }
  else
  {
    ghost var va_b31 := va_get_block(va_get_ifFalse(va_c23));
    ghost var va_b32, va_s32 := va_lemma_Store(va_b31, va_s24, va_s23, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s23 := va_lemma_empty(va_s32, va_s23);
  }
  ghost var va_b33, va_s33 := va_lemma_POP_OneReg(va_b23, va_s23, va_sM, va_op_reg_reg(EAX));
  ghost var va_b34, va_s34 := va_lemma_POP_TwoRegs(va_b33, va_s33, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b35, va_s35 := va_lemma_POP_TwoRegs(va_b34, va_s34, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b36, va_s36 := va_lemma_POP_OneReg(va_b35, va_s35, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s36, va_sM);
}
//--
//-- wimpdrv_ops_get_id

function method{:opaque} va_code_wimpdrv_ops_get_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma_wimpdrv_ops_get_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_id:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    wimpdrv_get_id_word(va_get_globals(va_s0), slot) == out_id
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
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
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 398 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s17), slot);
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b21, va_s21 := va_lemma_LDRglobal(va_b20, va_s20, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_Store(va_b21, va_s21, va_sM, va_op_word_reg(EBP), 1 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b23, va_s23 := va_lemma_POP_OneReg(va_b22, va_s22, va_sM, va_op_reg_reg(EAX));
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b23, va_s23, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
//-- wimpdrv_ops_get_pid_nocheck

function method{:opaque} va_code_wimpdrv_ops_get_pid_nocheck():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma_wimpdrv_ops_get_pid_nocheck(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_pid_nocheck(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_pid:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    wimpdrv_get_pid(va_get_globals(va_s0), slot) == WS_PartitionID(out_pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
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
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_pid_nocheck();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 476 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s17), slot);
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset));
  ghost var va_b21, va_s21 := va_lemma_LDRglobal(va_b20, va_s20, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_Store(va_b21, va_s21, va_sM, va_op_word_reg(EBP), 1 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b23, va_s23 := va_lemma_POP_OneReg(va_b22, va_s22, va_sM, va_op_reg_reg(EAX));
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b23, va_s23, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
//-- wimpdrv_ops_get_updateflag

function method{:opaque} va_code_wimpdrv_ops_get_updateflag():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_op_cmp_reg(ECX)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CNil())))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma_wimpdrv_ops_get_updateflag(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_updateflag(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var out_flag:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); ret == TRUE ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), slot) == out_flag
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_updateflag();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 557 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s17), slot);
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b21, va_s21 := va_lemma_LDRglobal(va_b20, va_s20, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_sM);
  ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
    va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
  if (va_cond_c23)
  {
    ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s24, va_s23, va_op_reg_reg(EDX),
      va_op_word_reg(EDI));
    ghost var va_b27, va_s27 := va_lemma_ADD(va_b26, va_s26, va_s23, va_op_word_reg(EDX),
      va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset));
    ghost var va_b28, va_s28 := va_lemma_LDRglobal(va_b27, va_s27, va_s23, va_op_word_reg(EAX),
      G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
    ghost var va_b29, va_s29 := va_lemma_Store(va_b28, va_s28, va_s23, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    ghost var va_b30, va_s30 := va_lemma_Store(va_b29, va_s29, va_s23, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s23 := va_lemma_empty(va_s30, va_s23);
  }
  else
  {
    ghost var va_b31 := va_get_block(va_get_ifFalse(va_c23));
    ghost var va_b32, va_s32 := va_lemma_Store(va_b31, va_s24, va_s23, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s23 := va_lemma_empty(va_s32, va_s23);
  }
  ghost var va_b33, va_s33 := va_lemma_POP_OneReg(va_b23, va_s23, va_sM, va_op_reg_reg(EAX));
  ghost var va_b34, va_s34 := va_lemma_POP_TwoRegs(va_b33, va_s33, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b35, va_s35 := va_lemma_POP_TwoRegs(va_b34, va_s34, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b36, va_s36 := va_lemma_POP_OneReg(va_b35, va_s35, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s36, va_sM);
}
//--
//-- wimpdrv_ops_get_updateflag_nocheck

function method{:opaque} va_code_wimpdrv_ops_get_updateflag_nocheck():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma_wimpdrv_ops_get_updateflag_nocheck(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_ops_get_updateflag_nocheck(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_flag:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    wimpdrv_do_get_flag(va_get_globals(va_s0), slot) == out_flag
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
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
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_wimpdrv_ops_get_updateflag_nocheck();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(EAX));
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 649 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s17), slot);
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset));
  ghost var va_b21, va_s21 := va_lemma_LDRglobal(va_b20, va_s20, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_Store(va_b21, va_s21, va_sM, va_op_word_reg(EBP), 1 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b23, va_s23 := va_lemma_POP_OneReg(va_b22, va_s22, va_sM, va_op_reg_reg(EAX));
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b23, va_s23, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ECX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
//-- wimpdrv_find_slot_in_partition

function method{:opaque} va_code_wimpdrv_find_slot_in_partition():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(WimpDrv_Info_ENTRIES -
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

lemma{:timeLimitMultiplier 5} va_lemma_wimpdrv_find_slot_in_partition(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_wimpdrv_find_slot_in_partition(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 8 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    result_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((ret == TRUE ==>
    wimpdrv_valid_slot_id(result_slot)) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    result_slot) == WS_PartitionID(pid))) && (ret == FALSE ==> (forall i:word ::
    wimpdrv_valid_slot_id(i) ==> wimpdrv_get_pid(va_get_globals(va_s0), i) != WS_PartitionID(pid)))
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
  reveal_va_code_wimpdrv_find_slot_in_partition();
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
  ghost var va_b17, va_s17 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b16, va_s16, va_sM);
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
    invariant 0 <= va_get_reg(EAX, va_sW29) <= WimpDrv_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) <
      WimpDrv_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) != in_pid ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && wimpdrv_valid_slot_id(j) ==> wimpdrv_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: wimpdrv_valid_slot_id(j) ==> wimpdrv_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) == in_pid ||
      va_get_reg(EAX, va_sW29) == WimpDrv_Info_ENTRIES - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) == in_pid ==>
      wimpdrv_valid_slot_id(va_get_reg(EAX, va_sW29)) && wimpdrv_get_pid(va_get_globals(va_old_s),
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
    decreases WimpDrv_Info_ENTRIES - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s29, va_sW30, va_op_word_reg(EAX));
    ghost var va_b33, va_s33 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b32, va_s32, va_sW30);
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
    assert va_get_reg(EAX, va_s52) == WimpDrv_Info_ENTRIES - 1;  // line 819 column 9 of file .\drv/drv_ops_utils.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 820 column 9 of file .\drv/drv_ops_utils.vad
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
//-- _wimpdrv_slot_get_id_pid

function method{:opaque} va_code__wimpdrv_slot_get_id_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(EAX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(ESI), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_ADD(va_op_word_reg(EDI), va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(), va_op_reg_reg(ESI),
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CCons(va_code_LDRglobal(va_op_word_reg(EAX), G_WimpDrvs_Info(),
    va_op_reg_reg(ESI), va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EAX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI),
    va_op_reg_reg(EAX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma__wimpdrv_slot_get_id_pid(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__wimpdrv_slot_get_id_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= slot <
    WimpDrv_Info_ENTRIES
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    wimpdrv_id:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var pid:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    wimpdrv_get_id_word(va_get_globals(va_s0), slot) == wimpdrv_id &&
    wimpdrv_get_pid(va_get_globals(va_s0), slot) == WS_PartitionID(pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code__wimpdrv_slot_get_id_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(ESI),
    G_WimpDrvs_Info());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 897 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_ADD(va_b16, va_s16, va_sM, va_op_word_reg(EDX),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b18, va_s18 := va_lemma_ADD(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset));
  Lemma_wimpdrv_info_slot_in_range_must_be_valid_vaddr(va_get_reg(ESI, va_s18), slot);
  ghost var va_b20, va_s20 := va_lemma_LDRglobal(va_b18, va_s18, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDX));
  ghost var va_b21, va_s21 := va_lemma_Store(va_b20, va_s20, va_sM, va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b22, va_s22 := va_lemma_LDRglobal(va_b21, va_s21, va_sM, va_op_word_reg(EAX),
    G_WimpDrvs_Info(), va_op_reg_reg(ESI), va_op_word_reg(EDI));
  ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s22, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b23, va_s23, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(EAX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDX));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
//-- _wimpdrv_update_slot_pid_to_invalid

function method{:opaque} va_code__wimpdrv_update_slot_pid_to_invalid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset)),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_const_word(WimpDrv_Slot_UpdateFlag_Updating)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI), va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset)),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_const_word(WimpDrv_Slot_UpdateFlag_Complete)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 40} va_lemma__wimpdrv_update_slot_pid_to_invalid(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__wimpdrv_update_slot_pid_to_invalid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 5 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    wimpdrv_valid_slot_id(slot) &&
    usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s0), slot)
  requires var new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    2 * ARCH_WORD_BYTES); var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES); ((new_pid == PID_INVALID &&
    WK_ValidPMemRegion(new_do_pbase, new_do_pend)) && (new_wimpdrv_id == WimpDrv_ID_RESERVED_EMPTY
    ==> new_pid == PID_INVALID)) && new_wimpdrv_id == WimpDrv_ID_RESERVED_EMPTY
  requires var new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    forall i:uint32 :: (wimpdrv_valid_slot_id(i) && i != slot) &&
    wimpdrv_get_id_word(va_get_globals(va_s0), i) != WimpDrv_ID_RESERVED_EMPTY ==>
    wimpdrv_get_id_word(va_get_globals(va_s0), i) != new_wimpdrv_id
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    unregistered_drv_idword := wimpdrv_get_id_word(va_get_globals(va_s0), slot);
    unregistered_drv_idword != WimpDrv_ID_RESERVED_EMPTY
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    unregistered_drv_idword := wimpdrv_get_id_word(va_get_globals(va_s0), slot); var
    unregistered_drv_id := WimpDrv_IDWord_ToDrvID(va_s0.subjects, va_s0.objects, va_s0.id_mappings,
    unregistered_drv_idword); wimpdrv_get_pid(va_get_globals(va_s0), slot) !=
    WS_PartitionID(PID_INVALID) && WSM_IsWimpDrvID(va_s0.subjects, unregistered_drv_id)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    2 * ARCH_WORD_BYTES); var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES); wimpdrv_info_newvalue(va_get_globals(va_s0),
    va_get_globals(va_sM), slot, new_wimpdrv_id, new_pid, new_do_pbase, new_do_pend,
    WimpDrv_Slot_UpdateFlag_Complete)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM,
    va_update_globals(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__wimpdrv_update_slot_pid_to_invalid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_wimpdrv_slot_equal();
  reveal_usbtds_verifiedtds_do_not_associate_wimpdrv();
  ghost var va_b4, va_s4 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b5, va_s5, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b11, va_s11 := va_lemma_PUSH_TwoRegs(va_b10, va_s10, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var orig_esp := va_get_reg(ESP, va_s11);
  ghost var va_b13, va_s13 := va_lemma_LDRglobaladdr_ToReg(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDX), G_WimpDrvs_Info());
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s14);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 1030 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b18, va_s18 := va_lemma_MUL_Reg_32BitsResult(va_b14, va_s14, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  assert va_get_globals(va_s18) == va_get_globals(va_old_s);  // line 1034 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b20, va_s20 := va_lemma_MOV_ToReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_ADD(va_b20, va_s20, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s21) + va_get_reg(ESI, va_s21);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s21), G_WimpDrvs_Info(), tmp_addr1,
    WimpDrv_Slot_UpdateFlag_Updating);
  ghost var new_this1 := va_s21.(wk_mstate := va_s21.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s21),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s21),
    new_globals1);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s21), new_globals1, slot,
    G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset, WimpDrv_Slot_UpdateFlag_Updating);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_HoldIfWrittingUpdateFlagField(va_get_globals(va_s21),
    new_globals1, slot, WimpDrv_Slot_UpdateFlag_Updating);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField(va_get_globals(va_s21),
    new_globals1, slot, WimpDrv_Slot_UpdateFlag_Updating);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_get_globals(va_s21),
    new_globals1, slot);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s21),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s21),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s21),
    new_globals1);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s21),
    new_globals1);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_s21,
    new_this1, new_globals1, slot);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s21,
    new_this1);
  assert ins_valid_strglobal_word(va_s21.subjects, va_s21.objects, va_s21.id_mappings,
    va_s21.objs_addrs, va_s21.activate_conds, va_get_globals(va_s21), G_WimpDrvs_Info(), tmp_addr1,
    WimpDrv_Slot_UpdateFlag_Updating);  // line 1058 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b38, va_s38 := va_lemma_STRglobal(va_b21, va_s21, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_const_word(WimpDrv_Slot_UpdateFlag_Updating));
  ghost var va_b39, va_s39 := va_lemma_MOV_ToReg(va_b38, va_s38, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b40, va_s40 := va_lemma_ADD(va_b39, va_s39, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset));
  ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s40, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var new_pid := va_get_reg(ECX, va_s41);
  ghost var tmp_addr3 := va_get_reg(EDX, va_s41) + va_get_reg(ESI, va_s41);
  ghost var new_globals3 := global_write_word(va_get_globals(va_s41), G_WimpDrvs_Info(), tmp_addr3,
    va_get_reg(ECX, va_s41));
  ghost var new_this3 := va_s41.(wk_mstate := va_s41.wk_mstate.(globals := new_globals3));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s41),
    new_globals3);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s41),
    new_globals3);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s41), new_globals3, slot,
    G_WimpDrv_Info_ENTRY_PID_BytesOffset, va_get_reg(ECX, va_s41));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_NewPIDIsInvalid(va_get_globals(va_s41),
    new_globals3, slot, va_get_reg(ECX, va_s41));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingPIDField(va_get_globals(va_s41),
    new_globals3, slot, va_get_reg(ECX, va_s41));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s41),
    new_globals3);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s41),
    new_globals3);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s41),
    new_globals3);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s41),
    new_globals3);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingPIDField(va_s41, new_this3, new_globals3,
    slot, va_get_reg(ECX, va_s41));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s41,
    new_this3);
  assert ins_valid_strglobal_word(va_s41.subjects, va_s41.objects, va_s41.id_mappings,
    va_s41.objs_addrs, va_s41.activate_conds, va_get_globals(va_s41), G_WimpDrvs_Info(), tmp_addr3,
    va_get_reg(ECX, va_s41));  // line 1088 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b58, va_s58 := va_lemma_STRglobal(va_b41, va_s41, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b59, va_s59 := va_lemma_MOV_ToReg(va_b58, va_s58, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b60, va_s60 := va_lemma_ADD(va_b59, va_s59, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b61, va_s61 := va_lemma_Load(va_b60, va_s60, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var new_wimpdrv_id := va_get_reg(ECX, va_s61);
  ghost var tmp_addr2 := va_get_reg(EDX, va_s61) + va_get_reg(ESI, va_s61);
  ghost var new_globals2 := global_write_word(va_get_globals(va_s61), G_WimpDrvs_Info(), tmp_addr2,
    va_get_reg(ECX, va_s61));
  ghost var new_this2 := va_s61.(wk_mstate := va_s61.wk_mstate.(globals := new_globals2));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s61),
    new_globals2);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s61),
    new_globals2);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s61), new_globals2, slot,
    G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset, va_get_reg(ECX, va_s61));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDrvIDField_PIDIsAlreadyInvalid(va_get_globals(va_s61),
    new_globals2, slot, va_get_reg(ECX, va_s61));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDrvIDField(va_get_globals(va_s61),
    new_globals2, slot, va_get_reg(ECX, va_s61));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s61),
    new_globals2);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s61),
    new_globals2);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s61),
    new_globals2);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s61),
    new_globals2);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDrvIDField(va_s61, new_this2, new_globals2,
    slot, va_get_reg(ECX, va_s61));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s61,
    new_this2);
  assert ins_valid_strglobal_word(va_s61.subjects, va_s61.objects, va_s61.id_mappings,
    va_s61.objs_addrs, va_s61.activate_conds, va_get_globals(va_s61), G_WimpDrvs_Info(), tmp_addr2,
    va_get_reg(ECX, va_s61));  // line 1118 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b78, va_s78 := va_lemma_STRglobal(va_b61, va_s61, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b79, va_s79 := va_lemma_MOV_ToReg(va_b78, va_s78, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b80, va_s80 := va_lemma_ADD(va_b79, va_s79, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset));
  ghost var va_b81, va_s81 := va_lemma_Load(va_b80, va_s80, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
  ghost var new_do_pbase := va_get_reg(ECX, va_s81);
  ghost var tmp_addr4 := va_get_reg(EDX, va_s81) + va_get_reg(ESI, va_s81);
  ghost var new_globals4 := global_write_word(va_get_globals(va_s81), G_WimpDrvs_Info(), tmp_addr4,
    va_get_reg(ECX, va_s81));
  ghost var new_this4 := va_s81.(wk_mstate := va_s81.wk_mstate.(globals := new_globals4));
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s81), new_globals4, slot,
    G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset, va_get_reg(ECX, va_s81));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDOPAddrBaseField(va_get_globals(va_s81),
    new_globals4, slot, va_get_reg(ECX, va_s81));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDOPAddrBaseField_UnderFlagUpdating(va_get_globals(va_s81),
    new_globals4, slot, va_get_reg(ECX, va_s81));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s81),
    new_globals4);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s81),
    new_globals4);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s81),
    new_globals4);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s81),
    new_globals4);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDOPAddrBaseField(va_s81, new_this4,
    new_globals4, slot, va_get_reg(ECX, va_s81));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s81,
    new_this4);
  assert ins_valid_strglobal_word(va_s81.subjects, va_s81.objects, va_s81.id_mappings,
    va_s81.objs_addrs, va_s81.activate_conds, va_get_globals(va_s81), G_WimpDrvs_Info(), tmp_addr4,
    va_get_reg(ECX, va_s81));  // line 1145 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b96, va_s96 := va_lemma_STRglobal(va_b81, va_s81, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b97, va_s97 := va_lemma_MOV_ToReg(va_b96, va_s96, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b98, va_s98 := va_lemma_ADD(va_b97, va_s97, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset));
  ghost var va_b99, va_s99 := va_lemma_Load(va_b98, va_s98, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
  ghost var new_do_pend := va_get_reg(ECX, va_s99);
  ghost var tmp_addr5 := va_get_reg(EDX, va_s99) + va_get_reg(ESI, va_s99);
  ghost var new_globals5 := global_write_word(va_get_globals(va_s99), G_WimpDrvs_Info(), tmp_addr5,
    va_get_reg(ECX, va_s99));
  ghost var new_this5 := va_s99.(wk_mstate := va_s99.wk_mstate.(globals := new_globals5));
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s99), new_globals5, slot,
    G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset, va_get_reg(ECX, va_s99));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDOPAddrEndField(va_get_globals(va_s99),
    new_globals5, slot, va_get_reg(ECX, va_s99));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDOPAddrEndField_UnderFlagUpdating(va_get_globals(va_s99),
    new_globals5, slot, va_get_reg(ECX, va_s99));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s99),
    new_globals5);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s99),
    new_globals5);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s99),
    new_globals5);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s99),
    new_globals5);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDOPAddrEndField(va_s99, new_this5,
    new_globals5, slot, va_get_reg(ECX, va_s99));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s99,
    new_this5);
  assert ins_valid_strglobal_word(va_s99.subjects, va_s99.objects, va_s99.id_mappings,
    va_s99.objs_addrs, va_s99.activate_conds, va_get_globals(va_s99), G_WimpDrvs_Info(), tmp_addr5,
    va_get_reg(ECX, va_s99));  // line 1172 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b114, va_s114 := va_lemma_STRglobal(va_b99, va_s99, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b115, va_s115 := va_lemma_MOV_ToReg(va_b114, va_s114, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b116, va_s116 := va_lemma_ADD(va_b115, va_s115, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset));
  ghost var tmp_addr6 := va_get_reg(EDX, va_s116) + va_get_reg(ESI, va_s116);
  ghost var new_globals6 := global_write_word(va_get_globals(va_s116), G_WimpDrvs_Info(),
    tmp_addr6, WimpDrv_Slot_UpdateFlag_Complete);
  ghost var new_this6 := va_s116.(wk_mstate := va_s116.wk_mstate.(globals := new_globals6));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s116), new_globals6, slot,
    G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset, WimpDrv_Slot_UpdateFlag_Complete);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_HoldIfWrittingUpdateFlagField(va_get_globals(va_s116),
    new_globals6, slot, WimpDrv_Slot_UpdateFlag_Complete);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField(va_get_globals(va_s116),
    new_globals6, slot, WimpDrv_Slot_UpdateFlag_Complete);
  Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(va_get_globals(va_s116),
    new_globals6, slot);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(va_s116,
    new_this6, new_globals6, slot);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s116,
    new_this6);
  assert ins_valid_strglobal_word(va_s116.subjects, va_s116.objects, va_s116.id_mappings,
    va_s116.objs_addrs, va_s116.activate_conds, va_get_globals(va_s116), G_WimpDrvs_Info(),
    tmp_addr6, WimpDrv_Slot_UpdateFlag_Complete);  // line 1201 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b133, va_s133 := va_lemma_STRglobal(va_b116, va_s116, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_const_word(WimpDrv_Slot_UpdateFlag_Complete));
  assert va_get_globals(va_s133) == new_globals6;  // line 1205 column 5 of file .\drv/drv_ops_utils.vad
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingWimpDrvNotAssociatedWithAnyUSBTD(va_get_globals(va_old_s),
    va_get_globals(va_s133), slot);
  Lemma__wimpdrv_update_slot_pid_to_invalid_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s,
    va_s133, slot);
  Lemma_WK_WimpDrvs_UpdateAllFieldsMustSatisfy_wimpdrv_info_newvalue2(va_get_globals(va_old_s),
    va_get_globals(va_s133), slot, new_wimpdrv_id, new_pid, new_do_pbase, new_do_pend,
    new_globals1, new_globals3, new_globals2, new_globals4, new_globals5, new_globals6);
  assert va_get_reg(ESP, va_s133) == orig_esp;  // line 1217 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b139, va_s139 := va_lemma_POP_TwoRegs(va_b133, va_s133, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b140, va_s140 := va_lemma_POP_TwoRegs(va_b139, va_s139, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b141, va_s141 := va_lemma_POP_OneReg(va_b140, va_s140, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s141, va_sM);
}
//--
//-- _wimpdrv_update_slot_pid_to_valid

function method{:opaque} va_code__wimpdrv_update_slot_pid_to_valid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_WimpDrvs_Info()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WimpDrv_Info_ENTRY_SZ)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI),
    va_op_word_reg(EDI)), va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset)),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_const_word(WimpDrv_Slot_UpdateFlag_Updating)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI), va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset)),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_op_word_reg(ECX)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_op_word_reg(EDI)),
    va_CCons(va_code_ADD(va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset)),
    va_CCons(va_code_STRglobal(G_WimpDrvs_Info(), va_op_reg_reg(EDX), va_op_word_reg(ESI),
    va_const_word(WimpDrv_Slot_UpdateFlag_Complete)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 40} va_lemma__wimpdrv_update_slot_pid_to_valid(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__wimpdrv_update_slot_pid_to_valid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 5 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    wimpdrv_valid_slot_id(slot) &&
    usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s0), slot)
  requires var new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    2 * ARCH_WORD_BYTES); var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES); (WS_PartitionID(new_pid) in
    pids_parse_g_wimp_pids(va_get_globals(va_s0)) && WK_ValidPMemRegion(new_do_pbase, new_do_pend))
    && new_wimpdrv_id != WimpDrv_ID_RESERVED_EMPTY
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    2 * ARCH_WORD_BYTES); var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES);
    wimpdrv_registration_info_must_exist(va_s0.subjects, va_s0.objects, va_s0.id_mappings,
    va_s0.objs_addrs, new_wimpdrv_id, new_do_pbase, new_do_pend)
  requires var new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    (forall i:uint32 :: (wimpdrv_valid_slot_id(i) && i != slot) &&
    wimpdrv_get_id_word(va_get_globals(va_s0), i) != WimpDrv_ID_RESERVED_EMPTY ==>
    wimpdrv_get_id_word(va_get_globals(va_s0), i) != new_wimpdrv_id) &&
    wimpdrv_get_id_word(va_get_globals(va_s0), slot) == WimpDrv_ID_RESERVED_EMPTY
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES);
    var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3 *
    ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 4 * ARCH_WORD_BYTES); forall i:uint32 :: (((wimpdrv_valid_slot_id(i) && i != slot) &&
    wimpdrv_do_get_flag(va_get_globals(va_s0), i) == WimpDrv_Slot_UpdateFlag_Complete) &&
    wimpdrv_get_pid(va_get_globals(va_s0), i) != WS_PartitionID(PID_INVALID)) && new_pid !=
    PID_INVALID ==> !(is_mem_region_overlap(wimpdrv_do_get_paddr_base(va_get_globals(va_s0), i),
    wimpdrv_do_get_paddr_end(va_get_globals(va_s0), i), new_do_pbase, new_do_pend))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_wimpdrv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    2 * ARCH_WORD_BYTES); var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES); wimpdrv_info_newvalue(va_get_globals(va_s0),
    va_get_globals(va_sM), slot, new_wimpdrv_id, new_pid, new_do_pbase, new_do_pend,
    WimpDrv_Slot_UpdateFlag_Complete)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM,
    va_update_globals(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__wimpdrv_update_slot_pid_to_valid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_usbtds_verifiedtds_do_not_associate_wimpdrv();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b4, va_s4, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var orig_esp := va_get_reg(ESP, va_s10);
  ghost var va_b12, va_s12 := va_lemma_LDRglobaladdr_ToReg(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDX), G_WimpDrvs_Info());
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WimpDrv_Info_ENTRY_SZ, WimpDrv_Info_ENTRIES, WimpDrv_Info_ENTRY_SZ);
  assert isUInt32(slot * WimpDrv_Info_ENTRY_SZ);  // line 1339 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WimpDrv_Info_ENTRY_SZ));
  assert va_get_globals(va_s17) == va_get_globals(va_old_s);  // line 1343 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b17, va_s17, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s20) + va_get_reg(ESI, va_s20);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s20), G_WimpDrvs_Info(), tmp_addr1,
    WimpDrv_Slot_UpdateFlag_Updating);
  ghost var new_this1 := va_s20.(wk_mstate := va_s20.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s20),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s20),
    new_globals1);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s20), new_globals1, slot,
    G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset, WimpDrv_Slot_UpdateFlag_Updating);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_HoldIfWrittingUpdateFlagField(va_get_globals(va_s20),
    new_globals1, slot, WimpDrv_Slot_UpdateFlag_Updating);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField(va_get_globals(va_s20),
    new_globals1, slot, WimpDrv_Slot_UpdateFlag_Updating);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_get_globals(va_s20),
    new_globals1, slot);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s20),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s20),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s20),
    new_globals1);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s20),
    new_globals1);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(va_s20,
    new_this1, new_globals1, slot);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s20,
    new_this1);
  assert ins_valid_strglobal_word(va_s20.subjects, va_s20.objects, va_s20.id_mappings,
    va_s20.objs_addrs, va_s20.activate_conds, va_get_globals(va_s20), G_WimpDrvs_Info(), tmp_addr1,
    WimpDrv_Slot_UpdateFlag_Updating);  // line 1367 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b37, va_s37 := va_lemma_STRglobal(va_b20, va_s20, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_const_word(WimpDrv_Slot_UpdateFlag_Updating));
  ghost var va_b38, va_s38 := va_lemma_MOV_ToReg(va_b37, va_s37, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b39, va_s39 := va_lemma_ADD(va_b38, va_s38, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset));
  ghost var va_b40, va_s40 := va_lemma_Load(va_b39, va_s39, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var new_wimpdrv_id := va_get_reg(ECX, va_s40);
  ghost var tmp_addr2 := va_get_reg(EDX, va_s40) + va_get_reg(ESI, va_s40);
  ghost var new_globals2 := global_write_word(va_get_globals(va_s40), G_WimpDrvs_Info(), tmp_addr2,
    va_get_reg(ECX, va_s40));
  ghost var new_this2 := va_s40.(wk_mstate := va_s40.wk_mstate.(globals := new_globals2));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s40),
    new_globals2);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s40),
    new_globals2);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s40), new_globals2, slot,
    G_WimpDrv_Info_ENTRY_DrvIDWord_BytesOffset, va_get_reg(ECX, va_s40));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDrvIDField_NonEmptyWimpDrvID(va_get_globals(va_s40),
    new_globals2, slot, va_get_reg(ECX, va_s40));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDrvIDField(va_get_globals(va_s40),
    new_globals2, slot, va_get_reg(ECX, va_s40));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s40),
    new_globals2);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s40),
    new_globals2);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s40),
    new_globals2);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s40),
    new_globals2);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDrvIDField(va_s40, new_this2, new_globals2,
    slot, va_get_reg(ECX, va_s40));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s40,
    new_this2);
  assert ins_valid_strglobal_word(va_s40.subjects, va_s40.objects, va_s40.id_mappings,
    va_s40.objs_addrs, va_s40.activate_conds, va_get_globals(va_s40), G_WimpDrvs_Info(), tmp_addr2,
    va_get_reg(ECX, va_s40));  // line 1397 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b57, va_s57 := va_lemma_STRglobal(va_b40, va_s40, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b58, va_s58 := va_lemma_MOV_ToReg(va_b57, va_s57, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b59, va_s59 := va_lemma_ADD(va_b58, va_s58, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_PID_BytesOffset));
  ghost var va_b60, va_s60 := va_lemma_Load(va_b59, va_s59, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var new_pid := va_get_reg(ECX, va_s60);
  ghost var tmp_addr3 := va_get_reg(EDX, va_s60) + va_get_reg(ESI, va_s60);
  ghost var new_globals3 := global_write_word(va_get_globals(va_s60), G_WimpDrvs_Info(), tmp_addr3,
    va_get_reg(ECX, va_s60));
  ghost var new_this3 := va_s60.(wk_mstate := va_s60.wk_mstate.(globals := new_globals3));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s60),
    new_globals3);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s60),
    new_globals3);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s60), new_globals3, slot,
    G_WimpDrv_Info_ENTRY_PID_BytesOffset, va_get_reg(ECX, va_s60));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_WimpDrvAlreadyNotEmpty(va_get_globals(va_s60),
    new_globals3, slot, va_get_reg(ECX, va_s60));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingPIDField(va_get_globals(va_s60),
    new_globals3, slot, va_get_reg(ECX, va_s60));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s60),
    new_globals3);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s60),
    new_globals3);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s60),
    new_globals3);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s60),
    new_globals3);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingPIDField(va_s60, new_this3, new_globals3,
    slot, va_get_reg(ECX, va_s60));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s60,
    new_this3);
  assert ins_valid_strglobal_word(va_s60.subjects, va_s60.objects, va_s60.id_mappings,
    va_s60.objs_addrs, va_s60.activate_conds, va_get_globals(va_s60), G_WimpDrvs_Info(), tmp_addr3,
    va_get_reg(ECX, va_s60));  // line 1427 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b77, va_s77 := va_lemma_STRglobal(va_b60, va_s60, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b78, va_s78 := va_lemma_MOV_ToReg(va_b77, va_s77, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b79, va_s79 := va_lemma_ADD(va_b78, va_s78, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset));
  ghost var va_b80, va_s80 := va_lemma_Load(va_b79, va_s79, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
  ghost var new_do_pbase := va_get_reg(ECX, va_s80);
  ghost var tmp_addr4 := va_get_reg(EDX, va_s80) + va_get_reg(ESI, va_s80);
  ghost var new_globals4 := global_write_word(va_get_globals(va_s80), G_WimpDrvs_Info(), tmp_addr4,
    va_get_reg(ECX, va_s80));
  ghost var new_this4 := va_s80.(wk_mstate := va_s80.wk_mstate.(globals := new_globals4));
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s80), new_globals4, slot,
    G_WimpDrv_Info_ENTRY_DO_PBase_BytesOffset, va_get_reg(ECX, va_s80));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDOPAddrBaseField(va_get_globals(va_s80),
    new_globals4, slot, va_get_reg(ECX, va_s80));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDOPAddrBaseField_UnderFlagUpdating(va_get_globals(va_s80),
    new_globals4, slot, va_get_reg(ECX, va_s80));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s80),
    new_globals4);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s80),
    new_globals4);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s80),
    new_globals4);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s80),
    new_globals4);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDOPAddrBaseField(va_s80, new_this4,
    new_globals4, slot, va_get_reg(ECX, va_s80));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s80,
    new_this4);
  assert ins_valid_strglobal_word(va_s80.subjects, va_s80.objects, va_s80.id_mappings,
    va_s80.objs_addrs, va_s80.activate_conds, va_get_globals(va_s80), G_WimpDrvs_Info(), tmp_addr4,
    va_get_reg(ECX, va_s80));  // line 1454 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b95, va_s95 := va_lemma_STRglobal(va_b80, va_s80, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  ghost var va_b96, va_s96 := va_lemma_MOV_ToReg(va_b95, va_s95, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b97, va_s97 := va_lemma_ADD(va_b96, va_s96, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset));
  ghost var va_b98, va_s98 := va_lemma_Load(va_b97, va_s97, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
  ghost var new_do_pend := va_get_reg(ECX, va_s98);
  ghost var tmp_addr5 := va_get_reg(EDX, va_s98) + va_get_reg(ESI, va_s98);
  ghost var new_globals5 := global_write_word(va_get_globals(va_s98), G_WimpDrvs_Info(), tmp_addr5,
    va_get_reg(ECX, va_s98));
  ghost var new_this5 := va_s98.(wk_mstate := va_s98.wk_mstate.(globals := new_globals5));
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s98), new_globals5, slot,
    G_WimpDrv_Info_ENTRY_DO_PEnd_BytesOffset, va_get_reg(ECX, va_s98));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingDOPAddrEndField(va_get_globals(va_s98),
    new_globals5, slot, va_get_reg(ECX, va_s98));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingDOPAddrEndField_UnderFlagUpdating(va_get_globals(va_s98),
    new_globals5, slot, va_get_reg(ECX, va_s98));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s98),
    new_globals5);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s98),
    new_globals5);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s98),
    new_globals5);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s98),
    new_globals5);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingDOPAddrEndField(va_s98, new_this5,
    new_globals5, slot, va_get_reg(ECX, va_s98));
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s98,
    new_this5);
  assert ins_valid_strglobal_word(va_s98.subjects, va_s98.objects, va_s98.id_mappings,
    va_s98.objs_addrs, va_s98.activate_conds, va_get_globals(va_s98), G_WimpDrvs_Info(), tmp_addr5,
    va_get_reg(ECX, va_s98));  // line 1481 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b113, va_s113 := va_lemma_STRglobal(va_b98, va_s98, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_op_word_reg(ECX));
  reveal_wimpdrv_registration_info_must_exist();
  ghost var va_b115, va_s115 := va_lemma_MOV_ToReg(va_b113, va_s113, va_sM, va_op_reg_reg(ESI),
    va_op_word_reg(EDI));
  ghost var va_b116, va_s116 := va_lemma_ADD(va_b115, va_s115, va_sM, va_op_word_reg(ESI),
    va_const_word(G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset));
  ghost var tmp_addr6 := va_get_reg(EDX, va_s116) + va_get_reg(ESI, va_s116);
  ghost var new_globals6 := global_write_word(va_get_globals(va_s116), G_WimpDrvs_Info(),
    tmp_addr6, WimpDrv_Slot_UpdateFlag_Complete);
  ghost var new_this6 := va_s116.(wk_mstate := va_s116.wk_mstate.(globals := new_globals6));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WimpDrv_PreserveOtherSlotsIfModifyingOneSlot(va_get_globals(va_s116), new_globals6, slot,
    G_WimpDrv_Info_ENTRY_AccessFlag_BytesOffset, WimpDrv_Slot_UpdateFlag_Complete);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_HoldIfWrittingUpdateFlagField(va_get_globals(va_s116),
    new_globals6, slot, WimpDrv_Slot_UpdateFlag_Complete);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField(va_get_globals(va_s116),
    new_globals6, slot, WimpDrv_Slot_UpdateFlag_Complete);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(va_get_globals(va_s116),
    new_globals6, slot);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s116),
    new_globals6);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s116),
    new_globals6);
  assert va_s116.objects == va_old_s.objects;  // line 1509 column 5 of file .\drv/drv_ops_utils.vad
  reveal_p_wimpdrv_slot_equal();
  ghost var wimpdrv_idword := wimpdrv_get_id_word(new_globals6, slot);
  ghost var wimpdrv_id := WimpDrv_IDWord_ToDrvID(va_old_s.subjects, va_old_s.objects,
    va_old_s.id_mappings, wimpdrv_idword);
  Lemma_wimpdrv_in_system_ProveItsDOMustBeInSystem(va_old_s, wimpdrv_id);
  Lemma__wimpdrv_update_slot_pid_to_valid_Prove_WK_ValidObjAddrs_WimpDrv_DOPAddrs_HoldIfWrittingUpdateFlagField_WriteToComplete(va_s116,
    new_this6, new_globals6, slot, new_do_pbase, new_do_pend);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s116,
    new_this6);
  assert ins_valid_strglobal_word(va_s116.subjects, va_s116.objects, va_s116.id_mappings,
    va_s116.objs_addrs, va_s116.activate_conds, va_get_globals(va_s116), G_WimpDrvs_Info(),
    tmp_addr6, WimpDrv_Slot_UpdateFlag_Complete);  // line 1517 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b138, va_s138 := va_lemma_STRglobal(va_b116, va_s116, va_sM, G_WimpDrvs_Info(),
    va_op_reg_reg(EDX), va_op_word_reg(ESI), va_const_word(WimpDrv_Slot_UpdateFlag_Complete));
  assert va_get_globals(va_s138) == new_globals6;  // line 1521 column 5 of file .\drv/drv_ops_utils.vad
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingWimpDrvNotAssociatedWithAnyUSBTD(va_get_globals(va_old_s),
    va_get_globals(va_s138), slot);
  Lemma__wimpdrv_update_slot_pid_to_valid_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s, va_s138,
    slot, new_do_pbase, new_do_pend);
  Lemma_WK_WimpDrvs_UpdateAllFieldsMustSatisfy_wimpdrv_info_newvalue1(va_get_globals(va_old_s),
    va_get_globals(va_s138), slot, new_wimpdrv_id, new_pid, new_do_pbase, new_do_pend,
    new_globals1, new_globals2, new_globals3, new_globals4, new_globals5, new_globals6);
  assert va_get_reg(ESP, va_s138) == orig_esp;  // line 1533 column 5 of file .\drv/drv_ops_utils.vad
  ghost var va_b144, va_s144 := va_lemma_POP_TwoRegs(va_b138, va_s138, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b145, va_s145 := va_lemma_POP_TwoRegs(va_b144, va_s144, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b146, va_s146 := va_lemma_POP_OneReg(va_b145, va_s145, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s146, va_sM);
}
//--
//-- _wimpdrv_find_slot_by_id

function method{:opaque} va_code__wimpdrv_find_slot_by_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_wimpdrv_ops_get_id(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_wimpdrv_ops_get_id(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(WimpDrv_Info_ENTRIES -
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

lemma{:timeLimitMultiplier 10} va_lemma__wimpdrv_find_slot_by_id(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__wimpdrv_find_slot_by_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 8 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    result_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((ret == TRUE ==>
    wimpdrv_valid_slot_id(result_slot)) && (ret == TRUE ==>
    wimpdrv_get_id_word(va_get_globals(va_s0), result_slot) == id)) && (ret == FALSE ==> (forall
    i:word :: wimpdrv_valid_slot_id(i) ==> wimpdrv_get_id_word(va_get_globals(va_s0), i) != id))
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
  reveal_va_code__wimpdrv_find_slot_by_id();
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
  ghost var va_b17, va_s17 := va_lemma_wimpdrv_ops_get_id(va_b16, va_s16, va_sM);
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
    invariant 0 <= va_get_reg(EAX, va_sW29) <= WimpDrv_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) <
      WimpDrv_Info_ENTRIES
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) != in_id ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && wimpdrv_valid_slot_id(j) ==> wimpdrv_get_id_word(va_get_globals(va_old_s), j) !=
      in_id)
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: wimpdrv_valid_slot_id(j) ==> wimpdrv_get_id_word(va_get_globals(va_old_s), j) !=
      in_id)
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) == in_id ||
      va_get_reg(EAX, va_sW29) == WimpDrv_Info_ENTRIES - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) == in_id ==>
      wimpdrv_valid_slot_id(va_get_reg(EAX, va_sW29)) &&
      wimpdrv_get_id_word(va_get_globals(va_old_s), va_get_reg(EAX, va_sW29)) == in_id
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
    decreases WimpDrv_Info_ENTRIES - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s29, va_sW30, va_op_word_reg(EAX));
    ghost var va_b33, va_s33 := va_lemma_wimpdrv_ops_get_id(va_b32, va_s32, va_sW30);
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
    assert va_get_reg(EAX, va_s52) == WimpDrv_Info_ENTRIES - 1;  // line 1690 column 9 of file .\drv/drv_ops_utils.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 1691 column 9 of file .\drv/drv_ops_utils.vad
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
// Predicate: When registering a wimp driver, The given information must match the information in <subjs>, <objs>, 
// <id_mappings>, and <objs_addrs>, as they store all wimp drivers that will be activated in the system
predicate {:opaque} wimpdrv_registration_info_must_exist(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, objs_addrs:WSM_Objects_Addrs,
    new_wimpdrv_id:word, new_do_pbase:word, new_do_pend:uint
)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
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

    requires new_wimpdrv_id != WimpDrv_ID_RESERVED_EMPTY
    requires WK_ValidPMemRegion(new_do_pbase, new_do_pend)
{
    var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, new_wimpdrv_id);
    WSM_IsWimpDrvID(subjs, drv_id) &&
        // Requirement: As <subjs> and <objs> have given all wimp drivers to be loaded and their DO's
        // information, <new_wimpdrv_id> must map to some wimp driver's ID
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(subjs, objs, id_mappings, new_wimpdrv_id);
    (forall pmem :: pmem in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ==> (new_do_pbase == pmem.paddr_start && new_do_pend == pmem.paddr_end)) &&
        // Requirement: As <subjs> and <objs> have given all wimp drivers to be loaded and their DO's
        // information, <new_do_pbase> and <new_do_pend> must match these information
    WimpDrvDO_MemRegionSeparateFromAllActiveOSObjs(objs, objs_addrs, new_do_pbase, new_do_pend)
        // Requirement: As the wimp driver will be active after registration, then <new_do_pbase> and <new_do_pend> must 
        // be separate from all active OS objects
}
