include "../../../ins/x86/ins_utils.gen.dfy"
include "..\\..\\..\\wk_ops_commons.dfy"
include "..\\usb_def.dfy"
include "..\\eehci.s.dfy"
include "..\\usb_tds.s.dfy"
include "usb_tds_checks.s.dfy"
include "../../../drv/drv_ops_utils.gen.dfy"
include "../usb_tds_utils.gen.dfy"
include "..\\usb.i.dfy"
//-- usbtd_verify_td32_check_databuf_in_paddr_range
//--
//-- usbtd_check_buf_region

function method{:opaque} va_code_usbtd_check_buf_region():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ECX), va_op_reg_reg(EDX)),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EAX), va_op_cmp_reg(EBX)),
    va_Block(va_CCons(va_IfElse(va_cmp_le(va_op_cmp_reg(EAX), va_op_cmp_reg(ECX)),
    va_Block(va_CCons(va_IfElse(va_cmp_le(va_op_cmp_reg(ECX), va_const_cmp(ADDR_SPACE_UPPER -
    PAGE_4K_SZ)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_op_word_reg(ECX)),
    va_CCons(va_code_ADD(va_op_word_reg(EDX), va_const_word(PAGE_4K_SZ)),
    va_CCons(va_IfElse(va_cmp_le(va_op_cmp_reg(EDX), va_op_cmp_reg(EBX)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ECX), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))
}

lemma va_lemma_usbtd_check_buf_region(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_check_buf_region(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 3 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var wimpdrv_do_pbase:paddr := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var wimpdrv_do_pend:paddr := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var buf_pbase:paddr := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); wimpdrv_do_pbase <= wimpdrv_do_pend
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_do_pbase:paddr := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var wimpdrv_do_pend:paddr := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var buf_pbase:paddr := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var out_ret:word := stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_s0)); (out_ret == TRUE ==> is_valid_addr(buf_pbase + PAGE_4K_SZ)) &&
    (out_ret == TRUE ==> is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, buf_pbase,
    buf_pbase + PAGE_4K_SZ))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_check_buf_region();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(ECX),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_s13, va_c13, va_b13 := va_lemma_block(va_b12, va_s12, va_sM);
  ghost var va_cond_c13, va_s14:va_state := va_lemma_ifElse(va_get_ifCond(va_c13),
    va_get_ifTrue(va_c13), va_get_ifFalse(va_c13), va_s12, va_s13);
  if (va_cond_c13)
  {
    ghost var va_b15 := va_get_block(va_get_ifTrue(va_c13));
    ghost var va_s16, va_c16, va_b16 := va_lemma_block(va_b15, va_s14, va_s13);
    ghost var va_cond_c16, va_s17:va_state := va_lemma_ifElse(va_get_ifCond(va_c16),
      va_get_ifTrue(va_c16), va_get_ifFalse(va_c16), va_s14, va_s16);
    if (va_cond_c16)
    {
      ghost var va_b18 := va_get_block(va_get_ifTrue(va_c16));
      ghost var va_s19, va_c19, va_b19 := va_lemma_block(va_b18, va_s17, va_s16);
      ghost var va_cond_c19, va_s20:va_state := va_lemma_ifElse(va_get_ifCond(va_c19),
        va_get_ifTrue(va_c19), va_get_ifFalse(va_c19), va_s17, va_s19);
      if (va_cond_c19)
      {
        ghost var va_b21 := va_get_block(va_get_ifTrue(va_c19));
        ghost var va_b22, va_s22 := va_lemma_MOV_ToReg(va_b21, va_s20, va_s19, va_op_reg_reg(EDX),
          va_op_word_reg(ECX));
        ghost var va_b23, va_s23 := va_lemma_ADD(va_b22, va_s22, va_s19, va_op_word_reg(EDX),
          va_const_word(PAGE_4K_SZ));
        ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b23, va_s23, va_s19);
        ghost var va_cond_c24, va_s25:va_state := va_lemma_ifElse(va_get_ifCond(va_c24),
          va_get_ifTrue(va_c24), va_get_ifFalse(va_c24), va_s23, va_s24);
        if (va_cond_c24)
        {
          ghost var va_b26 := va_get_block(va_get_ifTrue(va_c24));
          ghost var va_b27, va_s27 := va_lemma_Store(va_b26, va_s25, va_s24, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          va_s24 := va_lemma_empty(va_s27, va_s24);
        }
        else
        {
          ghost var va_b28 := va_get_block(va_get_ifFalse(va_c24));
          ghost var va_b29, va_s29 := va_lemma_Store(va_b28, va_s25, va_s24, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          va_s24 := va_lemma_empty(va_s29, va_s24);
        }
        va_s19 := va_lemma_empty(va_s24, va_s19);
      }
      else
      {
        ghost var va_b30 := va_get_block(va_get_ifFalse(va_c19));
        ghost var va_b31, va_s31 := va_lemma_Store(va_b30, va_s20, va_s19, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        va_s19 := va_lemma_empty(va_s31, va_s19);
      }
      va_s16 := va_lemma_empty(va_s19, va_s16);
    }
    else
    {
      ghost var va_b32 := va_get_block(va_get_ifFalse(va_c16));
      ghost var va_b33, va_s33 := va_lemma_Store(va_b32, va_s17, va_s16, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s16 := va_lemma_empty(va_s33, va_s16);
    }
    va_s13 := va_lemma_empty(va_s16, va_s13);
  }
  else
  {
    ghost var va_b34 := va_get_block(va_get_ifFalse(va_c13));
    ghost var va_b35, va_s35 := va_lemma_Store(va_b34, va_s14, va_s13, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s13 := va_lemma_empty(va_s35, va_s13);
  }
  ghost var va_b36, va_s36 := va_lemma_POP_TwoRegs(va_b13, va_s13, va_sM, va_op_reg_reg(ECX),
    va_op_reg_reg(EDX));
  ghost var va_b37, va_s37 := va_lemma_POP_TwoRegs(va_b36, va_s36, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- usbtd_verify_td32_check_next_slot_and_tflag

function method{:opaque}
  va_code_usbtd_verify_td32_check_next_slot_and_tflag(drv_pid:va_operand_reg, flag:va_operand_reg,
  next_slot:va_operand_reg, ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_ne(va_coerce_reg_to_cmp(flag), va_const_cmp(1)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_coerce_reg_to_word(next_slot)),
    va_CCons(va_code_usbtd_check_and_get_td_pid(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_coerce_reg_to_cmp(drv_pid)),
    va_Block(va_CCons(va_code_PUSH(va_coerce_reg_to_word(next_slot)),
    va_CCons(va_code_usbtd_check_flags_slotsecure(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(TRUE)), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil())))))),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))),
    va_CNil())))))))), va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(TRUE)), va_CNil()))),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ECX), va_op_reg_reg(EAX)), va_CNil()))))
}

lemma va_lemma_usbtd_verify_td32_check_next_slot_and_tflag(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state, drv_pid:va_operand_reg, flag:va_operand_reg, next_slot:va_operand_reg,
  ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_verify_td32_check_next_slot_and_tflag(drv_pid, flag,
    next_slot, ret), va_s0, va_sN)
  requires va_is_src_reg(drv_pid, va_s0)
  requires va_is_src_reg(flag, va_s0)
  requires va_is_src_reg(next_slot, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 2 * ARCH_WORD_BYTES + 10 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires drv_pid == Reg5
  requires flag == Reg6
  requires next_slot == Reg4
  requires ret == Reg2
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> va_eval_reg(va_s0, flag) == 1 || ((0 <=
    va_eval_reg(va_s0, next_slot) < USB_TD_ENTRY_NUM && usbtd_map_get_pid(va_get_globals(va_s0),
    va_eval_reg(va_s0, next_slot)) == WS_PartitionID(va_eval_reg(va_s0, drv_pid))) &&
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), va_eval_reg(va_s0, next_slot)),
    USBTD_SLOT_FLAG_SlotSecure_Bit))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0))))))))))))
{
  reveal_va_code_usbtd_verify_td32_check_next_slot_and_tflag();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b4, va_s4 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(ECX),
    va_op_reg_reg(EAX));
  ghost var va_s5, va_c5, va_b5 := va_lemma_block(va_b4, va_s4, va_sM);
  ghost var va_cond_c5, va_s6:va_state := va_lemma_ifElse(va_get_ifCond(va_c5),
    va_get_ifTrue(va_c5), va_get_ifFalse(va_c5), va_s4, va_s5);
  if (va_cond_c5)
  {
    ghost var va_b7 := va_get_block(va_get_ifTrue(va_c5));
    ghost var va_b8, va_s8 := va_lemma_PUSH_VOID(va_b7, va_s6, va_s5, 1 * ARCH_WORD_BYTES);
    ghost var va_b9, va_s9 := va_lemma_PUSH(va_b8, va_s8, va_s5, va_coerce_reg_to_word(next_slot));
    ghost var va_b10, va_s10 := va_lemma_usbtd_check_and_get_td_pid(va_b9, va_s9, va_s5);
    ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_s5, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_s5, va_op_word_reg(EAX),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_s5, 2 * ARCH_WORD_BYTES);
    ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_s5);
    ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
      va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
    if (va_cond_c14)
    {
      ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
      assert usbtd_map_valid_slot_id(va_eval_reg(va_s15, next_slot));  // line 192 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
      ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b16, va_s15, va_s14);
      ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
        va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s15, va_s18);
      if (va_cond_c18)
      {
        ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
        ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18,
          va_coerce_reg_to_word(next_slot));
        ghost var va_b22, va_s22 := va_lemma_usbtd_check_flags_slotsecure(va_b21, va_s21, va_s18);
        ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(ECX),
          va_op_word_reg(ESP), 0);
        ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
        ghost var va_s25, va_c25, va_b25 := va_lemma_block(va_b24, va_s24, va_s18);
        ghost var va_cond_c25, va_s26:va_state := va_lemma_ifElse(va_get_ifCond(va_c25),
          va_get_ifTrue(va_c25), va_get_ifFalse(va_c25), va_s24, va_s25);
        if (va_cond_c25)
        {
          ghost var va_b27 := va_get_block(va_get_ifTrue(va_c25));
          ghost var va_b28, va_s28 := va_lemma_MOV_ToReg(va_b27, va_s26, va_s25, ret,
            va_const_word(TRUE));
          va_s25 := va_lemma_empty(va_s28, va_s25);
        }
        else
        {
          ghost var va_b29 := va_get_block(va_get_ifFalse(va_c25));
          ghost var va_b30, va_s30 := va_lemma_MOV_ToReg(va_b29, va_s26, va_s25, ret,
            va_const_word(FALSE));
          va_s25 := va_lemma_empty(va_s30, va_s25);
        }
        va_s18 := va_lemma_empty(va_s25, va_s18);
      }
      else
      {
        ghost var va_b31 := va_get_block(va_get_ifFalse(va_c18));
        ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s19, va_s18, ret,
          va_const_word(FALSE));
        va_s18 := va_lemma_empty(va_s32, va_s18);
      }
      va_s14 := va_lemma_empty(va_s18, va_s14);
    }
    else
    {
      ghost var va_b33 := va_get_block(va_get_ifFalse(va_c14));
      ghost var va_b34, va_s34 := va_lemma_MOV_ToReg(va_b33, va_s15, va_s14, ret,
        va_const_word(FALSE));
      va_s14 := va_lemma_empty(va_s34, va_s14);
    }
    va_s5 := va_lemma_empty(va_s14, va_s5);
  }
  else
  {
    ghost var va_b35 := va_get_block(va_get_ifFalse(va_c5));
    ghost var va_b36, va_s36 := va_lemma_MOV_ToReg(va_b35, va_s6, va_s5, ret, va_const_word(TRUE));
    va_s5 := va_lemma_empty(va_s36, va_s5);
  }
  ghost var va_b37, va_s37 := va_lemma_POP_TwoRegs(va_b5, va_s5, va_sM, va_op_reg_reg(ECX),
    va_op_reg_reg(EAX));
  va_sM := va_lemma_empty(va_s37, va_sM);
}
//--
//-- usbtd_verify_td32_Check5BufPAddrRange

function method{:opaque} va_code_usbtd_verify_td32_Check5BufPAddrRange():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EAX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_const_word(TRUE)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_verify_td32_check_databuf_in_paddr_range(va_op_reg_reg(ESI),
    va_op_reg_reg(EDX), va_op_reg_reg(EDI)), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(TRUE)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CNil())),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_verify_td32_check_databuf_in_paddr_range(va_op_reg_reg(ESI),
    va_op_reg_reg(EDX), va_op_reg_reg(EDI)), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(TRUE)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CNil())),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_verify_td32_check_databuf_in_paddr_range(va_op_reg_reg(ESI),
    va_op_reg_reg(EDX), va_op_reg_reg(EDI)), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(TRUE)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CNil())),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_verify_td32_check_databuf_in_paddr_range(va_op_reg_reg(ESI),
    va_op_reg_reg(EDX), va_op_reg_reg(EDI)), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(TRUE)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CNil())),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_verify_td32_check_databuf_in_paddr_range(va_op_reg_reg(ESI),
    va_op_reg_reg(EDX), va_op_reg_reg(EDI)), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(TRUE)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CNil())),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX),
    va_op_reg_reg(EAX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 60} va_lemma_usbtd_verify_td32_Check5BufPAddrRange(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_verify_td32_Check5BufPAddrRange(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 5 * ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 7 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var do_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 5 *
    ARCH_WORD_BYTES); var do_pend := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 6 *
    ARCH_WORD_BYTES); do_pbase <= do_pend
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var buf0_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    buf1_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    var buf2_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var buf3_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3
    * ARCH_WORD_BYTES); var buf4_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    4 * ARCH_WORD_BYTES); var do_pbase := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    5 * ARCH_WORD_BYTES); var do_pend := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    6 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM));
    ((((ret == TRUE ==> is_valid_addr(buf0_pbase + PAGE_4K_SZ) && is_mem_region_inside(do_pbase,
    do_pend, buf0_pbase, buf0_pbase + PAGE_4K_SZ)) && (ret == TRUE ==> is_valid_addr(buf1_pbase +
    PAGE_4K_SZ) && is_mem_region_inside(do_pbase, do_pend, buf1_pbase, buf1_pbase + PAGE_4K_SZ)))
    && (ret == TRUE ==> is_valid_addr(buf2_pbase + PAGE_4K_SZ) && is_mem_region_inside(do_pbase,
    do_pend, buf2_pbase, buf2_pbase + PAGE_4K_SZ))) && (ret == TRUE ==> is_valid_addr(buf3_pbase +
    PAGE_4K_SZ) && is_mem_region_inside(do_pbase, do_pend, buf3_pbase, buf3_pbase + PAGE_4K_SZ)))
    && (ret == TRUE ==> is_valid_addr(buf4_pbase + PAGE_4K_SZ) && is_mem_region_inside(do_pbase,
    do_pend, buf4_pbase, buf4_pbase + PAGE_4K_SZ))
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_params_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_params_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_usbtd_verify_td32_Check5BufPAddrRange();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDI));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EAX),
    va_const_word(TRUE));
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES);
  ghost var do_pbase := va_get_reg(EDX, va_s13);
  ghost var do_pend := va_get_reg(EDI, va_s13);
  assert do_pbase <= do_pend;  // line 310 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
  ghost var va_b17, va_s17 := va_lemma_usbtd_verify_td32_check_databuf_in_paddr_range(va_b13,
    va_s13, va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDX), va_op_reg_reg(EDI));
  ghost var test_buf0_pbase := va_get_reg(ESI, va_s17);
  ghost var va_s19, va_c19, va_b19 := va_lemma_block(va_b17, va_s17, va_sM);
  ghost var va_cond_c19, va_s20:va_state := va_lemma_ifElse(va_get_ifCond(va_c19),
    va_get_ifTrue(va_c19), va_get_ifFalse(va_c19), va_s17, va_s19);
  if (va_cond_c19)
  {
    ghost var va_b21 := va_get_block(va_get_ifTrue(va_c19));
    ghost var va_b22, va_s22 := va_lemma_MOV_ToReg(va_b21, va_s20, va_s19, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s19 := va_lemma_empty(va_s22, va_s19);
  }
  else
  {
    ghost var va_b23 := va_get_block(va_get_ifFalse(va_c19));
    va_s19 := va_lemma_empty(va_s20, va_s19);
  }
  ghost var va_b24, va_s24 := va_lemma_Load(va_b19, va_s19, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b25, va_s25 := va_lemma_usbtd_verify_td32_check_databuf_in_paddr_range(va_b24,
    va_s24, va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDX), va_op_reg_reg(EDI));
  ghost var test_buf1_pbase := va_get_reg(ESI, va_s25);
  ghost var va_s27, va_c27, va_b27 := va_lemma_block(va_b25, va_s25, va_sM);
  ghost var va_cond_c27, va_s28:va_state := va_lemma_ifElse(va_get_ifCond(va_c27),
    va_get_ifTrue(va_c27), va_get_ifFalse(va_c27), va_s25, va_s27);
  if (va_cond_c27)
  {
    ghost var va_b29 := va_get_block(va_get_ifTrue(va_c27));
    ghost var va_b30, va_s30 := va_lemma_MOV_ToReg(va_b29, va_s28, va_s27, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s27 := va_lemma_empty(va_s30, va_s27);
  }
  else
  {
    ghost var va_b31 := va_get_block(va_get_ifFalse(va_c27));
    va_s27 := va_lemma_empty(va_s28, va_s27);
  }
  ghost var va_b32, va_s32 := va_lemma_Load(va_b27, va_s27, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b33, va_s33 := va_lemma_usbtd_verify_td32_check_databuf_in_paddr_range(va_b32,
    va_s32, va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDX), va_op_reg_reg(EDI));
  ghost var test_buf2_pbase := va_get_reg(ESI, va_s33);
  ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b33, va_s33, va_sM);
  ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
    va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s33, va_s35);
  if (va_cond_c35)
  {
    ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
    ghost var va_b38, va_s38 := va_lemma_MOV_ToReg(va_b37, va_s36, va_s35, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s35 := va_lemma_empty(va_s38, va_s35);
  }
  else
  {
    ghost var va_b39 := va_get_block(va_get_ifFalse(va_c35));
    va_s35 := va_lemma_empty(va_s36, va_s35);
  }
  ghost var va_b40, va_s40 := va_lemma_Load(va_b35, va_s35, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
  ghost var va_b41, va_s41 := va_lemma_usbtd_verify_td32_check_databuf_in_paddr_range(va_b40,
    va_s40, va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDX), va_op_reg_reg(EDI));
  ghost var test_buf3_pbase := va_get_reg(ESI, va_s41);
  ghost var va_s43, va_c43, va_b43 := va_lemma_block(va_b41, va_s41, va_sM);
  ghost var va_cond_c43, va_s44:va_state := va_lemma_ifElse(va_get_ifCond(va_c43),
    va_get_ifTrue(va_c43), va_get_ifFalse(va_c43), va_s41, va_s43);
  if (va_cond_c43)
  {
    ghost var va_b45 := va_get_block(va_get_ifTrue(va_c43));
    ghost var va_b46, va_s46 := va_lemma_MOV_ToReg(va_b45, va_s44, va_s43, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s43 := va_lemma_empty(va_s46, va_s43);
  }
  else
  {
    ghost var va_b47 := va_get_block(va_get_ifFalse(va_c43));
    va_s43 := va_lemma_empty(va_s44, va_s43);
  }
  ghost var va_b48, va_s48 := va_lemma_Load(va_b43, va_s43, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
  ghost var va_b49, va_s49 := va_lemma_usbtd_verify_td32_check_databuf_in_paddr_range(va_b48,
    va_s48, va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDX), va_op_reg_reg(EDI));
  ghost var test_buf4_pbase := va_get_reg(ESI, va_s49);
  ghost var va_s51, va_c51, va_b51 := va_lemma_block(va_b49, va_s49, va_sM);
  ghost var va_cond_c51, va_s52:va_state := va_lemma_ifElse(va_get_ifCond(va_c51),
    va_get_ifTrue(va_c51), va_get_ifFalse(va_c51), va_s49, va_s51);
  if (va_cond_c51)
  {
    ghost var va_b53 := va_get_block(va_get_ifTrue(va_c51));
    ghost var va_b54, va_s54 := va_lemma_MOV_ToReg(va_b53, va_s52, va_s51, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s51 := va_lemma_empty(va_s54, va_s51);
  }
  else
  {
    ghost var va_b55 := va_get_block(va_get_ifFalse(va_c51));
    va_s51 := va_lemma_empty(va_s52, va_s51);
  }
  ghost var va_s56, va_c56, va_b56 := va_lemma_block(va_b51, va_s51, va_sM);
  ghost var va_cond_c56, va_s57:va_state := va_lemma_ifElse(va_get_ifCond(va_c56),
    va_get_ifTrue(va_c56), va_get_ifFalse(va_c56), va_s51, va_s56);
  if (va_cond_c56)
  {
    ghost var va_b58 := va_get_block(va_get_ifTrue(va_c56));
    ghost var va_b59, va_s59 := va_lemma_Store(va_b58, va_s57, va_s56, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    assert test_buf0_pbase == TRUE;  // line 366 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
    assert test_buf1_pbase == TRUE;  // line 367 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
    assert test_buf2_pbase == TRUE;  // line 368 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
    assert test_buf3_pbase == TRUE;  // line 369 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
    assert test_buf4_pbase == TRUE;  // line 370 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
    va_s56 := va_lemma_empty(va_s59, va_s56);
  }
  else
  {
    ghost var va_b65 := va_get_block(va_get_ifFalse(va_c56));
    ghost var va_b66, va_s66 := va_lemma_Store(va_b65, va_s57, va_s56, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s56 := va_lemma_empty(va_s66, va_s56);
  }
  ghost var va_b67, va_s67 := va_lemma_POP_TwoRegs(va_b56, va_s56, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EAX));
  ghost var va_b68, va_s68 := va_lemma_POP_TwoRegs(va_b67, va_s67, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDI));
  ghost var va_b69, va_s69 := va_lemma_POP_OneReg(va_b68, va_s68, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s69, va_sM);
}
//--
//-- usbtd_verify_td32_check_databuf_in_paddr_range

function method{:opaque}
  va_code_usbtd_verify_td32_check_databuf_in_paddr_range(tmp1:va_operand_reg,
  do_pbase:va_operand_reg, do_pend:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH(va_coerce_reg_to_word(tmp1)),
    va_CCons(va_code_PUSH(va_coerce_reg_to_word(do_pend)),
    va_CCons(va_code_PUSH(va_coerce_reg_to_word(do_pbase)),
    va_CCons(va_code_usbtd_check_buf_region(), va_CCons(va_code_Load(va_coerce_reg_to_word(tmp1),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CNil())))))))
}

lemma va_lemma_usbtd_verify_td32_check_databuf_in_paddr_range(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state, tmp1:va_operand_reg, do_pbase:va_operand_reg, do_pend:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_verify_td32_check_databuf_in_paddr_range(tmp1, do_pbase,
    do_pend), va_s0, va_sN)
  requires va_is_dst_reg(tmp1, va_s0)
  requires va_is_src_reg(do_pbase, va_s0)
  requires va_is_src_reg(do_pend, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
  requires tmp1 == Reg5
  requires do_pbase == Reg4
  requires do_pend == Reg6
  requires va_eval_reg(va_s0, do_pbase) <= va_eval_reg(va_s0, do_pend)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var buf_pbase := va_eval_reg(va_s0, tmp1); var ret:word := va_eval_reg(va_sM, tmp1);
    va_eval_reg(va_sM, do_pbase) <= va_eval_reg(va_sM, do_pend) && (va_eval_reg(va_sM, tmp1) ==
    TRUE ==> is_valid_addr(buf_pbase + PAGE_4K_SZ) && is_mem_region_inside(va_eval_reg(va_sM,
    do_pbase), va_eval_reg(va_sM, do_pend), buf_pbase, buf_pbase + PAGE_4K_SZ))
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_update_operand_reg(tmp1, va_sM, va_s0))))))))))))
{
  reveal_va_code_usbtd_verify_td32_check_databuf_in_paddr_range();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH(va_b1, va_s0, va_sM, va_coerce_reg_to_word(tmp1));
  ghost var buf_pbase := va_eval_reg(va_s2, tmp1);
  ghost var va_b4, va_s4 := va_lemma_PUSH(va_b2, va_s2, va_sM, va_coerce_reg_to_word(do_pend));
  ghost var va_b5, va_s5 := va_lemma_PUSH(va_b4, va_s4, va_sM, va_coerce_reg_to_word(do_pbase));
  ghost var va_b6, va_s6 := va_lemma_usbtd_check_buf_region(va_b5, va_s5, va_sM);
  ghost var va_b7, va_s7 := va_lemma_Load(va_b6, va_s6, va_sM, va_coerce_reg_to_word(tmp1),
    va_op_word_reg(ESP), 0);
  ghost var va_b8, va_s8 := va_lemma_POP_VOID(va_b7, va_s7, va_sM, 3 * ARCH_WORD_BYTES);
  if (va_eval_reg(va_s8, tmp1) == TRUE)
  {
    assert is_valid_addr(buf_pbase + PAGE_4K_SZ);  // line 442 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
    assert is_mem_region_inside(va_eval_reg(va_s8, do_pbase), va_eval_reg(va_s8, do_pend),
      buf_pbase, buf_pbase + PAGE_4K_SZ);  // line 443 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks.vad
  }
  va_sM := va_lemma_empty(va_s8, va_sM);
}
//--
