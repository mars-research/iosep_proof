include "ins.gen.dfy"
//-- PUSH_VOID

function method{:opaque} va_code_PUSH_VOID(n:constop):va_code
{
  va_Block(va_CCons(va_code_SUB(va_op_word_reg(ESP), va_const_word(n)), va_CNil()))
}

lemma va_lemma_PUSH_VOID(va_b0:va_codes, va_s0:va_state, va_sN:va_state, n:constop)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_PUSH_VOID(n), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires n % ARCH_WORD_BYTES == 0
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires isWord(va_get_reg(ESP, va_s0) - n)
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - n)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var stack_new_top1 := va_get_reg(ESP, va_s0) - n; va_get_reg(ESP, va_sM) ==
    stack_new_top1
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_s0))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_s0))))
{
  reveal_va_code_PUSH_VOID();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_SUB(va_b1, va_s0, va_sM, va_op_word_reg(ESP),
    va_const_word(n));
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- PUSH_IMM

function method{:opaque} va_code_PUSH_IMM(imm:constop):va_code
{
  va_Block(va_CCons(va_code_PUSH(va_const_word(imm)), va_CNil()))
}

lemma va_lemma_PUSH_IMM(va_b0:va_codes, va_s0:va_state, va_sN:va_state, imm:constop)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_PUSH_IMM(imm), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - 1 * ARCH_WORD_BYTES)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var stack_new_top1 := va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES; var mem1 :=
    stack_set_val(va_get_mem(va_s0), stack_new_top1, imm); (va_get_mem(va_sM) == mem1 &&
    va_get_reg(ESP, va_sM) == stack_new_top1) && imm == stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_sM))
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_s0))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_s0))))
{
  reveal_va_code_PUSH_IMM();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH(va_b1, va_s0, va_sM, va_const_word(imm));
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- PUSH_OneReg

function method{:opaque} va_code_PUSH_OneReg(reg1:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH(va_coerce_reg_to_word(reg1)), va_CNil()))
}

lemma va_lemma_PUSH_OneReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state, reg1:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_PUSH_OneReg(reg1), va_s0, va_sN)
  requires va_is_src_reg(reg1, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires reg1 != OReg(ESP)
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - 1 * ARCH_WORD_BYTES)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var stack_new_top1 := va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES; var mem1 :=
    stack_set_val(va_get_mem(va_s0), stack_new_top1, va_eval_reg(va_s0, reg1)); (va_get_mem(va_sM)
    == mem1 && va_get_reg(ESP, va_sM) == stack_new_top1) && va_eval_reg(va_sM, reg1) ==
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  va_eval_reg(va_sM, reg1) == va_eval_reg(va_s0, reg1)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_s0))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_s0))))
{
  reveal_va_code_PUSH_OneReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH(va_b1, va_s0, va_sM, va_coerce_reg_to_word(reg1));
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- PUSH_TwoRegs

function method{:opaque} va_code_PUSH_TwoRegs(reg1:va_operand_reg, reg2:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH(va_coerce_reg_to_word(reg1)),
    va_CCons(va_code_PUSH(va_coerce_reg_to_word(reg2)), va_CNil())))
}

lemma va_lemma_PUSH_TwoRegs(va_b0:va_codes, va_s0:va_state, va_sN:va_state, reg1:va_operand_reg,
  reg2:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_PUSH_TwoRegs(reg1, reg2), va_s0, va_sN)
  requires va_is_src_reg(reg1, va_s0)
  requires va_is_src_reg(reg2, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires reg1 != OReg(ESP)
  requires reg2 != OReg(ESP)
  requires reg1 != reg2
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - 2 * ARCH_WORD_BYTES)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var stack_new_top1 := va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES; var stack_new_top2 :=
    va_get_reg(ESP, va_s0) - 2 * ARCH_WORD_BYTES; var mem1 := stack_set_val(va_get_mem(va_s0),
    stack_new_top1, va_eval_reg(va_s0, reg1)); var mem2 := stack_set_val(mem1, stack_new_top2,
    va_eval_reg(va_s0, reg2)); ((va_get_mem(va_sM) == mem2 && va_get_reg(ESP, va_sM) ==
    stack_new_top2) && va_eval_reg(va_sM, reg2) == stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_sM))) && va_eval_reg(va_sM, reg1) == stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)
    + ARCH_WORD_BYTES)
  ensures  va_eval_reg(va_sM, reg1) == va_eval_reg(va_s0, reg1)
  ensures  va_eval_reg(va_sM, reg2) == va_eval_reg(va_s0, reg2)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_s0))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_s0))))
{
  reveal_va_code_PUSH_TwoRegs();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH(va_b1, va_s0, va_sM, va_coerce_reg_to_word(reg1));
  ghost var va_b3, va_s3 := va_lemma_PUSH(va_b2, va_s2, va_sM, va_coerce_reg_to_word(reg2));
  va_sM := va_lemma_empty(va_s3, va_sM);
}
//--
//-- PUSH_Reg1ToReg6

function method{:opaque} va_code_PUSH_Reg1ToReg6():va_code
{
  va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CNil())))))))
}

lemma va_lemma_PUSH_Reg1ToReg6(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_PUSH_Reg1ToReg6(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - 6 * ARCH_WORD_BYTES)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var stack_new_top1 := va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES; var stack_new_top2 :=
    va_get_reg(ESP, va_s0) - 2 * ARCH_WORD_BYTES; var stack_new_top3 := va_get_reg(ESP, va_s0) - 3
    * ARCH_WORD_BYTES; var stack_new_top4 := va_get_reg(ESP, va_s0) - 4 * ARCH_WORD_BYTES; var
    stack_new_top5 := va_get_reg(ESP, va_s0) - 5 * ARCH_WORD_BYTES; var stack_new_top6 :=
    va_get_reg(ESP, va_s0) - 6 * ARCH_WORD_BYTES; var mem1 := stack_set_val(va_get_mem(va_s0),
    stack_new_top1, va_get_reg(EAX, va_s0)); var mem2 := stack_set_val(mem1, stack_new_top2,
    va_get_reg(EBX, va_s0)); var mem3 := stack_set_val(mem2, stack_new_top3, va_get_reg(ECX,
    va_s0)); var mem4 := stack_set_val(mem3, stack_new_top4, va_get_reg(EDX, va_s0)); var mem5 :=
    stack_set_val(mem4, stack_new_top5, va_get_reg(ESI, va_s0)); var mem6 := stack_set_val(mem5,
    stack_new_top6, va_get_reg(EDI, va_s0)); ((((((va_get_mem(va_sM) == mem6 && va_get_reg(ESP,
    va_sM) == stack_new_top6) && va_get_reg(EDI, va_sM) == stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_sM))) && va_get_reg(ESI, va_sM) == stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_sM) + 1 * ARCH_WORD_BYTES)) && va_get_reg(EDX, va_sM) ==
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM) + 2 * ARCH_WORD_BYTES)) &&
    va_get_reg(ECX, va_sM) == stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM) + 3 *
    ARCH_WORD_BYTES)) && va_get_reg(EBX, va_sM) == stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_sM) + 4 * ARCH_WORD_BYTES)) && va_get_reg(EAX, va_sM) == stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_sM) + 5 * ARCH_WORD_BYTES)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_s0))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_s0))))
{
  reveal_va_code_PUSH_Reg1ToReg6();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH(va_b1, va_s0, va_sM, va_op_word_reg(EAX));
  ghost var va_b3, va_s3 := va_lemma_PUSH(va_b2, va_s2, va_sM, va_op_word_reg(EBX));
  ghost var va_b4, va_s4 := va_lemma_PUSH(va_b3, va_s3, va_sM, va_op_word_reg(ECX));
  ghost var va_b5, va_s5 := va_lemma_PUSH(va_b4, va_s4, va_sM, va_op_word_reg(EDX));
  ghost var va_b6, va_s6 := va_lemma_PUSH(va_b5, va_s5, va_sM, va_op_word_reg(ESI));
  ghost var va_b7, va_s7 := va_lemma_PUSH(va_b6, va_s6, va_sM, va_op_word_reg(EDI));
  va_sM := va_lemma_empty(va_s7, va_sM);
}
//--
//-- POP_VOID

function method{:opaque} va_code_POP_VOID(n:constop):va_code
{
  va_Block(va_CCons(va_code_ADD(va_op_word_reg(ESP), va_const_word(n)), va_CNil()))
}

lemma va_lemma_POP_VOID(va_b0:va_codes, va_s0:va_state, va_sN:va_state, n:constop)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_POP_VOID(n), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires n % ARCH_WORD_BYTES == 0
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires isWord(va_get_reg(ESP, va_s0) + n)
  requires IsAddrInStack(va_get_reg(ESP, va_s0) + n)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0) + n
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM, va_s0)))
{
  reveal_va_code_POP_VOID();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_ADD(va_b1, va_s0, va_sM, va_op_word_reg(ESP),
    va_const_word(n));
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- POP_OneReg

function method{:opaque} va_code_POP_OneReg(reg1:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_POP(reg1), va_CNil()))
}

lemma va_lemma_POP_OneReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state, reg1:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_POP_OneReg(reg1), va_s0, va_sN)
  requires va_is_dst_reg(reg1, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  requires reg1 != OReg(ESP)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES
  ensures  va_eval_reg(va_sM, reg1) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0))
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_update_operand_reg(reg1, va_sM, va_s0))))
{
  reveal_va_code_POP_OneReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_POP(va_b1, va_s0, va_sM, reg1);
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- POP_TwoRegs

function method{:opaque} va_code_POP_TwoRegs(reg1:va_operand_reg, reg2:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_POP(reg2), va_CCons(va_code_POP(reg1), va_CNil())))
}

lemma va_lemma_POP_TwoRegs(va_b0:va_codes, va_s0:va_state, va_sN:va_state, reg1:va_operand_reg,
  reg2:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_POP_TwoRegs(reg1, reg2), va_s0, va_sN)
  requires va_is_dst_reg(reg1, va_s0)
  requires va_is_dst_reg(reg2, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  requires reg1 != OReg(ESP)
  requires reg2 != OReg(ESP)
  requires reg1 != reg2
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES
  ensures  va_eval_reg(va_sM, reg2) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0))
  ensures  va_eval_reg(va_sM, reg1) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES)
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_update_operand_reg(reg2, va_sM, va_update_operand_reg(reg1, va_sM, va_s0)))))
{
  reveal_va_code_POP_TwoRegs();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_POP(va_b1, va_s0, va_sM, reg2);
  ghost var va_b3, va_s3 := va_lemma_POP(va_b2, va_s2, va_sM, reg1);
  va_sM := va_lemma_empty(va_s3, va_sM);
}
//--
//-- POP_Reg1ToReg6

function method{:opaque} va_code_POP_Reg1ToReg6():va_code
{
  va_Block(va_CCons(va_code_POP(va_op_reg_reg(EDI)), va_CCons(va_code_POP(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP(va_op_reg_reg(EDX)), va_CCons(va_code_POP(va_op_reg_reg(ECX)),
    va_CCons(va_code_POP(va_op_reg_reg(EBX)), va_CCons(va_code_POP(va_op_reg_reg(EAX)),
    va_CNil())))))))
}

lemma va_lemma_POP_Reg1ToReg6(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_POP_Reg1ToReg6(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES
  ensures  va_get_reg(EDI, va_sM) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0))
  ensures  va_get_reg(ESI, va_sM) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES)
  ensures  va_get_reg(EDX, va_sM) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES)
  ensures  va_get_reg(ECX, va_sM) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3 *
    ARCH_WORD_BYTES)
  ensures  va_get_reg(EBX, va_sM) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 4 *
    ARCH_WORD_BYTES)
  ensures  va_get_reg(EAX, va_sM) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 5 *
    ARCH_WORD_BYTES)
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_POP_Reg1ToReg6();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_POP(va_b1, va_s0, va_sM, va_op_reg_reg(EDI));
  ghost var va_b3, va_s3 := va_lemma_POP(va_b2, va_s2, va_sM, va_op_reg_reg(ESI));
  ghost var va_b4, va_s4 := va_lemma_POP(va_b3, va_s3, va_sM, va_op_reg_reg(EDX));
  ghost var va_b5, va_s5 := va_lemma_POP(va_b4, va_s4, va_sM, va_op_reg_reg(ECX));
  ghost var va_b6, va_s6 := va_lemma_POP(va_b5, va_s5, va_sM, va_op_reg_reg(EBX));
  ghost var va_b7, va_s7 := va_lemma_POP(va_b6, va_s6, va_sM, va_op_reg_reg(EAX));
  va_sM := va_lemma_empty(va_s7, va_sM);
}
//--
//-- MOV_ToReg

function method{:opaque} va_code_MOV_ToReg(dst:va_operand_reg, src:va_operand_word):va_code
{
  va_Block(va_CCons(va_code_MOV(va_coerce_reg_to_word(dst), src), va_CNil()))
}

lemma va_lemma_MOV_ToReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_reg,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_MOV_ToReg(dst, src), va_s0, va_sN)
  requires va_is_dst_reg(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires var v := va_eval_word(va_s0, src); ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, dst) == va_eval_word(va_s0, src)
  ensures  stack_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(dst, va_sM, va_s0)))
{
  reveal_va_code_MOV_ToReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_MOV(va_b1, va_s0, va_sM, va_coerce_reg_to_word(dst), src);
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- LDRglobaladdr_ToReg

function method{:opaque} va_code_LDRglobaladdr_ToReg(dst:va_operand_reg, g:symbol):va_code
{
  va_Block(va_CCons(va_code_LDRglobaladdr(va_coerce_reg_to_word(dst), g), va_CNil()))
}

lemma va_lemma_LDRglobaladdr_ToReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  dst:va_operand_reg, g:symbol)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_LDRglobaladdr_ToReg(dst, g), va_s0, va_sN)
  requires va_is_dst_reg(dst, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires dst != OReg(ESP)
  requires is_gvar_exist(g)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, dst) == AddressOfGlobal(g)
  ensures  stack_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(dst, va_sM, va_s0)))
{
  reveal_va_code_LDRglobaladdr_ToReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_LDRglobaladdr(va_b1, va_s0, va_sM, va_coerce_reg_to_word(dst),
    g);
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- ADD_SHL_ToReg

function method{:opaque} va_code_ADD_SHL_ToReg(dst:va_operand_reg, src1:va_operand_reg,
  shl1:va_operand_reg, bits:constop):va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_coerce_reg_to_word(shl1)),
    va_CCons(va_code_SHL(va_op_word_reg(ESI), va_const_word(bits)),
    va_CCons(va_code_MOV(va_coerce_reg_to_word(dst), va_coerce_reg_to_word(src1)),
    va_CCons(va_code_ADD(va_coerce_reg_to_word(dst), va_op_word_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)), va_CNil())))))))
}

lemma va_lemma_ADD_SHL_ToReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_reg,
  src1:va_operand_reg, shl1:va_operand_reg, bits:constop)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_ADD_SHL_ToReg(dst, src1, shl1, bits), va_s0, va_sN)
  requires va_is_dst_reg(dst, va_s0)
  requires va_is_src_reg(src1, va_s0)
  requires va_is_src_reg(shl1, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires dst != src1
  requires dst != shl1
  requires dst != OReg(ESP)
  requires src1 != OReg(ESP)
  requires shl1 != OReg(ESP)
  requires dst != Reg5
  requires src1 != Reg5
  requires shl1 != Reg5
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES)
  requires 0 <= bits < Ins_Shift_Max
  requires isWord(va_eval_reg(va_s0, src1) + LeftShift(va_eval_reg(va_s0, shl1), bits))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, dst) == va_eval_reg(va_s0, src1) + LeftShift(va_eval_reg(va_s0,
    shl1), bits)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_ok(va_sM, va_update_operand_reg(dst, va_sM, va_s0))))))
{
  reveal_va_code_ADD_SHL_ToReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(ESI));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_coerce_reg_to_word(shl1));
  ghost var va_b5, va_s5 := va_lemma_SHL(va_b4, va_s4, va_sM, va_op_word_reg(ESI),
    va_const_word(bits));
  ghost var va_b6, va_s6 := va_lemma_MOV(va_b5, va_s5, va_sM, va_coerce_reg_to_word(dst),
    va_coerce_reg_to_word(src1));
  ghost var va_b7, va_s7 := va_lemma_ADD(va_b6, va_s6, va_sM, va_coerce_reg_to_word(dst),
    va_op_word_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_POP_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  va_sM := va_lemma_empty(va_s8, va_sM);
}
//--
//-- MUL_Reg_32BitsResult

function method{:opaque} va_code_MUL_Reg_32BitsResult(reg1:va_operand_reg,
  src:va_operand_word):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_coerce_reg_to_word(reg1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), src), va_CCons(va_code_MUL(va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(reg1, va_op_word_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EDX)), va_CNil())))))))
}

lemma va_lemma_MUL_Reg_32BitsResult(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  reg1:va_operand_reg, src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_MUL_Reg_32BitsResult(reg1, src), va_s0, va_sN)
  requires va_is_dst_reg(reg1, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires reg1 != OReg(ESP)
  requires reg1 != Reg1
  requires reg1 != Reg4
  requires src != OReg(ESP)
  requires src != Reg1
  requires src != Reg4
  requires var stack_req_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space)
  requires isUInt32(va_eval_reg(va_s0, reg1) * va_eval_word(va_s0, src))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, reg1) == va_eval_reg(va_s0, reg1) * va_eval_word(va_s0, src)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EDX,
    va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM, va_update_operand_reg(reg1, va_sM,
    va_s0)))))))
{
  reveal_va_code_MUL_Reg_32BitsResult();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  Lemma_MulUin32UpperBound();
  ghost var va_b3, va_s3 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EDX));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_coerce_reg_to_word(reg1));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EDX), src);
  ghost var va_b6, va_s6 := va_lemma_MUL(va_b5, va_s5, va_sM, va_op_word_reg(EDX));
  ghost var va_b7, va_s7 := va_lemma_MOV_ToReg(va_b6, va_s6, va_sM, reg1, va_op_word_reg(EAX));
  ghost var va_b8, va_s8 := va_lemma_POP_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EDX));
  va_sM := va_lemma_empty(va_s8, va_sM);
}
//--
//-- SetBit

function method{:opaque} va_code_SetBit(dst:va_operand_word, bit_pos:constop):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(1)),
    va_CCons(va_code_SHL(va_op_word_reg(ESI), va_const_word(bit_pos)), va_CCons(va_code_OR(dst,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CNil()))))))
}

lemma va_lemma_SetBit(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  bit_pos:constop)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_SetBit(dst, bit_pos), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires 0 <= bit_pos < 32
  requires dst != Reg5
  requires dst != Reg3
  requires dst != OReg(ESP)
  requires var stack_req_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == SetBit(va_eval_word(va_s0, dst), bit_pos)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(ECX,
    va_sM, va_update_reg(ESI, va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM,
    va_s0)))))))
{
  reveal_va_code_SetBit();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b4, va_s4 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(ESI),
    va_const_word(1));
  ghost var va_b6, va_s6 := va_lemma_SHL(va_b5, va_s5, va_sM, va_op_word_reg(ESI),
    va_const_word(bit_pos));
  ghost var va_b7, va_s7 := va_lemma_OR(va_b6, va_s6, va_sM, dst, va_op_word_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_POP_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  va_sM := va_lemma_empty(va_s8, va_sM);
}
//--
//-- ClearBit

function method{:opaque} va_code_ClearBit(dst:va_operand_word, bit_pos:constop):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(1)),
    va_CCons(va_code_SHL(va_op_word_reg(ESI), va_const_word(bit_pos)),
    va_CCons(va_code_NOT(va_op_word_reg(ESI)), va_CCons(va_code_AND(dst, va_op_word_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)), va_CNil())))))))
}

lemma va_lemma_ClearBit(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  bit_pos:constop)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_ClearBit(dst, bit_pos), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires 0 <= bit_pos < 32
  requires dst != Reg5
  requires dst != Reg3
  requires dst != OReg(ESP)
  requires var stack_req_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == ClearBit(va_eval_word(va_s0, dst), bit_pos)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(ECX,
    va_sM, va_update_reg(ESI, va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM,
    va_s0)))))))
{
  reveal_va_code_ClearBit();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b4, va_s4 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(ESI),
    va_const_word(1));
  ghost var va_b6, va_s6 := va_lemma_SHL(va_b5, va_s5, va_sM, va_op_word_reg(ESI),
    va_const_word(bit_pos));
  ghost var va_b7, va_s7 := va_lemma_NOT(va_b6, va_s6, va_sM, va_op_word_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_AND(va_b7, va_s7, va_sM, dst, va_op_word_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_POP_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  va_sM := va_lemma_empty(va_s9, va_sM);
}
//--
//-- TestBit

function method{:opaque} va_code_TestBit(v:va_operand_word, bit_pos:constop,
  result:va_operand_word):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(1)),
    va_CCons(va_code_SHL(va_op_word_reg(ESI), va_const_word(bit_pos)),
    va_CCons(va_code_MOV_ToReg(va_coerce_word_to_reg(result), v), va_CCons(va_code_AND(result,
    va_op_word_reg(ESI)), va_CCons(va_IfElse(va_cmp_ne(va_coerce_word_to_cmp(result),
    va_const_cmp(0)), va_Block(va_CCons(va_code_MOV_ToReg(va_coerce_word_to_reg(result),
    va_const_word(TRUE)), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(va_coerce_word_to_reg(result), va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CNil()))))))))
}

lemma va_lemma_TestBit(va_b0:va_codes, va_s0:va_state, va_sN:va_state, v:va_operand_word,
  bit_pos:constop, result:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_TestBit(v, bit_pos, result), va_s0, va_sN)
  requires va_is_src_word(v, va_s0)
  requires va_is_dst_word(result, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires 0 <= bit_pos < 32
  requires result != v
  requires v != Reg3
  requires result != Reg3
  requires v != Reg5
  requires result != Reg5
  requires v != OReg(ESP)
  requires result != OReg(ESP)
  requires v != OReg(EBP)
  requires result != OReg(EBP)
  requires var stack_req_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  0 <= bit_pos < 32
  ensures  va_eval_word(va_sM, result) == TRUE <==> TestBit(va_eval_word(va_sM, v), bit_pos)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(ECX,
    va_sM, va_update_reg(ESI, va_sM, va_update_ok(va_sM, va_update_operand_word(result, va_sM,
    va_s0)))))))
{
  reveal_va_code_TestBit();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b4, va_s4 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(ESI),
    va_const_word(1));
  ghost var va_b6, va_s6 := va_lemma_SHL(va_b5, va_s5, va_sM, va_op_word_reg(ESI),
    va_const_word(bit_pos));
  ghost var va_b7, va_s7 := va_lemma_MOV_ToReg(va_b6, va_s6, va_sM, va_coerce_word_to_reg(result),
    v);
  ghost var va_b8, va_s8 := va_lemma_AND(va_b7, va_s7, va_sM, result, va_op_word_reg(ESI));
  ghost var va_s9, va_c9, va_b9 := va_lemma_block(va_b8, va_s8, va_sM);
  ghost var va_cond_c9, va_s10:va_state := va_lemma_ifElse(va_get_ifCond(va_c9),
    va_get_ifTrue(va_c9), va_get_ifFalse(va_c9), va_s8, va_s9);
  if (va_cond_c9)
  {
    ghost var va_b11 := va_get_block(va_get_ifTrue(va_c9));
    ghost var va_b12, va_s12 := va_lemma_MOV_ToReg(va_b11, va_s10, va_s9,
      va_coerce_word_to_reg(result), va_const_word(TRUE));
    va_s9 := va_lemma_empty(va_s12, va_s9);
  }
  else
  {
    ghost var va_b13 := va_get_block(va_get_ifFalse(va_c9));
    ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b13, va_s10, va_s9,
      va_coerce_word_to_reg(result), va_const_word(FALSE));
    va_s9 := va_lemma_empty(va_s14, va_s9);
  }
  ghost var va_b15, va_s15 := va_lemma_POP_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  va_sM := va_lemma_empty(va_s15, va_sM);
}
//--
