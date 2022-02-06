include "ins_wrapper.gen.dfy"
//-- impl_is_valid_addr

function method{:opaque} va_code_impl_is_valid_addr(base:va_operand_reg, ofs:va_operand_word,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(4294967295)),
    va_CCons(va_code_SUB(va_coerce_reg_to_word(ret), va_coerce_reg_to_word(base)),
    va_CCons(va_IfElse(va_cmp_le(va_coerce_word_to_cmp(ofs), va_coerce_reg_to_cmp(ret)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(TRUE)), va_CNil())),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))), va_CNil()))))
}

lemma va_lemma_impl_is_valid_addr(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  base:va_operand_reg, ofs:va_operand_word, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_impl_is_valid_addr(base, ofs, ret), va_s0, va_sN)
  requires va_is_src_reg(base, va_s0)
  requires va_is_src_word(ofs, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires base != OReg(ESP)
  requires ofs != OReg(ESP)
  requires ret != OReg(ESP)
  requires base != ret
  requires ofs != ret
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> is_valid_addr(va_eval_reg(va_sM, base) +
    va_eval_word(va_sM, ofs))
  ensures  va_eval_reg(va_sM, base) == va_eval_reg(va_s0, base)
  ensures  va_eval_word(va_sM, ofs) == va_eval_word(va_s0, ofs)
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_impl_is_valid_addr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_MOV_ToReg(va_b1, va_s0, va_sM, ret, va_const_word(4294967295));
  ghost var va_b3, va_s3 := va_lemma_SUB(va_b2, va_s2, va_sM, va_coerce_reg_to_word(ret),
    va_coerce_reg_to_word(base));
  ghost var va_s4, va_c4, va_b4 := va_lemma_block(va_b3, va_s3, va_sM);
  ghost var va_cond_c4, va_s5:va_state := va_lemma_ifElse(va_get_ifCond(va_c4),
    va_get_ifTrue(va_c4), va_get_ifFalse(va_c4), va_s3, va_s4);
  if (va_cond_c4)
  {
    ghost var va_b6 := va_get_block(va_get_ifTrue(va_c4));
    ghost var va_b7, va_s7 := va_lemma_MOV_ToReg(va_b6, va_s5, va_s4, ret, va_const_word(TRUE));
    va_s4 := va_lemma_empty(va_s7, va_s4);
  }
  else
  {
    ghost var va_b8 := va_get_block(va_get_ifFalse(va_c4));
    ghost var va_b9, va_s9 := va_lemma_MOV_ToReg(va_b8, va_s5, va_s4, ret, va_const_word(FALSE));
    va_s4 := va_lemma_empty(va_s9, va_s4);
  }
  va_sM := va_lemma_empty(va_s4, va_sM);
}
//--
