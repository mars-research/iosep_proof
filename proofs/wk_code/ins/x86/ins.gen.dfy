include "..\\..\\arch\\headers.dfy"
include "..\\..\\mm\\headers.dfy"
include "valesupp.i.dfy"
include "..\\util\\ffi.i.dfy"
include "..\\..\\mhv\\mhv.ffi.i.dfy"
// Interface realization: <Reg1 ... Reg6>
const Reg1:operand := OReg(EAX);
const Reg2:operand := OReg(EBX);
const Reg3:operand := OReg(ECX);
const Reg4:operand := OReg(EDX);
const Reg5:operand := OReg(ESI);
const Reg6:operand := OReg(EDI);

const Ins_Shift_Max:int := ARCH_Ins_SHIFT_MAX;

function MaybeUpdateOk(s:va_state, r:va_state) : va_state
{
    if !(s.ok && r.ok) then s.(ok := false) else r
}
//-- AND

function method{:opaque} va_code_AND(dst:va_operand_word, src:va_operand_word):va_code
{
  Ins(AND(dst, src))
}

lemma va_lemma_AND(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_AND(dst, src), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires var v := BitwiseAnd(va_eval_word(va_s0, dst), va_eval_word(va_s0, src));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == BitwiseAnd(va_eval_word(va_s0, dst), va_eval_word(va_s0,
    src))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_AND();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- OR

function method{:opaque} va_code_OR(dst:va_operand_word, src:va_operand_word):va_code
{
  Ins(OR(dst, src))
}

lemma va_lemma_OR(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OR(dst, src), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires var v := BitwiseOr(va_eval_word(va_s0, dst), va_eval_word(va_s0, src));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == BitwiseOr(va_eval_word(va_s0, dst), va_eval_word(va_s0, src))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_OR();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- XOR

function method{:opaque} va_code_XOR(dst:va_operand_word, src:va_operand_word):va_code
{
  Ins(XOR(dst, src))
}

lemma va_lemma_XOR(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_XOR(dst, src), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires var v := BitwiseXor(va_eval_word(va_s0, dst), va_eval_word(va_s0, src));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == BitwiseXor(va_eval_word(va_s0, dst), va_eval_word(va_s0,
    src))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_XOR();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- NOT

function method{:opaque} va_code_NOT(dst:va_operand_word):va_code
{
  Ins(NOT(dst))
}

lemma va_lemma_NOT(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_NOT(dst), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires var v := BitwiseNot(va_eval_word(va_s0, dst));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == BitwiseNot(va_eval_word(va_s0, dst))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_NOT();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- MOV

function method{:opaque} va_code_MOV(dst:va_operand_word, src:va_operand_word):va_code
{
  Ins(MOV(dst, src))
}

lemma va_lemma_MOV(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_MOV(dst, src), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires var v := va_eval_word(va_s0, src); ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == va_eval_word(va_s0, src)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_MOV();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- ADD

function method{:opaque} va_code_ADD(dst:va_operand_word, src:va_operand_word):va_code
{
  Ins(ADD(dst, src))
}

lemma va_lemma_ADD(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_ADD(dst, src), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires isUInt32(va_eval_word(va_s0, dst) + va_eval_word(va_s0, src))
  requires var v := va_eval_word(va_s0, dst) + va_eval_word(va_s0, src);
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == va_eval_word(va_s0, dst) + va_eval_word(va_s0, src)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_ADD();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_TruncateUInt32();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- SUB

function method{:opaque} va_code_SUB(dst:va_operand_word, src:va_operand_word):va_code
{
  Ins(SUB(dst, src))
}

lemma va_lemma_SUB(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_SUB(dst, src), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires isUInt32(va_eval_word(va_s0, dst) - va_eval_word(va_s0, src))
  requires var v := va_eval_word(va_s0, dst) - va_eval_word(va_s0, src);
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == va_eval_word(va_s0, dst) - va_eval_word(va_s0, src)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_SUB();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_TruncateUInt32();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- Store

function method{:opaque} va_code_Store(dst:va_operand_word, offset:uint32,
  src:va_operand_word):va_code
{
  Ins(MOV(MakeMemOp(dst, offset), src))
}

lemma va_lemma_Store(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  offset:uint32, src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_Store(dst, offset, src), va_s0, va_sN)
  requires va_is_src_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires x86wk_valid_memstate(va_get_mem(va_s0))
  ensures  x86wk_valid_memstate(va_get_mem(va_sM))
  requires var addr := va_eval_word(va_s0, dst) + offset; (is_valid_addr(addr) &&
    is_valid_vaddr(addr)) && WK_ValidMemForWrite(addr)
  requires var v := va_eval_word(va_s0, src); ins_valid_new_dst_opr_value(va_s0.wk_mstate,
    MakeMemOp(dst, offset), v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_get_mem(va_sM) == stack_set_val(va_get_mem(va_s0), va_eval_word(va_s0, dst) + offset,
    va_eval_word(va_s0, src))
  ensures  va_eval_word(va_sM, dst) == va_eval_word(va_s0, dst)
  ensures  offset == offset
  ensures  va_eval_word(va_sM, src) == va_eval_word(va_s0, src)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))
{
  reveal_va_code_Store();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- Load

function method{:opaque} va_code_Load(dst:va_operand_word, src:va_operand_word,
  offset:uint32):va_code
{
  Ins(MOV(dst, MakeMemOp(src, offset)))
}

lemma va_lemma_Load(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  src:va_operand_word, offset:uint32)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_Load(dst, src, offset), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires x86wk_valid_memstate(va_get_mem(va_s0))
  requires var addr := va_eval_word(va_s0, src) + offset; (is_valid_addr(addr) &&
    is_valid_vaddr(addr)) && WK_ValidMemForRead(addr)
  requires var src_operand := MakeMemOp(src, offset); var v := OperandContents(va_s0.wk_mstate,
    src_operand); ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == stack_get_val(va_get_mem(va_sM), va_eval_word(va_s0, src) +
    offset)
  ensures  va_sM.ok ==> WK_ValidMemForRead(va_eval_word(va_s0, src) + offset) &&
    va_eval_word(va_sM, dst) == wkm_stack_get_val(va_sM.wk_mstate, va_eval_word(va_s0, src) +
    offset)
  ensures  va_get_mem(va_sM) == va_get_mem(va_s0)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_Load();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- LDRglobaladdr

function method{:opaque} va_code_LDRglobaladdr(dst:va_operand_word, g:symbol):va_code
{
  Ins(MOV_reloc(dst, g))
}

lemma va_lemma_LDRglobaladdr(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  g:symbol)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_LDRglobaladdr(dst, g), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires is_gvar_exist(g)
  requires var v := AddressOfGlobal(g); ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == AddressOfGlobal(g)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_LDRglobaladdr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- LDRglobal

function method{:opaque} va_code_LDRglobal(dst:va_operand_word, g:symbol, base:va_operand_reg,
  ofs:va_operand_word):va_code
{
  Ins(LDR_global(dst, g, base, ofs))
}

lemma va_lemma_LDRglobal(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  g:symbol, base:va_operand_reg, ofs:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_LDRglobal(dst, g, base, ofs), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_reg(base, va_s0)
  requires va_is_src_word(ofs, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires WK_ValidGlobalVars_Decls(va_get_globals(va_s0))
  requires var addr := va_eval_reg(va_s0, base) + va_eval_word(va_s0, ofs); (is_valid_addr(addr) &&
    is_valid_vaddr(addr)) && is_gvar_valid_vaddr(g, addr)
  requires var v := gvar_read_word_byoffset(va_s0.wk_mstate, g, WordAlignedSub(va_eval_reg(va_s0,
    base) + va_eval_word(va_s0, ofs), AddressOfGlobal(g)));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == gvar_read_word_byaddr(va_sM.wk_mstate, g, va_eval_reg(va_s0,
    base) + va_eval_word(va_s0, ofs))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_LDRglobal();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- STRglobal

function method{:opaque} va_code_STRglobal(g:symbol, base:va_operand_reg, ofs:va_operand_word,
  v:va_operand_word):va_code
{
  Ins(STR_global(v, g, base, ofs))
}

lemma va_lemma_STRglobal(va_b0:va_codes, va_s0:va_state, va_sN:va_state, g:symbol,
  base:va_operand_reg, ofs:va_operand_word, v:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_STRglobal(g, base, ofs, v), va_s0, va_sN)
  requires va_is_src_reg(base, va_s0)
  requires va_is_src_word(ofs, va_s0)
  requires va_is_src_word(v, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires WK_ValidGlobalVars_Decls(va_get_globals(va_s0))
  requires var addr := va_eval_reg(va_s0, base) + va_eval_word(va_s0, ofs); (is_valid_addr(addr) &&
    is_valid_vaddr(addr)) && is_gvar_valid_vaddr(g, addr)
  requires var addr := va_eval_reg(va_s0, base) + va_eval_word(va_s0, ofs);
    ins_valid_strglobal_word(va_s0.subjects, va_s0.objects, va_s0.id_mappings, va_s0.objs_addrs,
    va_s0.activate_conds, va_get_globals(va_s0), g, addr, va_eval_word(va_s0, v))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  WK_ValidGlobalVars_Decls(va_get_globals(va_sM))
  ensures  va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), g, va_eval_reg(va_s0,
    base) + va_eval_word(va_s0, ofs), va_eval_word(va_s0, v))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0)))
{
  reveal_va_code_STRglobal();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- MUL

function method{:opaque} va_code_MUL(src:va_operand_word):va_code
{
  Ins(MUL(src))
}

lemma va_lemma_MUL(va_b0:va_codes, va_s0:va_state, va_sN:va_state, src:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_MUL(src), va_s0, va_sN)
  requires va_is_src_word(src, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  requires forall a:word, b:word :: isUInt64(a * b)
  ensures  var val:uint64 := va_get_reg(EAX, va_s0) * va_eval_word(va_s0, src); va_get_reg(EAX,
    va_sM) == UInt64Low(val) && va_get_reg(EDX, va_sM) == UInt64High(val)
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM,
    va_update_ok(va_sM, va_s0))))
{
  reveal_va_code_MUL();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_TruncateUInt32();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- PUSH

function method{:opaque} va_code_PUSH(v:va_operand_word):va_code
{
  Ins(PUSH(v))
}

lemma va_lemma_PUSH(va_b0:va_codes, va_s0:va_state, va_sN:va_state, v:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_PUSH(v), va_s0, va_sN)
  requires va_is_src_word(v, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires x86wk_valid_memstate(va_get_mem(va_s0))
  ensures  x86wk_valid_memstate(va_get_mem(va_sM))
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var stack_new_top := va_get_reg(ESP, va_s0) - ARCH_WORD_BYTES;
    (IsAddrInStack(stack_new_top) && va_get_reg(ESP, va_sM) == stack_new_top) && va_get_mem(va_sM)
    == stack_set_val(va_get_mem(va_s0), stack_new_top, va_eval_word(va_s0, v))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_s0))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_s0))))
{
  reveal_va_code_PUSH();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- POP

function method{:opaque} va_code_POP(dst:va_operand_reg):va_code
{
  Ins(POP(dst))
}

lemma va_lemma_POP(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_POP(dst), va_s0, va_sN)
  requires va_is_dst_reg(dst, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires x86wk_valid_memstate(va_get_mem(va_s0))
  ensures  x86wk_valid_memstate(va_get_mem(va_sM))
  requires IsAddrInStack(va_get_reg(ESP, va_s0))
  requires IsAddrInStack(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  requires dst != OReg(ESP)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES
  ensures  va_eval_reg(va_sM, dst) == stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0))
  ensures  va_sM.ok ==> WK_ValidMemForRead(va_get_reg(ESP, va_s0)) && va_eval_reg(va_sM, dst) ==
    wkm_stack_get_val(va_sM.wk_mstate, va_get_reg(ESP, va_s0))
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_update_operand_reg(dst, va_sM, va_s0))))
{
  reveal_va_code_POP();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- SHL

function method{:opaque} va_code_SHL(dst:va_operand_word, bits:va_operand_word):va_code
{
  Ins(SHL(dst, bits))
}

lemma va_lemma_SHL(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  bits:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_SHL(dst, bits), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(bits, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires bits == Reg3 || bits == OConst(va_eval_word(va_s0, bits))
  requires 0 <= va_eval_word(va_s0, bits) < Ins_Shift_Max
  requires var v := LeftShift(va_eval_word(va_s0, dst), va_eval_word(va_s0, bits));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == LeftShift(va_eval_word(va_s0, dst), va_eval_word(va_s0,
    bits))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_SHL();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- SHR

function method{:opaque} va_code_SHR(dst:va_operand_word, bits:va_operand_word):va_code
{
  Ins(SHR(dst, bits))
}

lemma va_lemma_SHR(va_b0:va_codes, va_s0:va_state, va_sN:va_state, dst:va_operand_word,
  bits:va_operand_word)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_SHR(dst, bits), va_s0, va_sN)
  requires va_is_dst_word(dst, va_s0)
  requires va_is_src_word(bits, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires bits == Reg3 || bits == OConst(va_eval_word(va_s0, bits))
  requires 0 <= va_eval_word(va_s0, bits) < Ins_Shift_Max
  requires var v := RightShift(va_eval_word(va_s0, dst), va_eval_word(va_s0, bits));
    ins_valid_new_dst_opr_value(va_s0.wk_mstate, dst, v)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_word(va_sM, dst) == RightShift(va_eval_word(va_s0, dst), va_eval_word(va_s0,
    bits))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_word(dst, va_sM, va_s0)))
{
  reveal_va_code_SHR();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
}
//--
//-- CALL_EEHCI_Activate

function method{:opaque} va_code_CALL_EEHCI_Activate():va_code
{
  Ins(CALL_EEHCI_Activate())
}

lemma va_lemma_CALL_EEHCI_Activate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_EEHCI_Activate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_retval_space := FFI_EEHCI_Activate_ReturnWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_EEHCI_Activate_ReturnWords)
  ensures  ffi_eehci_activate_stack_and_globals(va_s0.wk_mstate, va_get_mem(va_sM),
    va_get_globals(va_sM))
  ensures  ffi_eehci_activate_stack_and_globals2(va_s0, va_get_mem(va_sM), va_get_globals(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_EEHCI_Activate_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_EEHCI_Activate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_EEHCI_Activate_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 567 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 568 column 5 of file .\ins/x86/ins.vad
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfEEHCIActivate(va_old_s.wk_mstate, va_sM.wk_mstate,
    va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_eehci_activate_ResultStateIsValidMState_AndSecureEEHCIMemState(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_eehci_activate_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s, va_sM,
    va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_EEHCI_Deactivate

function method{:opaque} va_code_CALL_EEHCI_Deactivate():va_code
{
  Ins(CALL_EEHCI_Deactivate())
}

lemma va_lemma_CALL_EEHCI_Deactivate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_EEHCI_Deactivate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires ins_valid_eehci_deactivate(va_s0.wk_mstate, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_EEHCI_Deactivate_ReturnWords)
  ensures  ffi_eehci_deactivate_stack_and_globals(va_s0.wk_mstate, va_get_mem(va_sM),
    va_get_globals(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_EEHCI_Deactivate_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_EEHCI_Deactivate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_EEHCI_Deactivate_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 625 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 626 column 5 of file .\ins/x86/ins.vad
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfEEHCIDeactivate(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_eehci_deactivate_ResultStateIsValidMState_AndSecureEEHCIMemState(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_eehci_deactivate_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s, va_sM,
    va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_EEHCI_FIND_RefToUSBTD

function method{:opaque} va_code_CALL_EEHCI_FIND_RefToUSBTD():va_code
{
  Ins(CALL_EEHCI_FIND_RefToUSBTD())
}

lemma va_lemma_CALL_EEHCI_FIND_RefToUSBTD(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_EEHCI_FIND_RefToUSBTD(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_EEHCI_FindRefToUSBTD_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_EEHCI_FindRefToUSBTD_ReturnWords)
  ensures  p_ffi_eehci_find_ref_to_usbtd_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_EEHCI_FindRefToUSBTD_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_EEHCI_FIND_RefToUSBTD();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_EEHCI_FindRefToUSBTD_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 685 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 686 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_QTD32_ParseTDPointers

function method{:opaque} va_code_CALL_USBTD_QTD32_ParseTDPointers():va_code
{
  Ins(CALL_USBTD_QTD32_ParseTDPointers())
}

lemma va_lemma_CALL_USBTD_QTD32_ParseTDPointers(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_QTD32_ParseTDPointers(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords)
  ensures  p_ffi_usbtd_qtd32_parseTDPtrs_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_QTD32_ParseTDPointers();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 740 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 741 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_QTD32_ParseBufPointers

function method{:opaque} va_code_CALL_USBTD_QTD32_ParseBufPointers():va_code
{
  Ins(CALL_USBTD_QTD32_ParseBufPointers())
}

lemma va_lemma_CALL_USBTD_QTD32_ParseBufPointers(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_QTD32_ParseBufPointers(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords)
  ensures  p_ffi_usbtd_qtd32_parseDataBufPtrs_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords *
    ARCH_WORD_BYTES; stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM),
    va_get_reg(ESP, va_sM) + stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_QTD32_ParseBufPointers();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 796 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 797 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_QH32_ParseTDPointers

function method{:opaque} va_code_CALL_USBTD_QH32_ParseTDPointers():va_code
{
  Ins(CALL_USBTD_QH32_ParseTDPointers())
}

lemma va_lemma_CALL_USBTD_QH32_ParseTDPointers(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_QH32_ParseTDPointers(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords)
  ensures  p_ffi_usbtd_qh32_parseTDPtrs_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_QH32_ParseTDPointers();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 850 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 851 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_QH32_ParseBufPointers

function method{:opaque} va_code_CALL_USBTD_QH32_ParseBufPointers():va_code
{
  Ins(CALL_USBTD_QH32_ParseBufPointers())
}

lemma va_lemma_CALL_USBTD_QH32_ParseBufPointers(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_QH32_ParseBufPointers(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords)
  ensures  p_ffi_usbtd_qh32_parseDataBufPtrs_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_QH32_ParseBufPointers();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 905 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 906 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_QH32_ParseTargetUSBDevID

function method{:opaque} va_code_CALL_USBTD_QH32_ParseTargetUSBDevID():va_code
{
  Ins(CALL_USBTD_QH32_ParseTargetUSBDevID())
}

lemma va_lemma_CALL_USBTD_QH32_ParseTargetUSBDevID(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_QH32_ParseTargetUSBDevID(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords)
  ensures  p_ffi_usbtd_qh32_parseTargetUSBDevID_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords *
    ARCH_WORD_BYTES; stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM),
    va_get_reg(ESP, va_sM) + stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_QH32_ParseTargetUSBDevID();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 958 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 959 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_Copy_From_User

function method{:opaque} va_code_CALL_USBTD_Copy_From_User():va_code
{
  Ins(CALL_USBTD_Copy_From_User())
}

lemma va_lemma_CALL_USBTD_Copy_From_User(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_Copy_From_User(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords
    * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_CopyFromUser_ReturnWords)
  ensures  ffi_usbtd_copy_from_user_stack_and_globals(va_s0.wk_mstate, va_get_mem(va_sM),
    va_get_globals(va_sM))
  ensures  var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret != TRUE
    ==> va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  ffi_preserve_sp_and_bp(va_s0.wk_mstate, va_sM.wk_mstate.regs)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_CopyFromUser_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_USBTD_Copy_From_User();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_usbtd_copy_from_user_stack_and_globals();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_CopyFromUser_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1019 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1020 column 5 of file .\ins/x86/ins.vad
  Lemma_ffi_usbtd_copy_from_user_ProveSecurityProperty_WK_USBTD_Map_SecureGlobalVarValues(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_usbtd_copy_from_user_ResultStateIsValidMState_AndEEHCIMemSecureState(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_usbtd_copy_from_user_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s,
    va_sM, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_CheckNotModifyUSBPDevAddrs

function method{:opaque} va_code_CALL_USBTD_CheckNotModifyUSBPDevAddrs():va_code
{
  Ins(CALL_USBTD_CheckNotModifyUSBPDevAddrs())
}

lemma va_lemma_CALL_USBTD_CheckNotModifyUSBPDevAddrs(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_CheckNotModifyUSBPDevAddrs(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords)
  ensures  ffi_ffi_usbtd_check_not_modify_usbpdev_addrs_stack_and_globals(va_s0.wk_mstate,
    va_get_mem(va_sM))
  ensures  var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_sM)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==>
    usbtd_map_valid_slot_id(td_slot) && Is_USBTD_NotModifyUSBPDevsAddrs(va_get_globals(va_s0),
    td_slot)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords *
    ARCH_WORD_BYTES; stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM),
    va_get_reg(ESP, va_sM) + stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_CheckNotModifyUSBPDevAddrs();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_ffi_usbtd_check_not_modify_usbpdev_addrs_stack_and_globals();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1082 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1083 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_Backup

function method{:opaque} va_code_CALL_USBTD_Backup():va_code
{
  Ins(CALL_USBTD_Backup())
}

lemma va_lemma_CALL_USBTD_Backup(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_Backup(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_USBTD_Backup_StackParamsWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM), 0)
  ensures  ffi_usbtd_backup_stack_and_globals(va_s0.wk_mstate, va_get_globals(va_sM))
  ensures  ffi_preserve_sp_and_bp(va_s0.wk_mstate, va_sM.wk_mstate.regs)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_USBTD_Backup();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_usbtd_backup_stack_and_globals_inner();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  ghost var td_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  Lemma_ffi_usbtd_backup_ProveSecurityProperty_WK_USBTD_Map_SecureGlobalVarValues(va_get_globals(va_old_s),
    va_get_globals(va_sM), td_slot);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_sM));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    0);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1144 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1145 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_Restore

function method{:opaque} va_code_CALL_USBTD_Restore():va_code
{
  Ins(CALL_USBTD_Restore())
}

lemma va_lemma_CALL_USBTD_Restore(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_Restore(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_USBTD_Restore_StackParamsWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires ins_valid_usbtd_restore(va_get_mem(va_s0), va_get_globals(va_s0), va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM), 0)
  ensures  ffi_usbtd_restore_stack_and_globals(va_s0.wk_mstate, va_get_globals(va_sM))
  ensures  ffi_preserve_sp_and_bp(va_s0.wk_mstate, va_sM.wk_mstate.regs)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_USBTD_Restore();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_usbtd_restore_stack_and_globals_inner();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    0);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1200 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1201 column 5 of file .\ins/x86/ins.vad
  ghost var td_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD(va_get_globals(va_old_s),
    va_get_globals(va_sM), td_slot);
  Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD(va_get_globals(va_old_s),
    va_get_globals(va_sM), td_slot);
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_sM);
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_IsRefTargetUSBTD

function method{:opaque} va_code_CALL_USBTD_IsRefTargetUSBTD():va_code
{
  Ins(CALL_USBTD_IsRefTargetUSBTD())
}

lemma va_lemma_CALL_USBTD_IsRefTargetUSBTD(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_IsRefTargetUSBTD(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) + stack_params_space))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_USBTD_IsRefTargetUSBTD_ReturnWords)
  ensures  p_ffi_usbtd_is_ref_target_usbtd_retval(va_s0.wk_mstate, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_USBTD_IsRefTargetUSBTD_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_USBTD_IsRefTargetUSBTD();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_USBTD_IsRefTargetUSBTD_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1258 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1259 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBTD_Clear_Content

function method{:opaque} va_code_CALL_USBTD_Clear_Content():va_code
{
  Ins(CALL_USBTD_Clear_Content())
}

lemma va_lemma_CALL_USBTD_Clear_Content(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBTD_Clear_Content(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires ins_valid_usbtd_clear_content(va_get_mem(va_s0), va_get_globals(va_s0), va_get_reg(ESP,
    va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM), 0)
  ensures  ffi_usbtd_clear_content_stack_and_globals(va_s0.wk_mstate, va_get_globals(va_sM))
  ensures  ffi_preserve_sp_and_bp(va_s0.wk_mstate, va_sM.wk_mstate.regs)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_USBTD_Clear_Content();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    0);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1313 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1314 column 5 of file .\ins/x86/ins.vad
  Lemma_ffi_usbtd_clear_content_ProveSecurityProperty_WK_USBTD_Map_SecureGlobalVarValues(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_ffi_usbtd_clear_content_ResultStateIsValidMState_AndEEHCIMemSecureState(va_old_s.wk_mstate,
    va_sM.wk_mstate, va_sM.wk_mstate.regs, va_get_mem(va_sM), va_get_globals(va_sM));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_sM);
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_WimpDrv_DO_Clear

function method{:opaque} va_code_CALL_WimpDrv_DO_Clear():va_code
{
  Ins(CALL_WimpDrv_DO_Clear())
}

lemma va_lemma_CALL_WimpDrv_DO_Clear(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_WimpDrv_DO_Clear(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_WimpDrv_DO_Clear_StackParamsWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_wimpdrv_DO_clear(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM), 0)
  ensures  p_ffi_wimpdrv_DO_clear_retval(va_s0, va_get_mem(va_sM), va_sM.objects)
  ensures  var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var drv_id :=
    wimpdrv_get_id_word(va_get_globals(va_s0), drv_slot);
    wimpdrv_DO_clear_non_mstate_relationship(va_s0, va_sM, drv_id)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_objects(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_WimpDrv_DO_Clear();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_p_ffi_wimpdrv_DO_clear_retval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    0);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1374 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1375 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_objects_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_WimpDrv_CheckDOPAddrRange

function method{:opaque} va_code_CALL_WimpDrv_CheckDOPAddrRange():va_code
{
  Ins(CALL_WimpDrv_CheckDOPAddrRange())
}

lemma va_lemma_CALL_WimpDrv_CheckDOPAddrRange(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_WimpDrv_CheckDOPAddrRange(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords)
  ensures  p_ffi_wimpdrv_DO_check_paddr_range_retval(va_s0, va_get_mem(va_sM))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_WimpDrv_CheckDOPAddrRange();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1423 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1424 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_USBPDev_Clear

function method{:opaque} va_code_CALL_USBPDev_Clear():va_code
{
  Ins(CALL_USBPDev_Clear())
}

lemma va_lemma_CALL_USBPDev_Clear(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_USBPDev_Clear(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_USBPDev_Clear_StackParamsWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_usbpdev_clear(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM), 0)
  ensures  p_ffi_usbpdev_clear_retval(va_s0, va_get_mem(va_sM), va_sM.objects)
  ensures  var usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    usbpdev_addr_high := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var addr:USBPDev_Addr :=
    usb_parse_usbpdev_addr(UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low));
    usbpdev_clear_non_mstate_relationship(va_s0, va_sM, addr)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_objects(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_CALL_USBPDev_Clear();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_p_ffi_usbpdev_clear_retval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    0);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1483 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1484 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_objects_stateeq(va_old_s, va_sM);
}
//--
//-- AXIOM_Assign_USBPDevs_To_OS_Partition

function method{:opaque} va_code_AXIOM_Assign_USBPDevs_To_OS_Partition():va_code
{
  Ins(AXIOM_Assign_USBPDevs_To_OS_Partition())
}

lemma va_lemma_AXIOM_Assign_USBPDevs_To_OS_Partition(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_AXIOM_Assign_USBPDevs_To_OS_Partition(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires WK_ValidGlobalVarValues_USBPDevList(va_s0.subjects, va_s0.id_mappings,
    va_get_globals(va_s0))
  requires forall i:uint32 :: usbpdev_valid_slot_id(i) ==> usbpdev_get_pid(va_get_globals(va_s0),
    i) == WS_PartitionID(PID_INVALID)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var result_subjs := AXIOM_Assign_USBPDevs_To_OS_Partition_Property(va_s0); va_sM ==
    va_s0.(subjects := result_subjs)
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
  ensures  va_state_eq(va_sM, va_update_subjects(va_sM, va_update_ok(va_sM, va_s0)))
{
  reveal_va_code_AXIOM_Assign_USBPDevs_To_OS_Partition();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_AXIOM_Assign_USBPDevs_To_OS_Partition_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s,
    va_sM);
}
//--
//-- CALL_PMem_AssignToWimps

function method{:opaque} va_code_CALL_PMem_AssignToWimps():va_code
{
  Ins(CALL_PMem_AssignToWimps())
}

lemma va_lemma_CALL_PMem_AssignToWimps(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_PMem_AssignToWimps(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords
    * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pmem_assign_main_mem_to_wimps(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PMem_AssignToWimps_ReturnWords)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_PMem_AssignToWimps_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_PMem_AssignToWimps();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_PMem_AssignToWimps_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1567 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1568 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_PMem_ReleaseFromWimps

function method{:opaque} va_code_CALL_PMem_ReleaseFromWimps():va_code
{
  Ins(CALL_PMem_ReleaseFromWimps())
}

lemma va_lemma_CALL_PMem_ReleaseFromWimps(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_PMem_ReleaseFromWimps(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) + stack_params_space))
  requires ins_valid_pmem_release_main_mem_from_wimps(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PMem_ReleaseFromWimps_ReturnWords)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_CALL_PMem_ReleaseFromWimps();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_PMem_ReleaseFromWimps_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1614 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1615 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_PMem_ActivateInOS

function method{:opaque} va_code_CALL_PMem_ActivateInOS():va_code
{
  Ins(CALL_PMem_ActivateInOS())
}

lemma va_lemma_CALL_PMem_ActivateInOS(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_PMem_ActivateInOS(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords
    * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pmem_activate_main_mem_in_os(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PMem_ActivateInOS_ReturnWords)
  ensures  ffi_pmem_activate_main_mem_in_os_stack_and_statevars(va_s0, va_get_mem(va_sM),
    va_sM.subjects, va_sM.objects, va_sM.os_mem_active_map)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_PMem_ActivateInOS_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_os_mem_active_map(va_sM, va_update_objects(va_sM, va_update_subjects(va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))))
{
  reveal_va_code_CALL_PMem_ActivateInOS();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_pmem_activate_main_mem_in_os_stack_and_statevars();
  reveal_WK_SecureObjsAddrs_MemSeparation();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  ghost var paddr_end := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    ARCH_WORD_BYTES);
  ghost var paddr_start := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    Lemma_pmem_activate_main_mem_in_os_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s, va_sM,
      paddr_start, paddr_end);
  }
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_PMem_ActivateInOS_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1675 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1676 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_subjects_objects_pmem_active_map_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_PMem_DeactivateFromOS

function method{:opaque} va_code_CALL_PMem_DeactivateFromOS():va_code
{
  Ins(CALL_PMem_DeactivateFromOS())
}

lemma va_lemma_CALL_PMem_DeactivateFromOS(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_PMem_DeactivateFromOS(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space :=
    FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) + stack_params_space))
  requires ins_valid_pmem_deactivate_main_mem_from_os(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PMem_DeactivateFromOS_ReturnWords)
  ensures  ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars(va_s0, va_get_mem(va_sM),
    va_sM.subjects, va_sM.objects, va_sM.os_mem_active_map)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_os_mem_active_map(va_sM, va_update_objects(va_sM, va_update_subjects(va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))))
{
  reveal_va_code_CALL_PMem_DeactivateFromOS();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_pmem_deactivate_main_mem_from_os_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s, va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_PMem_DeactivateFromOS_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1726 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1727 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_subjects_objects_pmem_active_map_stateeq(va_old_s, va_sM);
}
//--
//-- CALL_PEHCI_ActivateInOS

function method{:opaque} va_code_CALL_PEHCI_ActivateInOS():va_code
{
  Ins(CALL_PEHCI_ActivateInOS())
}

lemma va_lemma_CALL_PEHCI_ActivateInOS(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_CALL_PEHCI_ActivateInOS(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := WK_STACK_FOR_EXTERNEL_FUNCS_SZ; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords
    * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pEHCI_ActivateInOS(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PEHCI_ActivateInOS_ReturnWords)
  ensures  ffi_pehci_activate_in_os_stack_and_statevars(va_s0, va_sM.subjects, va_sM.objects)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_PEHCI_ActivateInOS_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_objects(va_sM, va_update_subjects(va_sM, va_update_mem(va_sM, va_update_ok(va_sM,
    va_s0)))))))))))))
{
  reveal_va_code_CALL_PEHCI_ActivateInOS();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  reveal_va_eval();
  reveal_ffi_preserve_sp_and_bp();
  reveal_ffi_pehci_activate_in_os_stack_and_statevars();
  reveal_WK_SecureObjsAddrs_MemSeparation();
  va_sM := MaybeUpdateOk(va_old_s, va_sM);
  Lemma_ffi_pehci_activate_in_os_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(va_old_s,
    va_sM);
  Lemma_ffi_ret_on_stack_Implies_stack_under_sp_is_unchanged(va_old_s.wk_mstate, va_sM.wk_mstate,
    FFI_PEHCI_ActivateInOS_ReturnWords);
  assert ffi_preserve_sp_and_bp(va_old_s.wk_mstate, va_sM.wk_mstate.regs);  // line 1779 column 5 of file .\ins/x86/ins.vad
  assert va_sM.wk_mstate.sregs == va_old_s.wk_mstate.sregs;  // line 1780 column 5 of file .\ins/x86/ins.vad
  Lemma_modify_regs_subjects_objects_stateeq(va_old_s, va_sM);
}
//--
