//CCH: many things are from Komodo
//include "INTELdef2.s.dfy"
include "ins_eval.s.dfy"
include "../../arch/x86/x86_cpu.i.dfy"

//-----------------------------------------------------------------------------
// Spartan Types
//-----------------------------------------------------------------------------
type va_int = int
type va_bool = bool

type va_operand_reg = operand
type va_operand_constop = operand
type va_operand_word = operand

/*type va_operand = operand // va_operand is deprecated */
type va_operand_code = operand
type va_operand_lemma = operand
type va_cmp = operand
type va_code = code
type va_codes = codes
type va_state = state

//-----------------------------------------------------------------------------
// Spartan-Verification Interface
//-----------------------------------------------------------------------------

function method va_op(o:va_operand_lemma):va_operand_code { o }

predicate {:opaque} va_eval(c:code, s:state, r:state)
{
    s.ok ==> evalCode(c, s, r)
}

function method va_CNil():codes { CNil }
function va_cHead(b:codes):code requires b.va_CCons? { b.hd }
predicate va_cHeadIs(b:codes, c:code) { b.va_CCons? && b.hd == c }
predicate va_cTailIs(b:codes, t:codes) { b.va_CCons? && b.tl == t }

predicate va_require(b0:codes, c1:code, s0:va_state, sN:va_state)
{
    va_cHeadIs(b0, c1)
 && va_eval(Block(b0), s0, sN)
 && ValidState(s0)
}

predicate va_ensure(b0:codes, b1:codes, s0:va_state, s1:va_state, sN:va_state)
{
    va_cTailIs(b0, b1)
 && va_eval(va_Block(b1), s1, sN)
 && ValidState(s1)
}

function method va_op_cmp_reg(r:x86Reg):operand {va_op_reg(r)}
function method va_const_operand(n:word):operand { OConst(n) }
function method va_const_cmp(n:word):va_cmp { va_const_operand(n) }
function method va_coerce_operand_to_cmp(o:operand):operand { o }
function method va_coerce_word_to_cmp(o:va_operand_word):operand { va_coerce_operand_to_cmp(o) }
function method va_coerce_reg_to_cmp(o:va_operand_reg):operand { va_coerce_operand_to_cmp(o) }

function method va_cmp_eq(o1:operand, o2:operand):obool { OCmp(OEq, o1, o2) }
function method va_cmp_ne(o1:operand, o2:operand):obool { OCmp(ONe, o1, o2) }
function method va_cmp_le(o1:operand, o2:operand):obool { OCmp(OLe, o1, o2) }
function method va_cmp_ge(o1:operand, o2:operand):obool { OCmp(OGe, o1, o2) }
function method va_cmp_lt(o1:operand, o2:operand):obool { OCmp(OLt, o1, o2) }
function method va_cmp_gt(o1:operand, o2:operand):obool { OCmp(OGt, o1, o2) }
//function method va_cmp_tst_eq(o1:operand, o2:operand):obool { OCmp(OTstEq, o1, o2) }
//function method va_cmp_tst_ne(o1:operand, o2:operand):obool { OCmp(OTstNe, o1, o2) }

function method va_Block(block:codes):code { Block(block) }
function method va_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method va_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method va_get_block(c:code):codes requires c.Block? { c.block }
function method va_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method va_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method va_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method va_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method va_get_whileBody(c:code):code requires c.While? { c.whileBody }




/*********************** Vale-to-Dafny connections needed for refined mode ********************/
// Fetchers
function va_get_ok(s:state):bool { s.ok }
function va_get_reg(r:x86Reg, s:state):word
    requires Valid_WKMState_RegsDecl(s.wk_mstate.regs)
{
    x86_get_reg(s.wk_mstate, r)
}

function va_get_sreg(sr:SReg, s:state):word
    requires is_valid_x86_sregs(s.wk_mstate.sregs)
{
    //lemma_SRegDom(sr, s);
    x86_get_sreg(s.wk_mstate, sr)
}

function va_get_mem(s:state):wk_memmap
    requires ValidState(s)
    ensures x86wk_valid_memstate(va_get_mem(s))
{
    //reveal WK_ValidMemState(); 
    //reveal_ValidAddrMemStateOpaque(); 
    s.wk_mstate.m 
}

function va_get_globals(s:state):globalsmap
    requires ValidState(s)
    ensures WK_ValidGlobalVars_Decls(va_get_globals(s))
{ 
    //reveal WK_ValidMemState(); 
    //reveal_ValidGlobalStateOpaque(); 
    s.wk_mstate.globals
}




// Setters
function va_update_ok(sM:state, sK:state):state { sK.(ok := sM.ok) }

function va_update_reg(r:x86Reg, sM:state, sK:state):state 
    requires is_valid_x86_regs(sK.wk_mstate.regs)
    requires is_valid_x86_regs(sM.wk_mstate.regs)
    ensures is_valid_x86_regs(va_update_reg(r, sM, sK).wk_mstate.regs)
{
    //reveal ValidRegState();
    var new_wkm := sK.wk_mstate.(regs := sK.wk_mstate.regs[r := sM.wk_mstate.regs[r]]);
    sK.(wk_mstate := new_wkm)
}

function va_update_sreg(sr:SReg, sM:state, sK:state):state
    requires is_valid_x86_sregs(sK.wk_mstate.sregs)
    requires is_valid_x86_sregs(sM.wk_mstate.sregs)
    ensures is_valid_x86_sregs(va_update_sreg(sr, sM, sK).wk_mstate.sregs)
{
    var v := sM.wk_mstate.sregs[sr];
    var new_wkm := sK.wk_mstate.(sregs := sK.wk_mstate.sregs[sr := v]);
    sK.(wk_mstate := new_wkm)
}

function va_update_mem(sM:state, sK:state):state
    requires WK_ValidMemState(sM.wk_mstate)
    requires WK_ValidMemState(sK.wk_mstate)
    requires x86wk_valid_memstate(sM.wk_mstate.m)
    requires x86wk_valid_memstate(sK.wk_mstate.m)

    ensures WK_ValidMemState(va_update_mem(sM, sK).wk_mstate)
    ensures x86wk_valid_memstate(va_update_mem(sM, sK).wk_mstate.m)
{
    reveal x86wk_valid_memstate();

    sK.(wk_mstate := sK.wk_mstate.(m := sM.wk_mstate.m))
}

function va_update_operand(o:operand, sM:state, sK:state):state
    requires ins_is_reg_opr(o)  //CCH: should be reconsidered
    requires is_valid_x86_regs(sK.wk_mstate.regs)
    requires is_valid_x86_regs(sM.wk_mstate.regs)
    requires is_valid_x86_sregs(sK.wk_mstate.sregs)
    requires is_valid_x86_sregs(sM.wk_mstate.sregs)
{
    match o
        case OReg(r) => va_update_reg(r, sM, sK)
        case OSReg(sr) => va_update_sreg(sr, sM, sK)
        //CCH: should be reconsidered
}

function va_update_operand_reg(o:operand, sM:state, sK:state):state
    requires ins_is_reg_opr(o)  //CCH: should be reconsidered
    requires is_valid_x86_regs(sK.wk_mstate.regs)
    requires is_valid_x86_regs(sM.wk_mstate.regs)
    requires is_valid_x86_sregs(sK.wk_mstate.sregs)
    requires is_valid_x86_sregs(sM.wk_mstate.sregs)
{
    va_update_operand(o, sM, sK)
}

function va_update_operand_word(o:operand, sM:state, sK:state):state
    requires ins_is_reg_opr(o)  //CCH: should be reconsidered
    requires is_valid_x86_regs(sK.wk_mstate.regs)
    requires is_valid_x86_regs(sM.wk_mstate.regs)
    requires is_valid_x86_sregs(sK.wk_mstate.sregs)
    requires is_valid_x86_sregs(sM.wk_mstate.sregs)
{
    va_update_operand(o, sM, sK)
}

function va_update_globals(sM:state, sK:state) : (result:state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(sM.wk_mstate))
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(sK.wk_mstate))

    ensures WK_ValidGlobalVars_Decls(wkm_get_globals(result.wk_mstate))
{
    sK.(wk_mstate := sK.wk_mstate.(globals := sM.wk_mstate.globals))
}




// type reg
type reg = word
predicate va_is_src_reg(o:operand, s:state) { o.OReg? }
predicate va_is_dst_reg(o:operand, s:state) { o.OReg? }

function va_eval_reg(s:state, o:operand):reg
    requires va_is_src_reg(o, s);
    requires ValidState(s)
{
    OperandContents(s.wk_mstate,o)
}

function method va_coerce_reg_to_word(reg:va_operand_reg):va_operand_word {reg}

function method va_op_reg(r:x86Reg):va_operand_reg { OReg(r) }
function method va_op_reg_reg(r:x86Reg):va_operand_reg { va_op_reg(r) }
function method va_op_word_reg(r:x86Reg):va_operand_word { va_op_reg(r) }




// type word
predicate va_is_src_word(o:operand, s:state) { o.OReg? || o.OConst? }
predicate va_is_dst_word(o:operand, s:state) { o.OReg? }
function method va_coerce_word_to_reg(word:va_operand_word):va_operand_reg {word}

function va_eval_word(s:state, o:operand):word
    requires va_is_src_word(o, s);
    requires ValidState(s)
{
    OperandContents(s.wk_mstate,o)
}




// type constop
type constop = word
predicate va_is_src_constop(o:operand, s:state) { o.OConst? }

function va_eval_constop(s:state, o:operand):constop
    requires va_is_src_constop(o, s)
{
    o.n
}

function method va_const_constop(n:word):va_operand_constop {va_const_operand(n)}
function method va_coerce_constop_to_word(constop:va_operand_constop):va_operand_word {constop}
function method va_op_constop_reg(r:x86Reg):va_operand_constop { va_op_reg(r) }



// type state
predicate va_state_eq(s0:state, s1:state) 
{
    s0.wk_mstate == s1.wk_mstate &&
    state_equal_except_mstate(s0, s1)
}




// type word
function method va_const_word(n:word):va_operand_word {va_const_operand(n)}




function method MakeMemOp(o:operand, offset:uint32) : operand
{
    if o.OReg? then OMAddr(MReg(o.r, offset))
    else if o.OConst? then 
           if (0 <= o.n + offset) && (o.n + offset < UINT32_LIM) then OMAddr(MConst(o.n + offset))
           else OErr
    else OErr
}



// type subjects, objects, and os_mem_active_map
function va_update_subjects(sM:state, sK:state):state
{
    sK.(subjects := sM.subjects)
}

function va_update_objects(sM:state, sK:state):state
{
    sK.(objects := sM.objects)
}

function va_update_os_mem_active_map(sM:state, sK:state):state
{
    sK.(os_mem_active_map := sM.os_mem_active_map)
}



//-----------------------------------------------------------------------------
// Control Flow Lemmas
//-----------------------------------------------------------------------------

predicate valid_state(s:va_state) { ValidState(s) }

lemma va_lemma_empty(s:va_state, r:va_state) returns(r':va_state)
    requires va_eval(Block(va_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
    ensures  forall b, s' :: va_eval(b, r, s') ==> va_eval(b, s, s')
{
    reveal va_eval();
    r' := s;
}

lemma evalWhile_validity(b:obool, c:code, n:nat, s:state, r:state)
    requires evalWhile(b, c, n, s, r);
    decreases c, 1, n;
    ensures  valid_state(s) && r.ok ==> valid_state(r);
{
    if valid_state(s) && r.ok && ins_valid_opr(s.wk_mstate, b.o1) && ins_valid_opr(s.wk_mstate, b.o2) && n > 0 {
        var s', r' :| evalGuard(s, s') && evalOBool(s.wk_mstate, b) && evalCode(c, s', r') && evalWhile(b, c, n - 1, r', r);
        code_state_validity(c, s', r');
        evalWhile_validity(b, c, n - 1, r', r);
        assert valid_state(r);
    }
}

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    ensures  !s.ok ==> !r.ok;
    decreases block;
{
    if !block.CNil? {
        var r' :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        lemma_FailurePreservedByCode(block.hd, s, r');
        lemma_FailurePreservedByBlock(block.tl, r', r);
    }
}

lemma lemma_FailurePreservedByCode(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    ensures  !s.ok ==> !r.ok;
{
    if c.Block? {
        lemma_FailurePreservedByBlock(c.block, s, r);
    }
}

lemma block_state_validity(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    requires valid_state(s);
    decreases block, 0;
    ensures  r.ok ==> valid_state(r);
{
    if block.va_CCons? {
        var r':state :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        code_state_validity(block.hd, s, r');
        if r'.ok {
            block_state_validity(block.tl, r', r);
        }
        else {
            lemma_FailurePreservedByBlock(block.tl, r', r);
        }
    }
}

lemma code_state_validity(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    requires valid_state(s);
    decreases c, 0;
    ensures  r.ok ==> valid_state(r);
{
    if r.ok {
        if c.Ins? {
            reveal WK_ValidSubjs();
            reveal WK_ValidObjs();
            assert valid_state(r);
        } else if c.Block? {
            block_state_validity(c.block, s, r);
        } else if c.IfElse? {
            if ins_valid_opr(s.wk_mstate, c.ifCond.o1) && ins_valid_opr(s.wk_mstate, c.ifCond.o2) {
                var s' :| evalGuard(s, s') &&
                    if evalOBool(s.wk_mstate, c.ifCond) then
                        evalCode(c.ifTrue, s', r)
                    else
                        evalCode(c.ifFalse, s', r);
                if evalOBool(s.wk_mstate, c.ifCond) {
                    code_state_validity(c.ifTrue, s', r);
                } else {
                    code_state_validity(c.ifFalse, s', r);
                }
            }
            assert valid_state(r);
        } else if c.While? {
            var n:nat :| evalWhile(c.whileCond, c.whileBody, n, s, r);
            evalWhile_validity(c.whileCond, c.whileBody, n, s, r);
            assert valid_state(r);
        }
    }
}

lemma va_lemma_block(b:codes, s0:va_state, r:va_state) returns(r1:va_state, c0:code, b1:codes)
    requires b.va_CCons?
    requires va_eval(Block(b), s0, r)
    ensures  b == va_CCons(c0, b1)
    ensures  ValidState(s0) && r1.ok ==> ValidState(r1);
    ensures  va_eval(c0, s0, r1)
    ensures  va_eval(Block(b1), r1, r)
{
    reveal va_eval();
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r);
        r1 := r';
        if ValidState(s0) {
            code_state_validity(c0, s0, r1);
        }
        assert va_eval(c0, s0, r1);
    } else {
        r1 := s0;
    }
}

lemma va_lemma_ifElse(ifb:obool, ct:code, cf:code, s:va_state, r:va_state) returns(cond:bool, s':va_state)
    requires ValidState(s) && ins_valid_opr_bool(s.wk_mstate, ifb.o1) && ins_valid_opr_bool(s.wk_mstate, ifb.o2)
    requires !interrupts_enabled(x86_get_eflags(s.wk_mstate))
    requires va_eval(IfElse(ifb, ct, cf), s, r)
    ensures  forall c, t, t' :: va_eval(c, t, t') == (t.ok ==> va_eval(c, t, t'));
    ensures  if s.ok then
                    s'.ok
                 && ValidState(s')
                 && evalGuard(s, s')
                 && cond == evalOBool(s.wk_mstate, ifb)
                 && (if cond then va_eval(ct, s', r) else va_eval(cf, s', r))
             else
                 true //!r.ok;
{
    reveal va_eval();
    if s.ok {
        assert evalIfElse(ifb, ct, cf, s, r);
        cond := evalOBool(s.wk_mstate, ifb);
        var t:state :| evalGuard(s, t) && (if cond then evalCode(ct, t, r) else evalCode(cf, t, r));
        s' := t;
    }
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state)
{
    evalWhile(b, c, n, s, r)
}

predicate evalWhileLax(b:obool, c:code, n:nat, s:state, r:state)
{
    s.ok ==> evalWhileOpaque(b, c, n, s, r)
}

predicate va_whileInv(b:obool, c:code, n:int, r1:va_state, r2:va_state)
{
    n >= 0 && ValidState(r1) && evalWhileLax(b, c, n, r1, r2)
}

lemma va_lemma_while(b:obool, c:code, s:va_state, r:va_state) returns(n:nat, r':va_state)
    requires ValidState(s) && ins_valid_opr(s.wk_mstate, b.o1) && ins_valid_opr(s.wk_mstate, b.o2)
    requires va_eval(While(b, c), s, r)
    ensures  evalWhileLax(b, c, n, s, r)
    //ensures  r'.ok
    ensures  ValidState(r');
    ensures  r' == s
    //ensures  forall c', t, t' :: va_eval(c', t, t') == (t.ok ==> va_eval(c', t, t'));
{
    reveal va_eval();
    reveal evalWhileOpaque();
//    unpack_eval_while(b, c, s, r);
    if s.ok {
        assert evalCode(While(b, c), s, r);
        n :| evalWhile(b, c, n, s, r);
    } else {
        n := 0;
    }
    r' := s;
}

lemma va_lemma_whileTrue(b:obool, c:code, n:va_int, s:va_state, r:va_state) returns(s':va_state, r':va_state)
    requires ValidState(s) && ins_valid_opr_bool(s.wk_mstate, b.o1) && ins_valid_opr_bool(s.wk_mstate, b.o2)
    requires !interrupts_enabled(x86_get_eflags(s.wk_mstate))
    requires n > 0
    requires evalWhileLax(b, c, n, s, r)
    //ensures  ValidState(s) && r'.ok ==> ValidState(r');
    ensures  ValidState(s');
    ensures  evalWhileLax(b, c, n-1, r', r)
    ensures  va_eval(c, s', r');
    ensures  if s.ok then evalGuard(s, s') && s'.ok && evalOBool(s.wk_mstate, b) else s' == s;
{
    reveal va_eval();
    reveal evalWhileOpaque();

    if !s.ok {
        s' := s;
        r' := s;
        return;
    }
    assert evalWhile(b, c, n, s, r); // TODO: Dafny reveal/opaque issue

    if ValidState(s) {
        var s'', r'':state :| evalGuard(s, s'') && evalOBool(s.wk_mstate, b) && evalCode(c, s'', r'')
            && evalWhile(b, c, n - 1, r'', r);
        code_state_validity(c, s'', r'');
        s' := s'';
        r' := r'';
    } else {
        s' := s.(ok := false);
        r' := s.(ok := false);
    }
}

lemma va_lemma_whileFalse(b:obool, c:code, s:va_state, r:va_state) returns(r':va_state)
    requires ValidState(s) && ins_valid_opr_bool(s.wk_mstate, b.o1) && ins_valid_opr_bool(s.wk_mstate, b.o2)
    requires !interrupts_enabled(x86_get_eflags(s.wk_mstate))
    requires evalWhileLax(b, c, 0, s, r)
    ensures  forall c', t, t' :: va_eval(c', t, t') == (t.ok ==> va_eval(c', t, t'));
    ensures  if s.ok then
                    r.ok && r' == r && ValidState(r')
                     && evalGuard(s, r')
                     && !evalOBool(s.wk_mstate, b)
            else
                r' == s
{
    reveal va_eval();
    reveal evalWhileOpaque();

    if !s.ok {
        r' := s;
        return;
    }

    r' := r;
}

lemma Lemma_modify_regs_stateeq(old_s:state, new_s:state)
    requires WK_ValidMState(old_s.wk_mstate)
    requires WK_ValidMState(new_s.wk_mstate)

    requires new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
    requires state_equal_except_mstate(old_s, new_s)

    ensures va_state_eq(new_s, va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
    va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
    va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s,
    va_update_globals(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s))))))))))))
    ensures va_state_eq(new_s, va_update_reg(EDX, new_s, va_update_reg(ECX, new_s,
    va_update_reg(EBX, new_s, va_update_reg(EAX, new_s, va_update_reg(EDI, new_s,
    va_update_reg(ESI, new_s, va_update_mem(new_s, va_update_reg(ESP, new_s, va_update_reg(EBP,
    new_s, va_update_globals(new_s, va_update_ok(new_s, old_s))))))))))))
    ensures va_state_eq(new_s, va_update_reg(EDI, new_s, va_update_reg(ESI, new_s,
    va_update_reg(EDX, new_s, va_update_reg(ECX, new_s, va_update_reg(EBX, new_s,
    va_update_reg(EAX, new_s, va_update_mem(new_s, va_update_reg(EBP, new_s, va_update_reg(ESP,
    new_s, va_update_globals(new_s, va_update_ok(new_s, old_s))))))))))))
{
    var s1 := va_update_globals(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s)));

    assert s1.wk_mstate.m == new_s.wk_mstate.m;
    assert s1.wk_mstate.globals == new_s.wk_mstate.globals;
    assert s1.ok == new_s.ok;
    //assert WKOps_UnchangedStateVars(s1, new_s);

    var s2 := va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
    va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
    va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s, s1))))))));

    assert s1.wk_mstate.m == s2.wk_mstate.m;
    assert s1.wk_mstate.globals == s2.wk_mstate.globals;
    assert s1.ok == s2.ok; 

    // Prove s2.wk_mstate.regs == new_s.wk_mstate.regs
    Lemma_EachRegsIsSameThenRegsAreSame(s2.wk_mstate.regs, new_s.wk_mstate.regs);
    assert s2.wk_mstate.regs == new_s.wk_mstate.regs;

    assert WKOps_UnchangedStateVars(s2, new_s);
}

lemma Lemma_modify_3regs_mem_stateeq(old_s:state, new_s:state)
    requires ValidState(old_s)
    requires ValidState(new_s)

    requires new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
    requires state_equal_except_mstate(old_s, new_s)

    ensures (va_get_reg(EAX, old_s) == va_get_reg(EAX, new_s) &&
            va_get_reg(EBX, old_s) == va_get_reg(EBX, new_s) &&
            va_get_reg(ECX, old_s) == va_get_reg(ECX, new_s) &&
            va_get_reg(EDX, old_s) == va_get_reg(EDX, new_s) &&
            va_get_reg(ESI, old_s) == va_get_reg(ESI, new_s) &&
            va_get_globals(old_s) == va_get_globals(new_s)
            )
        ==> va_state_eq(new_s, va_update_reg(EDI, new_s, va_update_mem(new_s, va_update_reg(ESP,
                new_s, va_update_reg(EBP, new_s, va_update_ok(new_s, old_s))))))
{
    Lemma_modify_regs_stateeq(old_s, new_s);
}

lemma Lemma_modify_regs_objects_stateeq(old_s:state, new_s:state)
    requires WK_ValidMState(old_s.wk_mstate)
    requires WK_ValidMState(new_s.wk_mstate)

    requires new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
    requires new_s.wk_mstate.globals == old_s.wk_mstate.globals
    requires old_s.subjects == new_s.subjects &&
            old_s.objs_addrs == new_s.objs_addrs &&
            old_s.id_mappings == new_s.id_mappings &&
            old_s.activate_conds == new_s.activate_conds &&
            old_s.ok == new_s.ok &&
            old_s.os_mem_active_map == new_s.os_mem_active_map

    ensures va_state_eq(new_s, va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
        va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
        va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s,
        va_update_objects(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s))))))))))))
{
    var s1 := va_update_objects(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s)));

    assert s1.wk_mstate.m == new_s.wk_mstate.m;
    assert s1.objects == new_s.objects;
    assert s1.ok == new_s.ok;

    var s2 := va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
    va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
    va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s, s1))))))));

    assert s1.wk_mstate.m == s2.wk_mstate.m;
    assert s1.wk_mstate.globals == s2.wk_mstate.globals;
    assert s1.ok == s2.ok; 

    // Prove s2.wk_mstate.regs == new_s.wk_mstate.regs
    Lemma_EachRegsIsSameThenRegsAreSame(s2.wk_mstate.regs, new_s.wk_mstate.regs);
    assert s2.wk_mstate.regs == new_s.wk_mstate.regs;

    assert s2.wk_mstate.globals == new_s.wk_mstate.globals;
    assert s2.wk_mstate == new_s.wk_mstate;
}

lemma Lemma_modify_regs_subjects_objects_stateeq(old_s:state, new_s:state)
    requires WK_ValidMState(old_s.wk_mstate)
    requires WK_ValidMState(new_s.wk_mstate)

    requires new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
    requires new_s.wk_mstate.globals == old_s.wk_mstate.globals
    requires old_s.objs_addrs == new_s.objs_addrs &&
            old_s.id_mappings == new_s.id_mappings &&
            old_s.activate_conds == new_s.activate_conds &&
            old_s.ok == new_s.ok &&
            old_s.os_mem_active_map == new_s.os_mem_active_map

    ensures va_state_eq(new_s, va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
        va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
        va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s,
        va_update_objects(new_s, va_update_subjects(new_s, va_update_mem(new_s, va_update_ok(new_s,
        old_s)))))))))))))
{
    var s1 := va_update_objects(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s)));

    assert s1.wk_mstate.m == new_s.wk_mstate.m;
    assert s1.objects == new_s.objects;
    assert s1.ok == new_s.ok;

    var s2 := va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
    va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
    va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s, s1))))))));

    assert s1.wk_mstate.m == s2.wk_mstate.m;
    assert s1.wk_mstate.globals == s2.wk_mstate.globals;
    assert s1.ok == s2.ok; 

    // Prove s2.wk_mstate.regs == new_s.wk_mstate.regs
    Lemma_EachRegsIsSameThenRegsAreSame(s2.wk_mstate.regs, new_s.wk_mstate.regs);
    assert s2.wk_mstate.regs == new_s.wk_mstate.regs;

    assert s2.wk_mstate.globals == new_s.wk_mstate.globals;
    assert s2.wk_mstate == new_s.wk_mstate;
}


lemma Lemma_modify_regs_subjects_objects_pmem_active_map_stateeq(old_s:state, new_s:state)
    requires WK_ValidMState(old_s.wk_mstate)
    requires WK_ValidMState(new_s.wk_mstate)

    requires new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
    requires new_s.wk_mstate.globals == old_s.wk_mstate.globals
    requires old_s.objs_addrs == new_s.objs_addrs &&
            old_s.id_mappings == new_s.id_mappings &&
            old_s.activate_conds == new_s.activate_conds &&
            old_s.ok == new_s.ok

    ensures  va_state_eq(new_s, va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
        va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
        va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s,
        va_update_os_mem_active_map(new_s, va_update_objects(new_s, va_update_subjects(new_s,
        va_update_mem(new_s, va_update_ok(new_s, old_s))))))))))))))
{
    var s1 := va_update_objects(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s)));

    assert s1.wk_mstate.m == new_s.wk_mstate.m;
    assert s1.objects == new_s.objects;
    assert s1.ok == new_s.ok;

    var s2 := va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
    va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
    va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s, s1))))))));

    assert s1.wk_mstate.m == s2.wk_mstate.m;
    assert s1.wk_mstate.globals == s2.wk_mstate.globals;
    assert s1.ok == s2.ok; 

    // Prove s2.wk_mstate.regs == new_s.wk_mstate.regs
    Lemma_EachRegsIsSameThenRegsAreSame(s2.wk_mstate.regs, new_s.wk_mstate.regs);
    assert s2.wk_mstate.regs == new_s.wk_mstate.regs;

    assert s2.wk_mstate.globals == new_s.wk_mstate.globals;
    assert s2.wk_mstate == new_s.wk_mstate;
}

lemma Lemma_x86_IfEFlagsIsUnchanged_ThenSRegsIsUnchanged(old_s:state, new_s:state, old_flags:word, new_flags:word)
    requires WK_ValidMState(old_s.wk_mstate)
    requires WK_ValidMState(new_s.wk_mstate)

    requires old_flags == va_get_sreg(EFLAGS, old_s)
    requires new_flags == va_get_sreg(EFLAGS, new_s)
    requires is_flags_unchanged(old_flags, new_flags)

    ensures new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
{
    assert is_valid_x86_sregs(new_s.wk_mstate.sregs);
    assert is_valid_x86_sregs(old_s.wk_mstate.sregs);

    assert forall e :: e in new_s.wk_mstate.sregs ==> e == EFLAGS;
}