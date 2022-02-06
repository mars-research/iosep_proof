include "bitvector_uint.s.dfy"

// [Math] Axiom (well known)
lemma {:axiom} Lemma_BitwiseAndFFFFYieldsUInt16(a:uint32)
    ensures isUInt16(BitwiseAnd(a, 0xFFFF))

// [Math] Axiom (well known): If a value has a bit set, then test the bit returns true
lemma {:axiom} Lemma_TestBit_ReturnTrueIfANumberSetBit(flag_bit:uint32)
    requires 0 <= flag_bit < 32
    ensures forall v:uint32 :: TestBit(SetBit(v, flag_bit), flag_bit) == true

// [Math] Axiom (well known): If a value is 0, then test any bit returns false
lemma {:axiom} Lemma_TestBit_ReturnFalseIfANumberIs0()
    ensures forall flag_bit :: 0 <= flag_bit < 32 ==> TestBit(0, flag_bit) == false

// [Math] Axiom (well known): If a value v has no bit <flag_bit> set, it still has this bit not set, even after setting other bits 
lemma {:axiom} Lemma_TestBit_ReturnFalse_IfBitNotSetAndAfterSetOtherBits(flag_bit:uint32)
    requires 0 <= flag_bit < 32
    ensures forall v:uint32, other_bit:uint32 :: 0 <= other_bit < 32 && TestBit(v, flag_bit) == false
                ==> TestBit(SetBit(v, other_bit), flag_bit) == false

// [Math] Axiom (well known): SetBit operation is associative
lemma {:axiom} Lemma_SetBit_Associative(flag_bit1:uint32, flag_bit2:uint32)
    requires 0 <= flag_bit1 < 32
    requires 0 <= flag_bit2 < 32
    ensures forall v:uint32 :: SetBit(SetBit(v, flag_bit1), flag_bit2)
                == SetBit(SetBit(v, flag_bit2), flag_bit1)

// [Math] Axiom (well known): BitwiseAnd(0, _) == 0
lemma {:axiom} Lemma_BitAnd_Return0IfANumberIs0()
    ensures forall i :: BitwiseAnd(0, i) == 0

lemma Lemma_BitAndEquiv(v1:uint32, v2:uint32)
    ensures BitwiseAnd(v1, v2) == BitsAsUInt32(BitAnd(UInt32AsBits(v1), UInt32AsBits(v2)))
{
    reveal BitAnd();

    var bit_result:bv32 := BitAnd(UInt32AsBits(v1), UInt32AsBits(v2));
    assert BitwiseAnd(v1, v2) == BitsAsUInt32(bit_result);
}

