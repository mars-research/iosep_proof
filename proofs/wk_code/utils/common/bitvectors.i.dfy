include "bitvectors.s.dfy"
include "bitvector_uint.s.dfy"
include "bitvectors_primitive.i.dfy"


lemma lemma_BitShiftsRightSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures BitShiftRight(x, a + b) == BitShiftRight(BitShiftRight(x, a), b)
{
    lemma_ShiftsRightSum(x, a, b);
    reveal BitShiftRight();
}

lemma lemma_BitShiftsLeftSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures BitShiftLeft(x, a + b) == BitShiftLeft(BitShiftLeft(x, a), b)
{
    lemma_ShiftsLeftSum(x, a, b);
    reveal BitShiftLeft();
}

lemma lemma_BitOrCommutative(a: bv32, b:bv32)
    ensures BitOr(a, b) == BitOr(b, a)
{ reveal BitOr(); }

lemma lemma_BitOrAssociative(a: bv32, b:bv32, c: bv32)
    ensures BitOr(a, BitOr(b, c)) == BitOr(BitOr(a, b), c)
{ reveal BitOr(); }

lemma lemma_BitAndCommutative(a: bv32, b:bv32)
    ensures BitAnd(a, b) == BitAnd(b, a)
{ reveal BitAnd(); }

lemma lemma_BitAndAssociative(a: bv32, b:bv32, c: bv32)
    ensures BitAnd(a, BitAnd(b, c)) == BitAnd(BitAnd(a, b), c)
{ reveal BitAnd(); }

lemma lemma_BitOrAndRelation(a: bv32, b:bv32, c: bv32)
    ensures BitAnd(BitOr(a, b), c) == BitOr(BitAnd(a, c), BitAnd(b, c))
{ reveal BitAnd(); reveal_BitOr(); }

lemma lemma_BitPos12()
    ensures BitsAsUInt32(BitAtPos(12)) == 0x1000
{
    lemma_pow2_properties(12);
}

lemma lemma_BitShiftLeft1(x: bv32)
    requires x < 0x80000000
    ensures BitShiftLeft(x, 1) == BitMul(x, 2)
{
    calc {
        BitShiftLeft(x, 1);
        { reveal BitShiftLeft(); }
        x << 1;
        x * 2;
        { reveal BitMul(); }
        BitMul(x, 2);
    }
}

lemma lemma_BitShiftRight1(x: bv32)
    ensures BitShiftRight(x, 1) == BitDiv(x, 2)
{
    calc {
        BitShiftRight(x, 1);
        { reveal BitShiftRight(); }
        x >> 1;
        x / 2;
        { reveal BitDiv(); }
        BitDiv(x, 2);
    }
}

lemma lemma_LeftShift1(x: uint32)
    requires x < 0x80000000
    ensures LeftShift(x, 1) == x * 2
{
    calc {
        LeftShift(x, 1);
        BitsAsUInt32(BitShiftLeft(UInt32AsBits(x), 1));
        { lemma_BitCmpEquiv(x, 0x80000000);
          assert UInt32AsBits(0x80000000) == 0x80000000 by { reveal UInt32AsBits(); }
          lemma_BitShiftLeft1(UInt32AsBits(x)); }
        BitsAsUInt32(BitMul(UInt32AsBits(x), 2));
        { assert UInt32AsBits(2) == 2 by { reveal UInt32AsBits(); } }
        BitsAsUInt32(BitMul(UInt32AsBits(x), UInt32AsBits(2)));
        { lemma_BitMulEquiv(x, 2); }
        x * 2;
    }
}

lemma lemma_RightShift1(x: uint32)
    ensures RightShift(x, 1) == x / 2
{
    calc {
        RightShift(x, 1);
        BitsAsUInt32(BitShiftRight(UInt32AsBits(x), 1));
        { lemma_BitShiftRight1(UInt32AsBits(x)); }
        BitsAsUInt32(BitDiv(UInt32AsBits(x), 2));
        { assert UInt32AsBits(2) == 2 by { reveal UInt32AsBits(); } }
        BitsAsUInt32(BitDiv(UInt32AsBits(x), UInt32AsBits(2)));
        { lemma_BitDivEquiv(x, 2); }
        x / 2;
    }
}

lemma lemma_ShiftsAdd(x: uint32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures LeftShift(x, a + b) == LeftShift(LeftShift(x, a), b)
    ensures RightShift(x, a + b) == RightShift(RightShift(x, a), b)
{
    calc {
        LeftShift(x, a + b);
        BitsAsUInt32(BitShiftLeft(UInt32AsBits(x), a + b));
        { lemma_BitShiftsLeftSum(UInt32AsBits(x), a, b); }
        BitsAsUInt32(BitShiftLeft(BitShiftLeft(UInt32AsBits(x), a), b));
        { lemma_BitsAsUInt32AsBits(BitShiftLeft(UInt32AsBits(x), a)); }
        BitsAsUInt32(BitShiftLeft(UInt32AsBits(BitsAsUInt32(BitShiftLeft(UInt32AsBits(x), a))), b));
        BitsAsUInt32(BitShiftLeft(UInt32AsBits(LeftShift(x, a)), b));
        LeftShift(LeftShift(x, a), b);
    }

    calc {
        RightShift(x, a + b);
        BitsAsUInt32(BitShiftRight(UInt32AsBits(x), a + b));
        { lemma_BitShiftsRightSum(UInt32AsBits(x), a, b); }
        BitsAsUInt32(BitShiftRight(BitShiftRight(UInt32AsBits(x), a), b));
        { lemma_BitsAsUInt32AsBits(BitShiftRight(UInt32AsBits(x), a)); }
        BitsAsUInt32(BitShiftRight(UInt32AsBits(BitsAsUInt32(BitShiftRight(UInt32AsBits(x), a))), b));
        BitsAsUInt32(BitShiftRight(UInt32AsBits(RightShift(x, a)), b));
        RightShift(RightShift(x, a), b);
    }
}

lemma lemma_LeftShift2(x: uint32)
    requires x < 0x40000000
    ensures LeftShift(x, 2) == x * 4
{
    var x' := LeftShift(x, 1);
    lemma_LeftShift1(x);
    lemma_LeftShift1(x');
    lemma_ShiftsAdd(x, 1, 1);
}

lemma lemma_LeftShift3(x: uint32)
    requires x < 0x20000000
    ensures LeftShift(x, 3) == x * 8
{
    var x' := LeftShift(x, 2);
    lemma_LeftShift2(x);
    lemma_LeftShift1(x');
    lemma_ShiftsAdd(x, 2, 1);
}

lemma lemma_LeftShift4(x: uint32)
    requires x < 0x10000000
    ensures LeftShift(x, 4) == x * 16
{
    var x' := LeftShift(x, 2);
    lemma_LeftShift2(x);
    lemma_LeftShift2(x');
    lemma_ShiftsAdd(x, 2, 2);
}

lemma lemma_LeftShift12(x: uint32)
    requires x < 0x100000
    ensures LeftShift(x, 12) == x * 4096
{
    var x' := LeftShift(x, 4);
    lemma_LeftShift4(x);
    var x'' := LeftShift(x', 4);
    lemma_LeftShift4(x');
    lemma_ShiftsAdd(x, 4, 4);
    assert x'' == LeftShift(x, 8);
    assert x'' == x * 256;
    var x''' := LeftShift(x'', 4);
    lemma_LeftShift4(x'');
    assert x''' == x * 4096;
    lemma_ShiftsAdd(x, 8, 4);
    assert x''' == LeftShift(x, 12);
}



lemma lemma_LeftShift16(x: uint32)
    requires x < 0x10000
    ensures LeftShift(x, 16) == x * 0x10000
{
    var x' := LeftShift(x, 4);
    lemma_LeftShift4(x);
    lemma_LeftShift12(x');
    lemma_ShiftsAdd(x, 4, 12);

    assert LeftShift(x, 16) == LeftShift(LeftShift(x, 4), 12);
    assert LeftShift(x, 16) == x * 16 * 4096;
    
    lemma_MulAssociative(x, 16, 4096);
    assert x * 0x10000 == x * 16 * 4096;
}

lemma lemma_RightShift2(x: uint32)
    ensures RightShift(x, 2) == x / 4
{
    var x' := RightShift(x, 1);
    lemma_RightShift1(x);
    lemma_RightShift1(x');
    lemma_ShiftsAdd(x, 1, 1);
}

lemma lemma_RightShift4(x: uint32)
    ensures RightShift(x, 4) == x / 16
{
    var x' := RightShift(x, 2);
    lemma_RightShift2(x);
    lemma_RightShift2(x');
    lemma_ShiftsAdd(x, 2, 2);
}

lemma lemma_RightShift7(x: uint32)
    ensures RightShift(x, 7) == x / 128
{
    var x' := RightShift(x, 4);
    lemma_RightShift4(x);
    var x'' := RightShift(x', 2);
    lemma_RightShift2(x');
    lemma_ShiftsAdd(x, 4, 2);
    assert x'' == RightShift(x, 6);
    assert x'' == x / 64;
    var x''' := RightShift(x'', 1);
    lemma_RightShift1(x'');
    lemma_ShiftsAdd(x, 6, 1);
    assert x''' == x / 128;
}

lemma lemma_RightShift12(x: uint32)
    ensures RightShift(x, 12) == x / 4096
{
    var x' := RightShift(x, 4);
    lemma_RightShift4(x);
    var x'' := RightShift(x', 4);
    lemma_RightShift4(x');
    lemma_ShiftsAdd(x, 4, 4);
    assert x'' == RightShift(x, 8);
    assert x'' == x / 256;
    var x''' := RightShift(x'', 4);
    lemma_RightShift4(x'');
    assert x''' == x / 4096;
    lemma_ShiftsAdd(x, 8, 4);
    assert x''' == RightShift(x, 12);
}

lemma lemma_RightShift16(x: uint32)
    ensures RightShift(x, 16) == x / 0x10000
{
    var x' := RightShift(x, 4);
    lemma_RightShift4(x);
    lemma_RightShift12(x');
    lemma_ShiftsAdd(x, 4, 12);
}

lemma lemma_ExpandBitwiseOr(a: uint32, b: uint32, c: uint32)
    ensures BitwiseOr(BitwiseOr(a, b), c)
        == BitsAsUInt32(BitOr(BitOr(UInt32AsBits(a), UInt32AsBits(b)), UInt32AsBits(c)))
{
    lemma_BitsAsUInt32AsBits(BitOr(UInt32AsBits(a), UInt32AsBits(b)));
}

lemma lemma_BitwiseOrAssociative(a: uint32, b: uint32, c: uint32)
    ensures BitwiseOr(BitwiseOr(a, b), c) == BitwiseOr(a, BitwiseOr(b, c))
{
    calc {
        BitwiseOr(BitwiseOr(a, b), c);
        { lemma_ExpandBitwiseOr(a, b, c); }
        BitsAsUInt32(BitOr(BitOr(UInt32AsBits(a), UInt32AsBits(b)), UInt32AsBits(c)));
        { lemma_BitOrAssociative(UInt32AsBits(a), UInt32AsBits(b), UInt32AsBits(c)); }
        BitsAsUInt32(BitOr(UInt32AsBits(a), BitOr(UInt32AsBits(b), UInt32AsBits(c))));
        { lemma_BitsAsUInt32AsBits(BitOr(UInt32AsBits(b), UInt32AsBits(c))); }
        BitwiseOr(a, BitwiseOr(b, c));
    }
}

lemma lemma_BitsAndUInt32Conversions()
    // to avoid matching loops, we give of these a more restrictive trigger:
    ensures forall w:uint32 :: BitsAsUInt32(UInt32AsBits(w)) == w;
    ensures forall b:bv32 {:trigger UInt32AsBits(BitsAsUInt32(b))} :: UInt32AsBits(BitsAsUInt32(b)) == b;
{
    forall w:uint32 
        ensures BitsAsUInt32(UInt32AsBits(w)) == w;
    {
        lemma_UInt32AsBitsAsUInt32(w);
    }
    forall b:bv32
        ensures UInt32AsBits(BitsAsUInt32(b)) == b;
    {
        lemma_BitsAsUInt32AsBits(b);
    }
}

lemma lemma_load_32_bit_const_bv(c:bv32)
    ensures c == BitOr(BitShiftLeft(BitShiftRight(c, 16), 16), BitAnd(BitMod(c, 0x10000), 0xffff))
{
    reveal BitOr();
    reveal BitAnd();
    reveal BitShiftLeft();
    reveal BitShiftRight();
    reveal BitMod();
}

lemma lemma_load_32_bit_const_uint32(c:uint32)
    ensures c == UpdateTopBits(c % 0x10000, BitsAsUInt32(BitShiftRight(UInt32AsBits(c), 16)))
{
    assert BitmaskLow(16) == 0xffff by { reveal BitAtPos(); }
    assert BitsAsUInt32(0x10000) == 0x10000 by { reveal BitsAsUInt32(); }
    reveal UpdateTopBits();
    reveal BitwiseMaskLow();
    lemma_BitModEquiv(c, 0x10000);
    lemma_load_32_bit_const_bv(UInt32AsBits(c));
    lemma_BitsAndUInt32Conversions();
}

lemma {:timeLimitMultiplier 1} lemma_load_32_bit_const(c:uint32)
    ensures c == UpdateTopBits(c % 0x10000, BitsAsUInt32(UInt32AsBits(c) >> 16))
{
    lemma_load_32_bit_const_uint32(c);
    reveal BitShiftRight();

    var x :=  UInt32AsBits(c);

    assert BitShiftRight(UInt32AsBits(c), 16) == BitShiftRight(x, 16);
    assert BitShiftRight(x, 16) == x >> 16;
    assert BitShiftRight(UInt32AsBits(c), 16) == UInt32AsBits(c) >> 16;
}

lemma lemma_MaskReturnUInt16()
    ensures forall a:uint32 :: isUInt16(BitwiseAnd(a, 0x0000_ffff))
{
    reveal BitsAsUInt32();
    reveal UInt32AsBits();
    reveal BitAnd();
}

lemma lemma_MaskReturnUInt7()
    ensures forall a:uint32 :: 0 <= BitwiseAnd(a, 0x7F) < 128
{
    reveal BitsAsUInt32();
    reveal UInt32AsBits();
    reveal BitAnd();
}






/*********************** Axioms ********************/
// [Math] Axiom (well known)
lemma {:axiom} lemma_Bitmask12()
    ensures BitmaskLow(12) == 0xfff
    ensures BitmaskHigh(12) == 0xfffff000
    // This lemma causes errors in Dafny 2.3.0. And this lemma was proved in 
    // https://github.com/microsoft/Komodo/blob/master/verified/bitvectors.i.dfy

// [Math] Axiom (well known)
lemma {:axiom} lemma_Bitmask10()
    ensures BitmaskLow(10) == 0x3ff
    ensures BitmaskHigh(10) == 0xfffffc00
    // This lemma causes errors in Dafny 2.3.0. And this lemma was proved in 
    // https://github.com/microsoft/Komodo/blob/master/verified/bitvectors.i.dfy