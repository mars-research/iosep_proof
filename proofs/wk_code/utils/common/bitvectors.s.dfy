include "nlarith.s.dfy"
include "types.s.dfy"

// This file is copied from 
// https://github.com/microsoft/Komodo/blob/master/verified/bitvectors.s.dfy

/* Z3 gets hopelessly lost thinking about bitvectors, so we wrap both
 * the conversions and operations in opaque functions. We also need a
 * large number of axioms in this file, to work around limitations of
 * Z3's reasoning about the conversions between bitvectors and
 * ints. */

/* ================ Conversions ================ */
// [Math] Axiom (well known)
lemma {:axiom} lemma_UInt32AsBits(i:uint32)
    ensures i == 0 ==> i as bv32 == 0

function method {:opaque} UInt32AsBits(i:uint32): bv32
    ensures i == 0 <==> UInt32AsBits(i) == 0
{
    lemma_UInt32AsBits(i);
    i as bv32
}

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitsAsUInt32(b:bv32)
    ensures isUInt32(b as int)
    ensures b == 0 ==> b as int == 0

function method {:opaque} BitsAsUInt32(b:bv32): uint32
    ensures b == 0 <==> BitsAsUInt32(b) == 0
{
    lemma_BitsAsUInt32(b);
    (b as int) as uint32
}

// [Math] Axiom (well known)
lemma {:axiom} lemma_UInt32AsBitsAsUInt32(i:uint32)
    ensures BitsAsUInt32(UInt32AsBits(i)) == i

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitsAsUInt32AsBits(b:bv32)
    ensures UInt32AsBits(BitsAsUInt32(b)) == b

lemma lemma_UInt32BitsEquiv(i:uint32, b:bv32)
    requires i == BitsAsUInt32(b) || b == UInt32AsBits(i)
    ensures i == BitsAsUInt32(b) && b == UInt32AsBits(i)
{
    lemma_UInt32AsBitsAsUInt32(i);
    lemma_BitsAsUInt32AsBits(b);
}

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitsAreUnique(b1:bv32, b2:bv32)
    requires BitsAsUInt32(b1) == BitsAsUInt32(b2)
    ensures b1 == b2

/* ================ Primitives ================ */

function {:opaque} BitAdd(x:bv32, y:bv32): bv32
{
    x + y
}

function {:opaque} BitSub(x:bv32, y:bv32): bv32
{
    x - y
}

function {:opaque} BitAnd(x:bv32, y:bv32): bv32
{
    x & y
}

function {:opaque} BitOr(x:bv32, y:bv32): bv32
{
    x | y
}

function {:opaque} BitXor(x:bv32, y:bv32): bv32
{
    x ^ y
}

function {:opaque} BitMod(x:bv32, y:bv32): bv32
    requires y != 0
{
    x % y
}

function {:opaque} BitDiv(x:bv32, y:bv32): bv32
    requires y != 0
{
    x / y
}

function {:opaque} BitMul(x:bv32, y:bv32): bv32
{
    x * y
}

function {:opaque} BitNot(x:bv32): bv32
{
    !x
}

function {:opaque} BitShiftLeft(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x << amount
}

function {:opaque} BitShiftRight(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x >> amount
}

function {:opaque} BitRotateRight(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x.RotateRight(amount)
}

/* ================ Axioms relating the primitives ================ */
/* (it would be nice to prove these!) */

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitAddEquiv(x:uint32, y:uint32)
    requires isUInt32(x + y)
    ensures BitsAsUInt32(BitAdd(UInt32AsBits(x), UInt32AsBits(y))) == x + y

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitSubEquiv(x:uint32, y:uint32)
    requires isUInt32(x - y)
    ensures BitsAsUInt32(BitSub(UInt32AsBits(x), UInt32AsBits(y))) == x - y

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitModEquiv(x:uint32, y:uint32)
    requires y != 0
    ensures BitsAsUInt32(BitMod(UInt32AsBits(x), UInt32AsBits(y))) == x % y

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitDivEquiv(x:uint32, y:uint32)
    requires y != 0
    ensures BitsAsUInt32(BitDiv(UInt32AsBits(x), UInt32AsBits(y))) == x / y

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitMulEquiv(x:uint32, y:uint32)
    requires isUInt32(x * y)
    ensures BitsAsUInt32(BitMul(UInt32AsBits(x), UInt32AsBits(y))) == x * y

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitCmpEquiv(x:uint32, y:uint32)
    ensures x > y ==> UInt32AsBits(x) > UInt32AsBits(y)
    ensures x < y ==> UInt32AsBits(x) < UInt32AsBits(y)
    ensures x == y ==> UInt32AsBits(x) == UInt32AsBits(y)

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitRotatesRightSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures BitRotateRight(x, a + b) == BitRotateRight(BitRotateRight(x, a), b)

/* ================ Higher-level operations (needed for spec) ================ */


function {:opaque} pow2(n:nat): nat
    ensures pow2(n) > 0
{
    if n == 0 then 1 else 2 * pow2(n - 1)
}

function BitAtPos'(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    (1 as bv32 << bitpos)
}

// [Math] Axiom (well known)
lemma {:axiom} lemma_BitposPowerOf2(bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitsAsUInt32(BitAtPos'(bitpos)) == pow2(bitpos)

function {:opaque} BitAtPos(bitpos:int): bv32
    requires 0 <= bitpos < 32
    ensures BitAtPos(bitpos) != 0
    ensures BitsAsUInt32(BitAtPos(bitpos)) == pow2(bitpos)
{
    lemma_BitposPowerOf2(bitpos); BitAtPos'(bitpos)
}

function BitmaskLow(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    BitAtPos(bitpos) - 1
}

function BitmaskHigh(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    BitNot(BitmaskLow(bitpos))
}

// [Math] Axiom (well known)
lemma {:axiom} lemma_Bitmask(b:bv32, bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitAnd(b, BitmaskLow(bitpos)) == BitMod(b, BitAtPos(bitpos))
    ensures BitAnd(b, BitmaskHigh(bitpos))
        == BitMul(BitDiv(b, BitAtPos(bitpos)), BitAtPos(bitpos))
/* TODO: can't we prove this? */

lemma lemma_BitmaskAsUInt32(i:uint32, bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskLow(bitpos))) == i % pow2(bitpos)

    ensures BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskHigh(bitpos))) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskHigh(bitpos))) % pow2(bitpos) == 0
{
    lemma_BitmaskAsUInt32_Property1(i, bitpos);
    
    var b, pi := lemma_BitmaskAsUInt32_Property2and3_Inner(i, bitpos);
    lemma_BitmaskAsUInt32_Property2and3_Equal(i, bitpos, b, pi);
}

// useful properties of pow2 needed for spec
predicate pow2_properties(n:nat)
{
    (n >= 2 ==> pow2(n) % 4 == 0)
    && pow2(10) == 0x400
    && pow2(12) == 0x1000
}

lemma lemma_pow2_properties(n:nat)
    ensures pow2_properties(n)
{
    reveal pow2();
}

function {:opaque} BitwiseMaskHigh(i:uint32, bitpos:int): uint32
    requires 0 <= bitpos < 32;
    ensures BitwiseMaskHigh(i, bitpos) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitwiseMaskHigh(i, bitpos) % pow2(bitpos) == 0
    ensures pow2_properties(bitpos)
{
    lemma_BitmaskAsUInt32(i, bitpos);
    lemma_pow2_properties(bitpos);
    BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskHigh(bitpos)))
}

function {:opaque} BitwiseMaskLow(i:uint32, bitpos:int): uint32
    requires 0 <= bitpos < 32;
    ensures BitwiseMaskLow(i, bitpos) == i % pow2(bitpos)
    ensures pow2_properties(bitpos)
{
    lemma_BitmaskAsUInt32(i, bitpos);
    lemma_pow2_properties(bitpos);
    BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskLow(bitpos)))
}




/*********************** Private Lemmas ********************/
lemma lemma_BitmaskAsUInt32_Property1(i:uint32, bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskLow(bitpos))) == i % pow2(bitpos)
{
    var b := UInt32AsBits(i);
    lemma_UInt32BitsEquiv(i, b);
    var pb := BitAtPos(bitpos);
    var pi := pow2(bitpos);
    lemma_UInt32BitsEquiv(pi, pb);

    lemma_Bitmask(b, bitpos);

    assert BitsAsUInt32(BitAnd(b, BitmaskLow(bitpos))) == i % pi by {
        calc {
            BitsAsUInt32(BitAnd(b, BitmaskLow(bitpos)));
            BitsAsUInt32(BitMod(b, pb));
            { lemma_BitModEquiv(i, pi); }
            i % pi;
        }
    }
}

lemma lemma_BitmaskAsUInt32_Property2_Inner(i:uint32, bitpos:int) returns (b:bv32, pi:nat)
    requires 0 <= bitpos < 32

    ensures b == UInt32AsBits(i)
    ensures pi == pow2(bitpos)

    ensures BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi
{
    reveal UInt32AsBits();
    reveal BitsAsUInt32();
    reveal pow2();

    b := UInt32AsBits(i);
    lemma_UInt32BitsEquiv(i, b);
    var pb := BitAtPos(bitpos);
    pi := pow2(bitpos);
    lemma_UInt32BitsEquiv(pi, pb);

    lemma_Bitmask(b, bitpos);

    assert BitsAsUInt32(BitAnd(b, BitmaskLow(bitpos))) == i % pi by {
        calc {
            BitsAsUInt32(BitAnd(b, BitmaskLow(bitpos)));
            BitsAsUInt32(BitMod(b, pb));
            { lemma_BitModEquiv(i, pi); }
            i % pi;
        }
    }

    assert BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi by {
        calc {
            BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos)));
            BitsAsUInt32(BitMul(BitDiv(b, pb), pb));
            { lemma_BitsAsUInt32AsBits(BitDiv(b, pb)); }
            BitsAsUInt32(BitMul(UInt32AsBits(BitsAsUInt32(BitDiv(b, pb))), pb));
            {
                lemma_BitsAsUInt32AsBits(BitDiv(b, pb));
                lemma_DivMulLessThan(i, pi);
                assert BitsAsUInt32(BitDiv(b, pb)) == i / pi by { lemma_BitDivEquiv(i, pi); }
                assert i >= 0 && pi > 0;
                lemma_DivBounds(i, pi); lemma_MulSign(i / pi, pi);
                assert i / pi * pi >= 0;
                lemma_BitMulEquiv(BitsAsUInt32(BitDiv(b, pb)), pi);
            }
            BitsAsUInt32(BitDiv(b, pb)) * BitsAsUInt32(pb);
            { lemma_BitDivEquiv(i, pi); }
            i / pi * pi;
        }
    }

    assert BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi;
}

lemma lemma_BitmaskAsUInt32_Property2and3_Inner(i:uint32, bitpos:int) returns (b:bv32, pi:nat)
    requires 0 <= bitpos < 32

    ensures b == UInt32AsBits(i)
    ensures pi == pow2(bitpos)

    ensures BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi
    ensures BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) % pi == 0
{
    b, pi := lemma_BitmaskAsUInt32_Property2_Inner(i, bitpos);

    lemma_MulModZero(i / pi, pi);
}


lemma lemma_BitmaskAsUInt32_Property2and3_Equal(i:uint32, bitpos:int, b:bv32, pi:nat)
    requires 0 <= bitpos < 32
    requires b == UInt32AsBits(i)
    requires pi == pow2(bitpos)

    requires BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi
    requires BitsAsUInt32(BitAnd(b, BitmaskHigh(bitpos))) % pi == 0
    
    ensures BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskHigh(bitpos))) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitsAsUInt32(BitAnd(UInt32AsBits(i), BitmaskHigh(bitpos))) % pow2(bitpos) == 0
{
    // Dafny can automatically prove this lemma
}