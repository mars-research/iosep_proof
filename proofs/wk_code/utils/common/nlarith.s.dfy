

include "types.s.dfy"

lemma lemma_DivMulEqual(a:nat, b:nat)
    requires b > 0
    requires a % b == 0
    ensures (a / b) * b == a
{}


lemma lemma_DivMulLessThan(a:int, b:int)
    requires b > 0
    ensures (a / b) * b <= a
{}

lemma lemma_AddWrapAssociates(x1:nat, x2:nat, x3:nat)
    ensures (((x1 + x2) % 0x1_0000_0000) + x3) % 0x1_0000_0000
         == (x1 + ((x2 + x3) % 0x1_0000_0000)) % 0x1_0000_0000;
{
}

lemma lemma_DivBounds(a:int, b:int)
    requires a >= 0 && b > 0
    ensures 0 <= (a / b) <= a
{
    if a < b {
        lemma_DivBounds_ALessThanB(a,b);
        assert a / b == 0;
    } else if a == b {
        assert a / b == 1;
    } else if b == 1 {
        assert a / b == a;
    } else if a > b {
        lemma_DivBounds_AGreaterThanB(a,b);
        assert 1 <= a / b;
        lemma_DivBounds'(a, b);
    }
}

lemma lemma_MulSign(a:int, b:int)
    requires a >= 0 && b >= 0
    ensures a * b >= 0
{}

lemma lemma_MulDistrib(a:int, b:int, c:int)
    ensures (a + b) * c == a * c + b * c
{}

lemma lemma_MulAssociative(a:int, b:int, c:int)
    ensures (a * b) * c == a * (b * c)
{}

lemma Lemma_IntMul_EqualityOfMinusN(a:int)
    ensures -1 * a == 0-a
{
    // Dafny can automatically prove this lemma
}


lemma Lemma_NatMul_Ineq_4var(a:nat, b:nat, c:nat, d:nat)
    requires 0 <= a <= c
    requires 0 <= b <= d 
    ensures 0 <= a * b <= c * d
{
    Lemma_NatMul_Ineq(a, c, b);
    Lemma_NatMul_Ineq(b, d, c);
    assert a * b <= c * b;
    assert c * b <= c * d;
}

lemma Lemma_UInt32Mul_Range()
    ensures forall a:uint32, b:uint32 :: isUInt64(a*b)
{
    assert 0xFFFF_FFFF * 0xFFFF_FFFF < UINT64_LIM;
    forall a:uint32, b:uint32 ensures a * b <= 0xFFFF_FFFF * 0xFFFF_FFFF
    {
        if(a != 0 && b != 0)
        {
            Lemma_NatMul_Ineq_4var(a, b, 0xFFFF_FFFF, 0xFFFF_FFFF);
        }
    }
}

function method roundup(n:nat, num:nat):nat
    requires num != 0
    ensures roundup(n, num) - num < n <= roundup(n, num)
{
    if(n % num == 0) then
        n
    else
        (n / num + 1) * num
}




/*********************** Axioms ********************/
// [Math] Axiom (well known)
lemma {:axiom} lemma_MulModZero(a:int, b:int)
    requires b > 0
    ensures (a * b) % b == 0
/* FIXME: prove this! */

// [Math] Axiom (well known)
lemma {:axiom} lemma_DivBounds'(a:int, b:int)
    requires a > b > 0
    ensures a / b < a
/* FIXME: this is unstable, but proves in some versions of Dafny/Z3 */

// [Math] Axiom (well known)
lemma {:axiom} lemma_Div_SameSign_Positive(a:int, b:int)
    requires a >= 0
    requires b > 0
    ensures a/b >= 0
    // Refer to lemma_div_pos_is_pos in 
    // https://github.com/microsoft/Ironclad/blob/master/ironfleet/src/Dafny/Libraries/Math/div.i.dfy for proof

// [Math] Axiom (well known)
lemma {:axiom} lemma_DivBounds_ALessThanB(a:int, b:int)
    requires b > a >= 0
    ensures a / b == 0
    // Refer to lemma_basic_div in 
    // https://github.com/microsoft/Ironclad/blob/master/ironfleet/src/Dafny/Libraries/Math/div.i.dfy for proof

// [Math] Axiom (well known)
lemma {:axiom} lemma_DivBounds_AGreaterThanB(a:int, b:int)
    requires a > b > 0
    ensures a / b >= 1

// [Math] Axiom (well known)
lemma {:axiom} Lemma_NatMul_Ineq(a:nat, b:nat, c:nat)
    requires b >= a
    requires c >= 0
    ensures b * c >= a * c >= 0

// [Math] Axiom (well known)
lemma {:axiom} Lemma_IntMul_Ineq(a:int, b:int, c:nat)
    requires b >= a
    requires c >= 0
    ensures b * c >= a * c

// [Math] Axiom (well known)
lemma {:axiom} Lemma_NatMul_Ineq_NoEqualRight(a:nat, b:nat, c:nat)
    requires a < b
    requires 0 <= c
    ensures  0 <= a * c < b * c

// [Math] Axiom (well known)
lemma {:axiom} Lemma_MulUin32UpperBound()
    ensures forall a:uint32, b:uint32 :: isUInt64(a*b)

// [Math] Axiom (well known)
lemma {:axiom} Lemma_UInt32Mul_Add(a:uint32, b:uint32)
    ensures a * b == (a-1) * b + b

// [Math] Axiom (well known)
lemma {:axiom} lemma_MulDistrib_Sub(a:int, b:int, c:int)
    ensures (a - b) * c == a * c - b * c