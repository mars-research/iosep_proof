include "types.s.dfy"
include "nlarith.s.dfy"
include "uint32_ops.s.dfy"

lemma Lemma_NTimesUInt32IsStillAligned(num1:uint32, num2:uint32)
    requires UInt32Aligned(num2)
    requires isUInt32(num1 * num2)

    ensures UInt32Aligned(num1 * num2)
{
    reveal UInt32Aligned();

    if(num1 == 0)
    {
        assert UInt32Aligned(0);
        assert num1 * num2 == 0 * num2 == 0;
        assert UInt32Aligned(num1 * num2);
    }
    else
    {
        assert num1 >= 1;
        Lemma_NatMul_Ineq_4var(num1-1, num2, num1, num2);

        var val := (num1-1) * num2;
        lemma_MulSign(num1-1, num2);
        Lemma_NTimesUInt32IsStillAligned(num1-1, num2);
        assert UInt32Aligned(val);

        Lemma_UInt32Mul_Add(num1, num2);
        assert num1 * num2 == val + num2;
        assert num1 * num2 == UInt32AlignedAdd(val, num2);
    }
}