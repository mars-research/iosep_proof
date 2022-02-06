include "types.s.dfy"
include "nlarith.s.dfy"

function UInt32AlignedAdd(x1:int, x2:int): int
    requires UInt32Aligned(x1) && UInt32Aligned(x2)
    ensures  UInt32Aligned(UInt32AlignedAdd(x1, x2))
{
    reveal UInt32Aligned();
    x1 + x2
}

function UInt32AlignedSub(x1:int, x2:int): int
    requires UInt32Aligned(x1) && UInt32Aligned(x2)
    ensures  UInt32Aligned(UInt32AlignedSub(x1, x2))
{
    reveal UInt32Aligned();
    x1 - x2
}

function UInt32AlignedMul(x1:uint32, N:int): uint32
    requires UInt32Aligned(x1)
    requires N >= 0
    requires isUInt32(x1 * N)

    ensures UInt32Aligned(UInt32AlignedMul(x1, N))
    ensures UInt32AlignedMul(x1, N) == x1 * N
{
    reveal UInt32Aligned();

    if(N == 0) then
        assert x1 * 0 == 0;
        0
    else
        assert N >= 1;
        Lemma_NatMul_Ineq_4var(x1, N-1, x1, N);
        var result := UInt32AlignedAdd(x1, UInt32AlignedMul(x1, N-1));
        assert result == x1 + x1 * (N-1);
        lemma_MulDistrib_Sub(N, 1, x1);
        assert result == x1 * N;
        result
}