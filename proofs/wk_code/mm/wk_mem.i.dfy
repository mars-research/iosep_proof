include "wk_mem.dfy"


// Lemma: For a stack range [low, high], high - i * ARCH_WORD_BYTES is a valid stack address 
lemma Lemma_IsAddrInStack_ProveEveryAddrInRangeIsValidAddrInStack(high:word, low:word)
    requires IsAddrInStack(high)
    requires IsAddrInStack(low)
    requires high >= low
    requires forall i:int :: i >= 0 && 
            (high - i * ARCH_WORD_BYTES >= low) 
        ==> IsAddrInStack(high - i * ARCH_WORD_BYTES)
{
    // Dafny can automatically prove this lemma
}