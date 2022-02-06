include "../utils/common/headers.dfy"
include "../arch/headers.dfy"

/*********************** State Invariants, Transition Constraints and Related Functions ********************/
predicate WK_ValidMemState(s:WK_MState)
{
    WK_Mem_Separate_Segs() &&

    (true)
}




/*********************** Other Definitions And Utility Functions ********************/
predicate IsAddrInStack(addr:word)
{
    is_valid_addr(addr) && is_valid_vaddr(addr) && is_vaddr_in_stack(addr)
}




/*********************** Utility Lemmas ********************/
lemma Lemma_IsAddrInStack_Property(base:word, offset1:word, offset2:word)
    requires WordAligned(offset2)

    requires IsAddrInStack(base)
    requires isWord(base + offset1)
    requires IsAddrInStack(base + offset1)
    requires 0 <= offset2 <= offset1

    ensures IsAddrInStack(base + offset2)
{
    assert WK_StackSeg_Limit() <= base + offset1 < WK_StackSeg_Base();
    assert offset2 <= offset1;
    assert WK_StackSeg_Limit() <= base + offset2 < WK_StackSeg_Base();
}