include "arch_mem.dfy"

// Lemma: If [startC, endC) is in [startB, endB), and [startA, endA) does not overlap with [startB, endB), then
// [startA, endA) does not overlap with [startC, endC)
lemma Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(startA:addr, endA:uint, startB:addr, endB:uint, startC:addr, endC:uint)
    requires startA <= endA
    requires startB <= endB
    requires startC <= endC

    requires is_mem_region_inside(startB, endB, startC, endC)
    requires !is_mem_region_overlap(startA, endA, startB, endB)

    ensures !is_mem_region_overlap(startA, endA, startC, endC)
{
    // Dafny can automatically prove this lemma
}