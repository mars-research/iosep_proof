// This file holds WK memory functions (Dafny spec) common to different architectures
include "../types.dfy"


/*********************** Utility Functions ********************/
// If two regions overlap, one region is [startA, endA), and the second one is [startB, endB)
// [NOTE] if startB == endA or otherwise, then the two regions are separate
// [NOTE] endA and endB should be uint instead of addr, because endA/endB could be ARCH_WORD_LIMIT
predicate is_mem_region_overlap(startA:addr, endA:uint, startB:addr, endB:uint)
    requires startA <= endA
    requires startB <= endB
{
    if (startA == endA) then // if memory region A is 0-size, it is not considered as overlap with B
        false
    else if (startB == endB) then // if memory region B is 0-size, it is not considered as overlap with A
        false
    else if (startB <= startA < endB) then
        true
    else if (startA <= startB < endA) then
        true
    else
        false
}

// If region B is inside region A, one region is [startA, endA), and the second one is [startB, endB)
// [NOTE] endA and endB should be uint instead of addr, because endA/endB could be ARCH_WORD_LIMIT
predicate is_mem_region_inside(startA:addr, endA:uint, startB:addr, endB:uint)
    requires startA <= endA
    requires startB <= endB
{
    if (startA == endA) then // if memory region A is 0-size, it cannot contain any memory region
        false
    else if (startA <= startB) && (endB <= endA) then
        true
    else
        false
}

// If region A includes the addr, region A is [startA, endA)
predicate is_mem_region_include_addr(startA:addr, endA:uint, addr:addr)
    requires startA < endA
{
    if (startA <= addr < endA) then
        true
    else
        false
}