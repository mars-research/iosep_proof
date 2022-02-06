include "types.s.dfy"


/*********************** Axioms (Better to be proved) ********************/
// [Math] Axiom (well known): n * PAGE_4K_SZ is page aligned, n >= 0
lemma {:axiom} Lemma_NTimesPage4KSZIsPageAligned(n:nat)
    ensures PageAligned(n * PAGE_4K_SZ)
