include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"

// Given a valid eEHCI slot, and offset less than eEHCI_INSTANCE_BYTES, then 
// slot * eEHCI_INSTANCE_BYTES + offset < G_EEHCI_MEM_SZ_Tight
// [NOTE] Needs 10s to verify
lemma Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot:uint32, offset:uint32)
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires 0 <= offset < eEHCI_INSTANCE_BYTES

    ensures slot * eEHCI_INSTANCE_BYTES + offset < G_EEHCI_MEM_SZ_Tight
{
    var tmp := slot * eEHCI_INSTANCE_BYTES + offset;
    assert G_EEHCI_MEM_SZ_Tight == eEHCI_INSTANCE_BYTES * eEHCI_INSTANCE_NUM;
    assert eEHCI_INSTANCE_NUM - slot >= 1;

    Lemma_NatMul_Ineq_4var(1, eEHCI_INSTANCE_BYTES, (eEHCI_INSTANCE_NUM - slot), eEHCI_INSTANCE_BYTES);
    assert eEHCI_INSTANCE_BYTES <= (eEHCI_INSTANCE_NUM - slot) * eEHCI_INSTANCE_BYTES;
    lemma_MulDistrib(eEHCI_INSTANCE_NUM, 0-slot, eEHCI_INSTANCE_BYTES);
    assert G_EEHCI_MEM_SZ_Tight - slot * eEHCI_INSTANCE_BYTES == (eEHCI_INSTANCE_NUM - slot) * eEHCI_INSTANCE_BYTES;
    assert G_EEHCI_MEM_SZ_Tight - slot * eEHCI_INSTANCE_BYTES >= eEHCI_INSTANCE_BYTES;
    assert tmp < G_EEHCI_MEM_SZ_Tight;
}

// Lemma: For any given vaddr in g_eehci_mem, there is only one pair of td_slot and offset can yield that vaddr
lemma Lemma_eehci_slot_offset_UniquePairForVAddr()
    ensures forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 ::
                0 <= slot1 < eEHCI_INSTANCE_NUM && 0 <= slot2 < eEHCI_INSTANCE_NUM &&
                0 <= offset1 < eEHCI_INSTANCE_BYTES && 0 <= offset2 < eEHCI_INSTANCE_BYTES
            ==> ((slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2)
                    <==> (slot1 == slot2 && offset1 == offset2))
{
    reveal p_eehci_slot_offset_UniquePairForVAddr(); 
    Lemma_eehci_slot_offset_UniquePairForVAddr_inner();
}

lemma Lemma_eehci_slot_offset_UniquePairForVAddr_ForContradictionProof(slot1:uint32, offset1:uint32, slot2:uint32, offset2:uint32)
    requires 0 <= slot1 < eEHCI_INSTANCE_NUM
    requires 0 <= offset1 < eEHCI_INSTANCE_BYTES

    requires 0 <= slot2 < eEHCI_INSTANCE_NUM
    requires 0 <= offset2 < eEHCI_INSTANCE_BYTES

    requires slot1 != slot2
    requires slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2

    ensures false
{
    Lemma_eehci_slot_offset_UniquePairForVAddr();
}

// Given a valid eEHCI slot, and word aligned offset less than eEHCI_INSTANCE_BYTES, then 
// slot * eEHCI_INSTANCE_BYTES + offset is a valid gvar vaddr
// [NOTE] Needs 150s to verify
lemma Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(slot:uint32, offset:uint32)
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires WordAligned(offset)

    ensures var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), td_addr) &&
            is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr)
{
    lemma_DistinctGlobals();

    var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;

    // Prove td_addr >= 0
    lemma_MulSign(slot, eEHCI_INSTANCE_BYTES);
    assert td_addr >= 0;

    // Prove isUInt32(td_addr)
    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, offset);
    assert isUInt32(td_addr);

    // Prove td_addr is a vaddr
    assert WordAlignedMul(eEHCI_INSTANCE_BYTES, slot) == slot * eEHCI_INSTANCE_BYTES;
    assert WordAlignedAdd(WordAlignedAdd(AddressOfGlobal(G_EEHCI_MEM()), slot * eEHCI_INSTANCE_BYTES), offset) == td_addr;
    
    // Prove is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr)
    assert offset < eEHCI_INSTANCE_BYTES;
    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, offset);
    assert is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr);
}




/*********************** Private Lemmas ********************/
predicate {:opaque} p_eehci_slot_offset_UniquePairForVAddr(slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32)
{
    0 <= slot1 < eEHCI_INSTANCE_NUM && 0 <= slot2 < eEHCI_INSTANCE_NUM &&
    0 <= offset1 < eEHCI_INSTANCE_BYTES && 0 <= offset2 < eEHCI_INSTANCE_BYTES
}

// Lemma: For any given vaddr in g_eehci_mem, there is only one pair of td_slot and offset can yield that vaddr
lemma Lemma_eehci_slot_offset_UniquePairForVAddr_inner()
    ensures forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 ::
                p_eehci_slot_offset_UniquePairForVAddr(slot1, slot2, offset1, offset2)
            ==> ((slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2)
                    <==> (slot1 == slot2 && offset1 == offset2))
{
    reveal p_eehci_slot_offset_UniquePairForVAddr();

    forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 |
                p_eehci_slot_offset_UniquePairForVAddr(slot1, slot2, offset1, offset2)
        ensures ((slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2)
                    ==> (slot1 == slot2 && offset1 == offset2))
    {
        if(slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2)
        {
            if(slot1 > slot2)
            {
                lemma_MulDistrib_Sub(slot1, slot2, eEHCI_INSTANCE_BYTES);
                assert slot1 * eEHCI_INSTANCE_BYTES - slot2 * eEHCI_INSTANCE_BYTES == (slot1 - slot2) * eEHCI_INSTANCE_BYTES;
                assert (slot1 - slot2) * eEHCI_INSTANCE_BYTES == offset2 - offset1;

                assert (slot1 - slot2) >= 1;
                Lemma_NatMul_Ineq_4var(1, eEHCI_INSTANCE_BYTES, (slot1 - slot2), eEHCI_INSTANCE_BYTES);
                assert offset2 - offset1 >= eEHCI_INSTANCE_BYTES;

                assert false;
            }

            if(slot1 < slot2)
            {
                lemma_MulDistrib_Sub(slot2, slot1, eEHCI_INSTANCE_BYTES);
                assert slot2 * eEHCI_INSTANCE_BYTES - slot1 * eEHCI_INSTANCE_BYTES == (slot2 - slot1) * eEHCI_INSTANCE_BYTES;
                assert (slot2 - slot1) * eEHCI_INSTANCE_BYTES == offset1 - offset2;

                assert (slot2 - slot1) >= 1;
                Lemma_NatMul_Ineq_4var(1, eEHCI_INSTANCE_BYTES, (slot2 - slot1), eEHCI_INSTANCE_BYTES);
                assert offset2 - offset1 >= eEHCI_INSTANCE_BYTES;

                assert false;
            }
        }
    }

    forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 |
                p_eehci_slot_offset_UniquePairForVAddr(slot1, slot2, offset1, offset2)
        ensures ((slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2)
                    <== (slot1 == slot2 && offset1 == offset2))
    {
        if(slot1 == slot2 && offset1 == offset2)
        {
            assert slot1 * eEHCI_INSTANCE_BYTES + offset1 == slot2 * eEHCI_INSTANCE_BYTES + offset2;
        }
    }
}