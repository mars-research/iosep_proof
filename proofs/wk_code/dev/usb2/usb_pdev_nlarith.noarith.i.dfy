include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"

// Lemma: For any given vaddr in g_wimpdevs_info, there is only one pair of td_slot and offset can yield that vaddr
lemma Lemma_usbpdev_slot_offset_UniquePairForVAddr()
    ensures forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 ::
                0 <= slot1 < WimpUSBPDev_Info_ENTRIES && 0 <= slot2 < WimpUSBPDev_Info_ENTRIES &&
                0 <= offset1 < WimpUSBPDev_Info_ENTRY_SZ && 0 <= offset2 < WimpUSBPDev_Info_ENTRY_SZ
            ==> ((slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2)
                    <==> (slot1 == slot2 && offset1 == offset2))
{
    reveal p_usbpdev_slot_offset_UniquePairForVAddr(); 
    Lemma_usbpdev_slot_offset_UniquePairForVAddr_inner();
}

lemma Lemma_usbpdev_slot_offset_UniquePairForVAddr_ForContradictionProof(slot1:uint32, offset1:uint32, slot2:uint32, offset2:uint32)
    requires 0 <= slot1 < WimpUSBPDev_Info_ENTRIES
    requires 0 <= offset1 < WimpUSBPDev_Info_ENTRY_SZ

    requires 0 <= slot2 < WimpUSBPDev_Info_ENTRIES
    requires 0 <= offset2 < WimpUSBPDev_Info_ENTRY_SZ

    requires slot1 != slot2
    requires slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2

    ensures false
{
    Lemma_usbpdev_slot_offset_UniquePairForVAddr();
}




/*********************** Private Lemmas ********************/
predicate {:opaque} p_usbpdev_slot_offset_UniquePairForVAddr(slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32)
{
    0 <= slot1 < WimpUSBPDev_Info_ENTRIES && 0 <= slot2 < WimpUSBPDev_Info_ENTRIES &&
    0 <= offset1 < WimpUSBPDev_Info_ENTRY_SZ && 0 <= offset2 < WimpUSBPDev_Info_ENTRY_SZ
}

// Lemma: For any given vaddr in g_wimpdevs_info, there is only one pair of td_slot and offset can yield that vaddr
lemma Lemma_usbpdev_slot_offset_UniquePairForVAddr_inner()
    ensures forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 ::
                p_usbpdev_slot_offset_UniquePairForVAddr(slot1, slot2, offset1, offset2)
            ==> ((slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2)
                    <==> (slot1 == slot2 && offset1 == offset2))
{
    reveal p_usbpdev_slot_offset_UniquePairForVAddr();

    forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 |
                p_usbpdev_slot_offset_UniquePairForVAddr(slot1, slot2, offset1, offset2)
        ensures ((slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2)
                    ==> (slot1 == slot2 && offset1 == offset2))
    {
        if(slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2)
        {
            if(slot1 > slot2)
            {
                lemma_MulDistrib_Sub(slot1, slot2, WimpUSBPDev_Info_ENTRY_SZ);
                assert slot1 * WimpUSBPDev_Info_ENTRY_SZ - slot2 * WimpUSBPDev_Info_ENTRY_SZ == (slot1 - slot2) * WimpUSBPDev_Info_ENTRY_SZ;
                assert (slot1 - slot2) * WimpUSBPDev_Info_ENTRY_SZ == offset2 - offset1;

                assert (slot1 - slot2) >= 1;
                Lemma_NatMul_Ineq_4var(1, WimpUSBPDev_Info_ENTRY_SZ, (slot1 - slot2), WimpUSBPDev_Info_ENTRY_SZ);
                assert offset2 - offset1 >= WimpUSBPDev_Info_ENTRY_SZ;

                assert false;
            }

            if(slot1 < slot2)
            {
                lemma_MulDistrib_Sub(slot2, slot1, WimpUSBPDev_Info_ENTRY_SZ);
                assert slot2 * WimpUSBPDev_Info_ENTRY_SZ - slot1 * WimpUSBPDev_Info_ENTRY_SZ == (slot2 - slot1) * WimpUSBPDev_Info_ENTRY_SZ;
                assert (slot2 - slot1) * WimpUSBPDev_Info_ENTRY_SZ == offset1 - offset2;

                assert (slot2 - slot1) >= 1;
                Lemma_NatMul_Ineq_4var(1, WimpUSBPDev_Info_ENTRY_SZ, (slot2 - slot1), WimpUSBPDev_Info_ENTRY_SZ);
                assert offset2 - offset1 >= WimpUSBPDev_Info_ENTRY_SZ;

                assert false;
            }
        }
    }

    forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 |
                p_usbpdev_slot_offset_UniquePairForVAddr(slot1, slot2, offset1, offset2)
        ensures ((slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2)
                    <== (slot1 == slot2 && offset1 == offset2))
    {
        if(slot1 == slot2 && offset1 == offset2)
        {
            assert slot1 * WimpUSBPDev_Info_ENTRY_SZ + offset1 == slot2 * WimpUSBPDev_Info_ENTRY_SZ + offset2;
        }
    }
}