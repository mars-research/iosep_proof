include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"

// Any word aligned offset in G_Temp_USBTD() is a valid gvar vaddr
lemma Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(offset:uint32)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires WordAligned(offset)

    ensures var td_addr := AddressOfGlobal(G_Temp_USBTD()) + offset;
            is_gvar_valid_addr(G_Temp_USBTD(), td_addr) &&
            is_gvar_valid_vaddr(G_Temp_USBTD(), td_addr)
{
    lemma_DistinctGlobals();
}

// Lemma: For any given vaddr in g_usbtd_map_mem, there is only one pair of td_slot and offset can yield that vaddr
lemma Lemma_usbtd_slot_offset_UniquePairForVAddr()
    ensures forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 ::
                0 <= slot1 < USB_TD_ENTRY_NUM && 0 <= slot2 < USB_TD_ENTRY_NUM &&
                0 <= offset1 < G_USBTDs_MAP_ENTRY_SZ && 0 <= offset2 < G_USBTDs_MAP_ENTRY_SZ
            ==> ((slot1 * G_USBTDs_MAP_ENTRY_SZ + offset1 == slot2 * G_USBTDs_MAP_ENTRY_SZ + offset2)
                    <==> (slot1 == slot2 && offset1 == offset2))
{
    forall slot1:uint32, slot2:uint32, offset1:uint32, offset2:uint32 |
                0 <= slot1 < USB_TD_ENTRY_NUM && 0 <= slot2 < USB_TD_ENTRY_NUM &&
                0 <= offset1 < G_USBTDs_MAP_ENTRY_SZ && 0 <= offset2 < G_USBTDs_MAP_ENTRY_SZ
        ensures ((slot1 * G_USBTDs_MAP_ENTRY_SZ + offset1 == slot2 * G_USBTDs_MAP_ENTRY_SZ + offset2)
                    ==> (slot1 == slot2 && offset1 == offset2))
    {
        if(slot1 * G_USBTDs_MAP_ENTRY_SZ + offset1 == slot2 * G_USBTDs_MAP_ENTRY_SZ + offset2)
        {
            if(slot1 > slot2)
            {
                lemma_MulDistrib_Sub(slot1, slot2, G_USBTDs_MAP_ENTRY_SZ);
                assert slot1 * G_USBTDs_MAP_ENTRY_SZ - slot2 * G_USBTDs_MAP_ENTRY_SZ == (slot1 - slot2) * G_USBTDs_MAP_ENTRY_SZ;
                assert (slot1 - slot2) * G_USBTDs_MAP_ENTRY_SZ == offset2 - offset1;

                assert (slot1 - slot2) >= 1;
                Lemma_NatMul_Ineq_4var(1, G_USBTDs_MAP_ENTRY_SZ, (slot1 - slot2), G_USBTDs_MAP_ENTRY_SZ);
                assert offset2 - offset1 >= G_USBTDs_MAP_ENTRY_SZ;

                assert false;
            }

            if(slot1 < slot2)
            {
                lemma_MulDistrib_Sub(slot2, slot1, G_USBTDs_MAP_ENTRY_SZ);
                assert slot2 * G_USBTDs_MAP_ENTRY_SZ - slot1 * G_USBTDs_MAP_ENTRY_SZ == (slot2 - slot1) * G_USBTDs_MAP_ENTRY_SZ;
                assert (slot2 - slot1) * G_USBTDs_MAP_ENTRY_SZ == offset1 - offset2;

                assert (slot2 - slot1) >= 1;
                Lemma_NatMul_Ineq_4var(1, G_USBTDs_MAP_ENTRY_SZ, (slot2 - slot1), G_USBTDs_MAP_ENTRY_SZ);
                assert offset2 - offset1 >= G_USBTDs_MAP_ENTRY_SZ;

                assert false;
            }
        }
    }
}

lemma Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(slot1:uint32, offset1:uint32, slot2:uint32, offset2:uint32)
    requires 0 <= slot1 < USB_TD_ENTRY_NUM
    requires 0 <= offset1 < G_USBTDs_MAP_ENTRY_SZ

    requires 0 <= slot2 < USB_TD_ENTRY_NUM
    requires 0 <= offset2 < G_USBTDs_MAP_ENTRY_SZ

    requires slot1 != slot2
    requires slot1 * G_USBTDs_MAP_ENTRY_SZ + offset1 == slot2 * G_USBTDs_MAP_ENTRY_SZ + offset2

    ensures false
{
    Lemma_usbtd_slot_offset_UniquePairForVAddr();
}