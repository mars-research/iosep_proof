include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"
include "usb_tds_nlarith.noarith.i.dfy"

// Given a valid USB TD slot, and offset less than G_USBTDs_MAP_ENTRY_SZ, then 
// slot * G_USBTDs_MAP_ENTRY_SZ + offset < G_USBTDs_MAP_MEM_SZ_Tight
// [NOTE] Needs 30s to verify
lemma Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot:uint32, offset:uint32)
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ

    ensures slot * G_USBTDs_MAP_ENTRY_SZ + offset < G_USBTDs_MAP_MEM_SZ_Tight
{
    var tmp := slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    assert G_USBTDs_MAP_MEM_SZ_Tight == G_USBTDs_MAP_ENTRY_SZ * USB_TD_ENTRY_NUM;
    assert USB_TD_ENTRY_NUM - slot >= 1;

    Lemma_NatMul_Ineq_4var(1, G_USBTDs_MAP_ENTRY_SZ, (USB_TD_ENTRY_NUM - slot), G_USBTDs_MAP_ENTRY_SZ);
    assert G_USBTDs_MAP_ENTRY_SZ <= (USB_TD_ENTRY_NUM - slot) * G_USBTDs_MAP_ENTRY_SZ;
    lemma_MulDistrib(USB_TD_ENTRY_NUM, 0-slot, G_USBTDs_MAP_ENTRY_SZ);
    assert G_USBTDs_MAP_MEM_SZ_Tight - slot * G_USBTDs_MAP_ENTRY_SZ == (USB_TD_ENTRY_NUM - slot) * G_USBTDs_MAP_ENTRY_SZ;
    assert G_USBTDs_MAP_MEM_SZ_Tight - slot * G_USBTDs_MAP_ENTRY_SZ >= G_USBTDs_MAP_ENTRY_SZ;
    assert tmp < G_USBTDs_MAP_MEM_SZ_Tight;
}

// Given a valid USB TD slot, and word aligned offset less than G_USBTDs_MAP_ENTRY_SZ, then 
// slot * G_USBTDs_MAP_ENTRY_SZ + offset is a valid gvar vaddr
// [NOTE] Needs 150s to verify
lemma Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot:uint32, offset:uint32)
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires WordAligned(offset)

    ensures var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr) &&
            is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), td_addr)
{
    lemma_DistinctGlobals();

    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;

    // Prove td_addr >= 0
    lemma_MulSign(slot, G_USBTDs_MAP_ENTRY_SZ);
    assert td_addr >= 0;

    // Prove isUInt32(td_addr)
    Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot, offset);
    assert isUInt32(td_addr);

    // Prove td_addr is a vaddr
    assert WordAlignedMul(G_USBTDs_MAP_ENTRY_SZ, slot) == slot * G_USBTDs_MAP_ENTRY_SZ;
    assert WordAlignedAdd(WordAlignedAdd(AddressOfGlobal(G_USBTD_MAP_MEM()), slot * G_USBTDs_MAP_ENTRY_SZ), offset) == td_addr;
    
    // Prove is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), td_addr)
    assert offset < G_USBTDs_MAP_ENTRY_SZ;
    Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot, offset);
    assert is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), td_addr);
}

// Lemma: The start address of <TD> in a given USB TD slot must be a valid vaddr and a vaddr in the <g_usbtd_map_mem>
// [NOTE] Needs 50s to verify
lemma Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot:uint32)
    requires 0 <= td_slot < USB_TD_ENTRY_NUM

    ensures var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            is_valid_addr(td_vaddr) &&
            is_valid_vaddr(td_vaddr) &&
            is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), td_vaddr)
{
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
}