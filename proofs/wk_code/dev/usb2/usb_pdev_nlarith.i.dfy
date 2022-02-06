include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"
include "usb_pdev_nlarith.noarith.i.dfy"

// Given a valid USBPDev slot, and offset less than WimpUSBPDev_Info_ENTRY_SZ, then 
// slot * WimpUSBPDev_Info_ENTRY_SZ + offset < G_WimpUSBPDev_Info_SZ
// [NOTE] Needs 10s to verify
lemma Lemma_usbpdev_slot_offset_AlwaysInGUSBPDevMem(slot:uint32, offset:uint32)
    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires 0 <= offset < WimpUSBPDev_Info_ENTRY_SZ

    ensures slot * WimpUSBPDev_Info_ENTRY_SZ + offset < G_WimpUSBPDev_Info_SZ
{
    var tmp := slot * WimpUSBPDev_Info_ENTRY_SZ + offset;
    assert G_WimpUSBPDev_Info_SZ == WimpUSBPDev_Info_ENTRY_SZ * WimpUSBPDev_Info_ENTRIES;
    assert WimpUSBPDev_Info_ENTRIES - slot >= 1;

    Lemma_NatMul_Ineq_4var(1, WimpUSBPDev_Info_ENTRY_SZ, (WimpUSBPDev_Info_ENTRIES - slot), WimpUSBPDev_Info_ENTRY_SZ);
    assert WimpUSBPDev_Info_ENTRY_SZ <= (WimpUSBPDev_Info_ENTRIES - slot) * WimpUSBPDev_Info_ENTRY_SZ;
    lemma_MulDistrib(WimpUSBPDev_Info_ENTRIES, 0-slot, WimpUSBPDev_Info_ENTRY_SZ);
    assert G_WimpUSBPDev_Info_SZ - slot * WimpUSBPDev_Info_ENTRY_SZ == (WimpUSBPDev_Info_ENTRIES - slot) * WimpUSBPDev_Info_ENTRY_SZ;
    assert G_WimpUSBPDev_Info_SZ - slot * WimpUSBPDev_Info_ENTRY_SZ >= WimpUSBPDev_Info_ENTRY_SZ;
    assert tmp < G_WimpUSBPDev_Info_SZ;
}



// Given a valid USBPDev slot, and word aligned offset less than WimpUSBPDev_Info_ENTRY_SZ, then 
// slot * WimpUSBPDev_Info_ENTRY_SZ + offset is a valid gvar vaddr
// [NOTE] Needs 150s to verify
lemma Lemma_usbpdev_slot_offset_AlwaysValidGUSBPDevAddr(slot:uint32, offset:uint32)
    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires 0 <= offset < WimpUSBPDev_Info_ENTRY_SZ
    requires WordAligned(offset)

    ensures var td_addr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_WimpUSBPDev_Info(), td_addr) &&
            is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), td_addr)
{
    lemma_DistinctGlobals();

    var td_addr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + offset;

    // Prove td_addr >= 0
    lemma_MulSign(slot, WimpUSBPDev_Info_ENTRY_SZ);
    assert td_addr >= 0;

    // Prove isUInt32(td_addr)
    Lemma_usbpdev_slot_offset_AlwaysInGUSBPDevMem(slot, offset);
    assert isUInt32(td_addr);

    // Prove td_addr is a vaddr
    assert WordAlignedMul(WimpUSBPDev_Info_ENTRY_SZ, slot) == slot * WimpUSBPDev_Info_ENTRY_SZ;
    assert WordAlignedAdd(WordAlignedAdd(AddressOfGlobal(G_WimpUSBPDev_Info()), slot * WimpUSBPDev_Info_ENTRY_SZ), offset) == td_addr;
    
    // Prove is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), td_addr)
    assert offset < WimpUSBPDev_Info_ENTRY_SZ;
    Lemma_usbpdev_slot_offset_AlwaysInGUSBPDevMem(slot, offset);
    assert is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), td_addr);
}