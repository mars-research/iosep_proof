include "../usb_tds.i.dfy"

// Lemma: if Non-Scratchpad GlobalVars is unchanged, then global variable always satisfy eehci_mem_no_ref_to_usbtd_slot
lemma Lemma__usbtd_slot_submit_usbtd_UnmodifiedGEEHCIMem(globals1:globalsmap, globals2:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires usbtd_map_valid_slot_id(usbtd_slot_id)
    
    requires p_usbtd_slot_submit_usbtd_ret_global(globals1, globals2, usbtd_slot_id);
    ensures global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM());
{
    // Dafny can automatically prove this lemma
}
