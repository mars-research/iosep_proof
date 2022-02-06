include "../ffi/usb_tds.ffi.s.dfy"
include "../../../mm/wk_globals.dfy"
include "../usb_tds.s.dfy"

/*********************** Axioms ********************/
// [HW] Axiom (related): If most fields of the secure USB TDs are unchanged, and the given USB TD is secure, then
// Is_USBTD_NotModifyUSBPDevsAddrs holds
// [NOTE] This axiom makes sense, because (1) we know that secure USB TDs can only ref secure USB TDs, and (2) USBPDev's
// info slot refed by a secure USB TD cannot be modified
// [NOTE] This axiom relates to the axiom <Is_USBTD_NotModifyUSBPDevsAddrs>
lemma {:axiom} Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged(
    globals1:globalsmap, globals2:globalsmap, td_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && 
                    TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
                ==> (p_usbtd_content_equal(globals1, globals2, i) &&
                     usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i) &&
                     usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i))
        // Requirement: Secure USB TDs are unchanged
    requires TestBit(usbtd_map_get_flags(globals1, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The USB TD <td_slot> is secure

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot)


// [HW] Axiom (related): If only temp global variables are changed, then Is_USBTD_NotModifyUSBPDevsAddrs holds
// [NOTE] This axiom makes sense, because all global variables that map to state variables in WK design are unchanged
// [NOTE] This axiom relates to the axiom <Is_USBTD_NotModifyUSBPDevsAddrs>
/*lemma Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfNonTempGVarsAreUnchanged(globals1:globalsmap, globals2:globalsmap, td_slot:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires global_non_scratchpad_vars_are_unchanged(globals1, globals2)
    requires usbtd_map_valid_slot_id(td_slot)

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot) */


// [HW] Axiom (related): Equivilant of <Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged> for QTD32
// [NOTE] This axiom relates to the axiom <Is_USBTD_NotModifyUSBPDevsAddrs>
lemma {:axiom} Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged_QTD32(
    globals1:globalsmap, globals2:globalsmap, td_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && 
                    TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
                ==> (p_usbtd_content_equal(globals1, globals2, i) &&
                     usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i) &&
                     usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i))
        // Requirement: Secure USB TDs are unchanged
    requires var slot_type := usbtd_map_get_type(globals1, td_slot);
             slot_type == USBTDs_TYPE_QTD32 &&
             WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, td_slot)
        // Requirement: The USB TD <td_slot> is secure

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot)


// [HW] Axiom (related): Equivilant of <Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged> for QH32
// [NOTE] This axiom relates to the axiom <Is_USBTD_NotModifyUSBPDevsAddrs>
lemma {:axiom} Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged_QH32(
    globals1:globalsmap, globals2:globalsmap, td_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && 
                    TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
                ==> (p_usbtd_content_equal(globals1, globals2, i) &&
                     usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i) &&
                     usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i))
        // Requirement: Secure USB TDs are unchanged
    requires var slot_type := usbtd_map_get_type(globals1, td_slot);
             slot_type == USBTDs_TYPE_QH32 &&
             WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, td_slot)
        // Requirement: The USB TD <td_slot> is secure

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot)




/*********************** State Invariants and Related Predicates ********************/
predicate WK_USBTD_Map_SecureGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)
{
    // 1. In each slot of <g_usbtd_map_mem>, the USBTD fulfills *_OnSuccessCheck
    (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals, i) == USBTDs_TYPE_QTD32)
        ==> WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, i)) &&

    (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals, i) == USBTDs_TYPE_QH32)
        ==> WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, i)) &&

    (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals, i) == USBTDs_TYPE_iTD32)
        ==> WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals, i)) &&

    (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals, i) == USBTDs_TYPE_siTD32)
        ==> WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals, i)) &&
        
    (true)
}

predicate WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)
{
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    usbtd_idword != USBTD_ID_INVALID &&

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    wimpdrv_valid_slot_id(drv_slot) &&
    wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&

    var drv_pid := wimpdrv_get_pid(globals, drv_slot);
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    (wimpdrv_do_pbase <= wimpdrv_do_pend) &&

    p__usbtd_verify_qtd32_step1_OnSuccessCheck(globals, drv_pid.v, td_slot) &&
    p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals, drv_pid.v, td_slot) &&
    p__usbtd_verify_qtd32_step3_OnSuccessCheck(globals, drv_slot, td_slot) &&
    p__usbtd_verify_qtd32_step4_OnSuccessCheck(globals, td_slot) &&

    // Secure USB TD cannot modify any USBPDevs' USB addresses
    Is_USBTD_NotModifyUSBPDevsAddrs(globals, td_slot)
}

predicate WK_USBTD_Map_SecureGlobalVarValues_qh32(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)
{
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    usbtd_idword != USBTD_ID_INVALID &&

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    wimpdrv_valid_slot_id(drv_slot) &&
    wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&

    var drv_pid := wimpdrv_get_pid(globals, drv_slot);

    var pdev_slot := usbtd_map_get_usbpdev_slotid(globals, td_slot);
    usbpdev_valid_slot_id(pdev_slot) &&

    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    (wimpdrv_do_pbase <= wimpdrv_do_pend) &&

    p__usbtd_verify_qh32_step1_OnSuccessCheck(globals, drv_pid.v, td_slot) &&
    p__usbtd_verify_qh32_step2_OnSuccessCheck(globals, drv_pid.v, td_slot) &&
    p__usbtd_verify_qh32_step3_OnSuccessCheck(globals, td_slot, pdev_slot) &&
    p__usbtd_verify_qh32_step4_OnSuccessCheck(globals, drv_slot, td_slot) &&

    // Secure USB TD cannot modify any USBPDevs' USB addresses
    Is_USBTD_NotModifyUSBPDevsAddrs(globals, td_slot)
}

predicate WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)
{
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    usbtd_idword != USBTD_ID_INVALID &&

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    wimpdrv_valid_slot_id(drv_slot) &&
    wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&

    var drv_id := wimpdrv_get_id_word(globals, drv_slot);
    var drv_pid := wimpdrv_get_pid(globals, drv_slot);

    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    (wimpdrv_do_pbase <= wimpdrv_do_pend) &&

    p__usbtd_verify_qtd32_step1_OnSuccessCheck(globals, drv_pid.v, td_slot) && 
    p__usbtd_verify_qtd32_step4_OnSuccessCheck(globals, td_slot) // [TODO] Not support iTD and siTD yet

    // [TODO] Secure USB TD cannot modify any USBPDevs' USB addresses
    //&& Is_USBTD_NotModifyUSBPDevsAddrs(globals, td_slot)
}

predicate WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)
{
    var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
    usbtd_idword != USBTD_ID_INVALID &&
    
    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    wimpdrv_valid_slot_id(drv_slot) &&
    wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&

    var drv_id := wimpdrv_get_id_word(globals, drv_slot);
    var drv_pid := wimpdrv_get_pid(globals, drv_slot);

    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    (wimpdrv_do_pbase <= wimpdrv_do_pend) &&

    p__usbtd_verify_qtd32_step1_OnSuccessCheck(globals, drv_pid.v, td_slot) &&
    p__usbtd_verify_qtd32_step4_OnSuccessCheck(globals, td_slot) // [TODO] Not support iTD and siTD yet

    // [TODO] Secure USB TD cannot modify any USBPDevs' USB addresses
    // && Is_USBTD_NotModifyUSBPDevsAddrs(globals, td_slot)
}




/*********************** Predicates of Checks ********************/
// The predicates when <_usbtd_verify_qtd32_step1> return true
predicate {:opaque} p__usbtd_verify_qtd32_step1_OnSuccessCheck(globals:globalsmap, drv_pid:word, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    drv_pid != PID_INVALID &&
    drv_pid != PID_RESERVED_OS_PARTITION &&
    usbtd_map_get_pid(globals, td_slot) == WS_PartitionID(drv_pid)
}

// The predicates when <_usbtd_verify_qtd32_step2> return true
predicate {:opaque} p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals:globalsmap, drv_pid:word, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
    // According to EHCI specification, Section 3.5. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

    (
        next_qtd_p_Tflag == 1 || 
        (
            (0 <= next_qtd_slot < USB_TD_ENTRY_NUM) && 
            usbtd_map_get_pid(globals, next_qtd_slot) == WS_PartitionID(drv_pid) &&
            TestBit(usbtd_map_get_flags(globals, next_qtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
                    // The USB TD <next_slot> must be a verified/secure one
        )
    ) &&
    (
        alt_next_qtd_p_Tflag == 1 || 
        (
            (0 <= alt_next_qtd_slot < USB_TD_ENTRY_NUM) && 
            usbtd_map_get_pid(globals, alt_next_qtd_slot) == WS_PartitionID(drv_pid) &&
            TestBit(usbtd_map_get_flags(globals, alt_next_qtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
                    // The USB TD <next_slot> must be a verified/secure one
        )
    )
}

// The predicates when <_usbtd_verify_qtd32_step3> return true
predicate {:opaque} p__usbtd_verify_qtd32_step3_OnSuccessCheck(globals:globalsmap, drv_slot:word, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires 0 <= drv_slot < WimpDrv_Info_ENTRIES;
    requires var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
            var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
            (wimpdrv_do_pbase <= wimpdrv_do_pend)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 7 * UINT32_BYTES);
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);

    var r_buf0_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 3 * UINT32_BYTES), 0xFFFFF000); // According to EHCI specification, Section 3.5
    var r_buf1_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0xFFFFF000);
    var r_buf2_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0xFFFFF000);
    var r_buf3_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 6 * UINT32_BYTES), 0xFFFFF000);
    var r_buf4_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 7 * UINT32_BYTES), 0xFFFFF000);

    (is_valid_addr(r_buf0_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf0_p, r_buf0_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf1_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf1_p, r_buf1_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf2_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf2_p, r_buf2_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf3_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf3_p, r_buf3_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf4_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf4_p, r_buf4_p + PAGE_4K_SZ))
}

// The predicates when <_usbtd_verify_qtd32_step4> return true
predicate {:opaque} p__usbtd_verify_qtd32_step4_OnSuccessCheck(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var pdev_slot := usbtd_map_get_usbpdev_slotid(globals, td_slot);

    pdev_slot == WimpUSBPDev_SlotID_EMPTY
}

// The predicates when <_usbtd_verify_qh32_step1> return true
predicate {:opaque} p__usbtd_verify_qh32_step1_OnSuccessCheck(globals:globalsmap, drv_pid:word, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    drv_pid != PID_INVALID &&
    drv_pid != PID_RESERVED_OS_PARTITION &&
    usbtd_map_get_pid(globals, td_slot) == WS_PartitionID(drv_pid)
}

// The predicates when <_usbtd_verify_qh32_step2> return true
predicate {:opaque} p__usbtd_verify_qh32_step2_OnSuccessCheck(globals:globalsmap, drv_pid:word, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qh_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qh_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

    (
        next_qh_p_Tflag == 1 || 
        (
            (0 <= next_qh_slot < USB_TD_ENTRY_NUM) && 
            usbtd_map_get_pid(globals, next_qh_slot) == WS_PartitionID(drv_pid) &&
            TestBit(usbtd_map_get_flags(globals, next_qh_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
                // The USB TD <next_slot> must be a verified/secure one
        )
    ) &&
    (
        next_qtd_p_Tflag == 1 || 
        (
            (0 <= next_qtd_slot < USB_TD_ENTRY_NUM) && 
            usbtd_map_get_pid(globals, next_qtd_slot) == WS_PartitionID(drv_pid) &&
            TestBit(usbtd_map_get_flags(globals, next_qtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
                // The USB TD <next_slot> must be a verified/secure one
        )
    ) &&
    (
        alt_next_qtd_p_Tflag == 1 || 
        (
            (0 <= alt_next_qtd_slot < USB_TD_ENTRY_NUM) && 
            usbtd_map_get_pid(globals, alt_next_qtd_slot) == WS_PartitionID(drv_pid) &&
            TestBit(usbtd_map_get_flags(globals, alt_next_qtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
                // The USB TD <next_slot> must be a verified/secure one
        )
    )
}

// The predicates when <_usbtd_verify_qh32_step3> return true
predicate {:opaque} p__usbtd_verify_qh32_step3_OnSuccessCheck(globals:globalsmap, td_slot:uint32, pdev_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)
    requires usbpdev_valid_slot_id(pdev_slot) 
{
    var usbpdev_addr_raw := usbpdev_get_addr(globals, pdev_slot);
    var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
    var empty_addr:USBPDev_Addr := usb_parse_usbpdev_addr(empty_addr_raw);

    // 1. The TD info at <td_slot> can generate USBPDev ID
    usbtd_qh32_can_parse_TargetUSBDevID_from_global(globals, td_slot) &&
    // 2. The PDev info must not be in the middle of updating
    usbpdev_get_updateflag(globals, pdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
    (
        var dest_pdev_addr:USBPDev_Addr := usbtd_qh32_parse_TargetUSBPDevAddr_from_global(globals, td_slot);
        var found_pdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

        // 3. The USBPDev Addr generated from the TD info at <td_slot> must not be empty addr 
        (found_pdev_addr != empty_addr) &&
        // 4. The USBPDev Addr generated from the TD info at <td_slot> must be equal to the USBPDev ID stored in <pdev_slot>
        (dest_pdev_addr == found_pdev_addr)  &&
        // 5. The TD and the USBPDev must be in the same partition
        (usbtd_map_get_pid(globals, td_slot) == usbpdev_get_pid(globals, pdev_slot))
    )
}

// The predicates when <_usbtd_verify_qh32_step4> return true
predicate {:opaque} p__usbtd_verify_qh32_step4_OnSuccessCheck(globals:globalsmap, drv_slot:word, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires 0 <= drv_slot < WimpDrv_Info_ENTRIES;
    requires var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
            var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
            (wimpdrv_do_pbase <= wimpdrv_do_pend)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 11 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6
    var r_buf0_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 7 * UINT32_BYTES), 0xFFFFF000); 
    var r_buf1_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 8 * UINT32_BYTES), 0xFFFFF000);
    var r_buf2_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 9 * UINT32_BYTES), 0xFFFFF000);
    var r_buf3_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 10 * UINT32_BYTES), 0xFFFFF000);
    var r_buf4_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 11 * UINT32_BYTES), 0xFFFFF000);

    (is_valid_addr(r_buf0_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf0_p, r_buf0_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf1_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf1_p, r_buf1_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf2_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf2_p, r_buf2_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf3_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf3_p, r_buf3_p + PAGE_4K_SZ)) &&
    (is_valid_addr(r_buf4_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf4_p, r_buf4_p + PAGE_4K_SZ))
}