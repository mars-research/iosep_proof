include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"
include "../../drv/drv.s.dfy"
include "../../partition_id.s.dfy"
include "usb_pdev.s.dfy"

include "usb_tds_nlarith.i.dfy"

/*********************** Axioms ********************/
// [HW] Axiom (related): Exist a function to check if the given USB TD cannot modify any USBPDevs' USB addresses
predicate {:axiom} Is_USBTD_NotModifyUSBPDevsAddrs(globals:globalsmap, td_slot:word)
    requires usbtd_map_valid_slot_id(td_slot)




/*********************** State Invariants and Related Predicates ********************/
predicate WK_USBTD_Map_ValidGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 0. In each slot of <g_usbtd_map_mem>, the ID field's value must be <= the global variable <g_usbtd_counter>
    (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_id(globals, i)) && 

    // 1. In each slot of <g_usbtd_map_mem>, the PID field's value must be either invalid or a wimp partition's PID
    (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_pid(globals, i)) && 

    // 2. In each slot of <g_usbtd_map_mem>, the type field's value must be one of the allowed types
    (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_type(globals, i)) && 

    // 3. In each slot of <g_usbtd_map_mem>, the bus_id field's value must be one of the allowed types
    (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_busid(globals, i)) && 

    // 4. In each slot of <g_usbtd_map_mem>, the wimpdrv_slot field's value must be one of the allowed types
    (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_wimpdrv_slotid(globals, i)) && 

    // 5. In each slot of <g_usbtd_map_mem>, the usbpdev_slot field's value must be one of the allowed types
    (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_usbpdev_slotid(globals, i)) &&

    // 6. Validity properties related to <id_words> of USB TDs
    WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals) &&
        
    (true)
}

// Predicate: In the given <slot> of <g_usbtd_map_mem>, the ID field's value must be <= the value of usbtd id counter
predicate usbtd_slot_valid_id(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    usbtd_map_get_idword(globals, slot) <= usbtd_id_counter_read(globals) || 
    usbtd_map_get_idword(globals, slot) == USBTD_ID_INVALID
}

// Predicate: In the given <slot> of <g_usbtd_map_mem>, the PID field's value must be either invalid or a wimp 
// partition's PID
predicate usbtd_slot_valid_pid(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    (usbtd_map_get_pid(globals, slot) == WS_PartitionID(PID_INVALID) || 
        usbtd_map_get_pid(globals, slot) in pids_parse_g_wimp_pids(globals))
}

// Predicate: In the given <slot> of <g_usbtd_map_mem>, the type field's value must be one of the allowed types
predicate usbtd_slot_valid_type(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    var v := usbtd_map_get_type(globals, slot);

    (v == USBTDs_TYPE_QTD32) || (v == USBTDs_TYPE_QH32) || 
    (v == USBTDs_TYPE_iTD32) || (v == USBTDs_TYPE_siTD32)
}

// Predicate: In the given <slot> of <g_usbtd_map_mem>, the bus_id field's value must be valid
predicate usbtd_slot_valid_busid(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    var id := usbtd_map_get_busid_word(globals, slot);

    isUInt16(id)
}

// Predicate: In the given <slot> of <g_usbtd_map_mem>, the <wimpdrv_slot_id> field's value must be valid
predicate usbtd_slot_valid_wimpdrv_slotid(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    var s := usbtd_map_get_wimpdrv_slotid(globals, slot);

    s == WimpDrv_SlotID_EMPTY || wimpdrv_valid_slot_id(s)
}

// Predicate: In the given <slot> of <g_usbtd_map_mem>, the <usbpdev_slot_id> field's value must be valid
predicate usbtd_slot_valid_usbpdev_slotid(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    var s := usbtd_map_get_usbpdev_slotid(globals, slot);

    s == WimpUSBPDev_SlotID_EMPTY || usbpdev_valid_slot_id(s)
}

predicate WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // Each slot must map to a unique USBTD_ID_word, unless it is USBTD_ID_INVALID
    (forall i, j :: usbtd_map_valid_slot_id(i) && usbtd_map_valid_slot_id(j) &&
            usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID && usbtd_map_get_idword(globals, j) != USBTD_ID_INVALID
        ==> (usbtd_map_get_idword(globals, i) == usbtd_map_get_idword(globals, j) <==> i == j)
    ) &&

    // If a USB TD is active, then its id_word cannot be USBTD_ID_INVALID 
    (forall slot :: usbtd_map_valid_slot_id(slot) &&
            usbtd_map_get_pid(globals, slot) != WS_PartitionID(PID_INVALID)
        ==> usbtd_map_get_idword(globals, slot) != USBTD_ID_INVALID
    ) &&

    (true)
}




/*********************** For G_USBTD_ID_Counter() ********************/
// Return the value of g_usbtd_counter
function usbtd_id_counter_read(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();
    var v := global_read_word(globals, G_USBTD_ID_Counter(), AddressOfGlobal(G_USBTD_ID_Counter()));

    v
}




/*********************** Util Predicates And Functions ********************/
// Predicate The USB TD refered by <slot> must be in <g_usbtd_map_mem>
predicate usbtd_map_valid_slot_id(slot:uint32)
{
    0 <= slot < USB_TD_ENTRY_NUM
}

// Predicate: No verified/secure USB TD is associated with the given <usbpdev_slot>
predicate usbtds_verifiedtds_do_not_associate_usb_pdev(globals:globalsmap, usbpdev_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbpdev_valid_slot_id(usbpdev_slot)
{
    forall usbtd_slot :: usbtd_map_valid_slot_id(usbtd_slot) &&
            TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
            ==> usbtd_map_get_usbpdev_slotid(globals, usbtd_slot) != usbpdev_slot
}

// Predicate: No verified/secure USB TD is associated with the given <wimpdrv_slot>
predicate {:opaque} usbtds_verifiedtds_do_not_associate_wimpdrv(globals:globalsmap, wimpdrv_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
{
    forall usbtd_slot :: usbtd_map_valid_slot_id(usbtd_slot) &&
            TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
            ==> usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot) != wimpdrv_slot
}

function usbtd_map_get_tdaddr(globals:globalsmap, slot:uint32) : addr
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var v := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ;
    Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);

    v
}

// Return the <pid> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_pid(globals:globalsmap, slot:uint32) : WS_PartitionID 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
    var pid := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    WS_PartitionID(pid)
}

// Return the <id> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_idword(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
    var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    v
}

// Return the <type> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_type(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
    var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    v
}

// Return the <eechi_id> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_busid(globals:globalsmap, slot:uint32) : uint16 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
    requires usbtd_slot_valid_busid(globals, slot)
{
    usbtd_map_get_busid_word(globals, slot)
}

function usbtd_map_get_busid_word(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
    var id := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    id
}

// Return the <wimpdrv_slot_id> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_wimpdrv_slotid(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
    var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    v
}

// Return the <usbpdev_slot_id> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_usbpdev_slotid(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
    var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    v
}

// Return the <flag> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_flags(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
    var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    v
}

// Return the <handle> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_handle(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset);
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
    var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);

    v
}

// Return the <input_params> field of the given USB TD info slot in <g_usbtd_map_mem>
function usbtd_map_get_inputparam(globals:globalsmap, slot:uint32, param_sel:word) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)

    requires param_sel == G_USBTDs_MAP_ENTRY_InputParam1 || param_sel == G_USBTDs_MAP_ENTRY_InputParam2 || param_sel == G_USBTDs_MAP_ENTRY_InputParam3
{
    reveal WK_ValidGlobalVars_Decls();

    if(param_sel == G_USBTDs_MAP_ENTRY_InputParam1) then
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);
        var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
        var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);
        v
    else if(param_sel == G_USBTDs_MAP_ENTRY_InputParam2) then
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);
        var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
        var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);
        v
    else
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);
        var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
        var v := global_read_word(globals, G_USBTD_MAP_MEM(), vaddr1);
        v
}

// Predicate: The given <id_word> only appears at <slot> in <g_usbtd_map_mem>
predicate p_usbtd_slot_idword_unique(globals:globalsmap, slot:word, id_word:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(slot)
    requires id_word != USBTD_ID_INVALID
{
    forall i :: usbtd_map_valid_slot_id(i) && i != slot &&
                usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals, i) != id_word
}




/*********************** USBTD clear content ********************/
predicate usbtd_has_clear_content(new_globals:globalsmap, td_slot:uint32, td_type:uint32)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(td_slot)
    requires (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32) || 
            (td_type == USBTDs_TYPE_iTD32) || (td_type == USBTDs_TYPE_siTD32)
{
    if(td_type == USBTDs_TYPE_QTD32) then
        ffi_usbtd_clear_content_stack_and_globals_qtd32(new_globals, td_slot)
    else if (td_type == USBTDs_TYPE_QH32) then
        ffi_usbtd_clear_content_stack_and_globals_qh32(new_globals, td_slot)
    else if (td_type == USBTDs_TYPE_iTD32) then
        // [TODO] Not support iTD and siTD yet
        true
    else 
        assert td_type == USBTDs_TYPE_siTD32;
        // [TODO] Not support iTD and siTD yet
        true
}

predicate {:opaque} ffi_usbtd_clear_content_stack_and_globals_qtd32(new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot);
{
    lemma_DistinctGlobals();
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(td_slot);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == SetBit(0, 0) &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) == SetBit(0, 0) &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) == SetBit(0, 7) &&     // Status is inactive
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES) == 0
}

predicate {:opaque} ffi_usbtd_clear_content_stack_and_globals_qh32(new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot);
{
    lemma_DistinctGlobals();
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    var temp_td_addr := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(td_slot);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) == SetBit(0, 0) &&    // QH link pointer has T flag
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) == 0 &&     
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) == SetBit(0, 0) && // Next qTD pointer has T flag

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) == SetBit(0, 0) && // Alt next qTD pointer has T flag
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) == SetBit(0, 7) && // Status is inactive
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) == 0 &&

    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) == 0 &&
    global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES) == 0
}




/*********************** Util Predicates And Functions for Temp TD (g_temp_usbtd) ********************/
// Predicate: In the temp USB TD, the ID field's value must be <= usbtd_id_counter_read(globals)
predicate usbtd_temp_valid_id(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    (
        usbtd_temp_get_id(globals) <= usbtd_id_counter_read(globals) ||
        usbtd_temp_get_id(globals) == USBTD_ID_INVALID
    ) &&

    (
        usbtd_temp_get_pid(globals) != WS_PartitionID(PID_INVALID)
            ==> usbtd_temp_get_id(globals) != USBTD_ID_INVALID
    )
}

// Predicate: In the temp USB TD, the PID field's value must be either invalid or a wimp 
// partition's PID
predicate usbtd_temp_valid_pid(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    (usbtd_temp_get_pid(globals) == WS_PartitionID(PID_INVALID) || 
        usbtd_temp_get_pid(globals) in pids_parse_g_wimp_pids(globals))
}

// Predicate: In the temp USB TD, the type field's value must be one of the allowed types
predicate usbtd_temp_valid_type(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var v := usbtd_temp_get_type(globals);

    (v == USBTDs_TYPE_QTD32) || (v == USBTDs_TYPE_QH32) || 
    (v == USBTDs_TYPE_iTD32) || (v == USBTDs_TYPE_siTD32)
}

// Predicate: In the temp USB TD, the bus_id field's value must valid
predicate usbtd_temp_valid_busid(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var id := usbtd_temp_get_busid_word(globals);

    isUInt16(id)
}

// Predicate: In the temp USB TD, the <wimpdrv_slot_id> field's value must be valid
predicate usbtd_temp_valid_wimpdrv_slotid(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var s := usbtd_temp_get_wimpdrv_slotid(globals);

    s == WimpDrv_SlotID_EMPTY || wimpdrv_valid_slot_id(s)
}

// Predicate: In the temp USB TD, the <usbpdev_slot_id> field's value must be empty or valid
predicate usbtd_temp_valid_usbpdev_slotid(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    var s := usbtd_temp_get_usbpdev_slotid(globals);

    s == WimpUSBPDev_SlotID_EMPTY || usbpdev_valid_slot_id(s)
}

// For temp USB TD: Return the <type> field
function usbtd_temp_get_id(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_ID_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_ID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
    var v := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    v
}

// For temp USB TD: Return the <pid> field
function usbtd_temp_get_pid(globals:globalsmap) : WS_PartitionID 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_PID_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_PID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
    var pid := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    WS_PartitionID(pid)
}

// For temp USB TD: Return the <type> field
function usbtd_temp_get_type(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
    var v := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    v
}

// For temp USB TD: Return the <bus_id> word
function usbtd_temp_get_busid_word(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
    var id := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    id
}

// For temp USB TD: Return the <flags> word
function usbtd_temp_get_flags(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
    var id := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    id
}

// Return the <wimpdrv_slot_id> field of the given USB TD info slot in <g_temp_usbtd>
function usbtd_temp_get_wimpdrv_slotid(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
    var id := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    id
}

// Return the <usbpdev_slot_id> field of the given USB TD info slot in <g_temp_usbtd>
function usbtd_temp_get_usbpdev_slotid(globals:globalsmap) : word 
    requires WK_ValidGlobalVars_Decls(globals)
{
    reveal WK_ValidGlobalVars_Decls();

    Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
    assert ValidGlobalOffset(G_Temp_USBTD(), G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
    var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
    var id := global_read_word(globals, G_Temp_USBTD(), vaddr1);

    id
}

// Return the <input_params> field of the given USB TD info slot in <g_temp_usbtd>
function usbtd_temp_get_inputparam(globals:globalsmap, param_sel:word) : word 
    requires WK_ValidGlobalVars_Decls(globals)

    requires param_sel == G_USBTDs_MAP_ENTRY_InputParam1 || param_sel == G_USBTDs_MAP_ENTRY_InputParam2 || param_sel == G_USBTDs_MAP_ENTRY_InputParam3
{
    reveal WK_ValidGlobalVars_Decls();

    if(param_sel == G_USBTDs_MAP_ENTRY_InputParam1) then
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);
        var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
        var v := global_read_word(globals, G_Temp_USBTD(), vaddr1);
        v
    else if(param_sel == G_USBTDs_MAP_ENTRY_InputParam2) then
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);
        var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
        var v := global_read_word(globals, G_Temp_USBTD(), vaddr1);
        v
    else
        Lemma_temp_usbtd_slot_offset_AlwaysValidGTRempUSBTDMemAddr(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);
        var vaddr1 := AddressOfGlobal(G_Temp_USBTD()) + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
        var v := global_read_word(globals, G_Temp_USBTD(), vaddr1);
        v
}




/*********************** Private Lemmas ********************/
lemma Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot:uint32)
    requires usbtd_map_valid_slot_id(slot)
    ensures var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr) && 
            (forall i :: 0 <= i < MAX_USB_TD_BYTES/UINT32_BYTES ==> isUInt32(td_addr + i * UINT32_BYTES))
{
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(slot);
    lemma_DistinctGlobals();

    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    forall i | 0 <= i < MAX_USB_TD_BYTES/UINT32_BYTES
        ensures isUInt32(td_addr + i * UINT32_BYTES)
    {
        Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot, i * UINT32_BYTES);
        assert slot * G_USBTDs_MAP_ENTRY_SZ + i * UINT32_BYTES < G_USBTDs_MAP_MEM_SZ_Tight;
    }
}