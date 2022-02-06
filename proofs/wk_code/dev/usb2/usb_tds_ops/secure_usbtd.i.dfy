include "../../../utils/model/utils_objaddrs.s.dfy"
include "../../../utils/model/utils_subjs_objs.i.dfy"
include "../../../drv/public/wimpdrv_lemmas.i.dfy"

// Lemma: For a secure qTD32, the data buffer fields reference the target WimpDrv's DO only
lemma Lemma_SecureUSBTD_QTD32_DataBuf_RefsOnlyWimpDrvDOAmongAllActiveObjs(s:state, usbtd_slot_id:uint32)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QTD32
        // Requirement: Given USB TD is a secure USB TD, and is a QTD32

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            wimpdrv_valid_slot_id(drv_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            WSM_IsWimpDrvID(s.subjects, wimpdrv_id) 

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var dest_objs := WSM_SecureUSBTD_QTD32_GetAllActiveObjsOverlappedWithDataBufs(s, usbtd_slot_id);
            dest_objs == {wimpdrv_do_id.oid}
{
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, usbtd_slot_id);

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
    var wimpdrv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals, drv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    // Prove wimpdrv_do_id is active
    Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid, wimpdrv_do_id.oid);
    Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(s.subjects, s.objects, s.id_mappings, wimpdrv_idword, wimpdrv_id);
    assert SubjPID_WimpDrv_ByIDWord(globals, wimpdrv_idword) != WS_PartitionID(PID_INVALID);
    assert SubjPID_WimpDrv_ByDrvID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id) != WS_PartitionID(PID_INVALID);
    assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid) != WS_PartitionID(PID_INVALID);
    assert WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid);

    // Prove <dest_objs> contains the target wimp driver's DO only
    var dest_objs := WSM_SecureUSBTD_QTD32_GetAllActiveObjsOverlappedWithDataBufs(s, usbtd_slot_id);
    Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(s, drv_slot, wimpdrv_do_pbase, wimpdrv_do_pend);

    assume wimpdrv_do_id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForDOs(s.objects, s.objs_addrs, globals, wimpdrv_do_pbase, wimpdrv_do_pend);
    assert wimpdrv_do_id.oid in dest_objs;

    // Prove dest_objs == {wimpdrv_do_id.oid}
    if(dest_objs != {wimpdrv_do_id.oid})
    {
        var o_id :| o_id in dest_objs && o_id != wimpdrv_do_id.oid;
        assume false;
    }
    assert dest_objs == {wimpdrv_do_id.oid};
}

// Lemma: For a secure QH32, the data buffer fields reference the target WimpDrv's DO only
lemma Lemma_SecureUSBTD_QH32_DataBuf_RefsOnlyWimpDrvDOAmongAllActiveObjs(s:state, usbtd_slot_id:uint32)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QH32
        // Requirement: Given USB TD is a secure USB TD, and is a QH32

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            wimpdrv_valid_slot_id(drv_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            WSM_IsWimpDrvID(s.subjects, wimpdrv_id) 

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            var dest_objs := WSM_SecureUSBTD_QH32_GetAllActiveObjsOverlappedWithDataBufs(s, usbtd_slot_id);
            dest_objs == {wimpdrv_do_id.oid}
{
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, usbtd_slot_id);

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
    var wimpdrv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals, drv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    // Prove wimpdrv_do_id is active
    Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid, wimpdrv_do_id.oid);
    Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(s.subjects, s.objects, s.id_mappings, wimpdrv_idword, wimpdrv_id);
    assert SubjPID_WimpDrv_ByIDWord(globals, wimpdrv_idword) != WS_PartitionID(PID_INVALID);
    assert SubjPID_WimpDrv_ByDrvID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id) != WS_PartitionID(PID_INVALID);
    assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid) != WS_PartitionID(PID_INVALID);
    assert WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid);

    // Prove <dest_objs> contains the target wimp driver's DO only
    var dest_objs := WSM_SecureUSBTD_QH32_GetAllActiveObjsOverlappedWithDataBufs(s, usbtd_slot_id);
    Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(s, drv_slot, wimpdrv_do_pbase, wimpdrv_do_pend);

    assume wimpdrv_do_id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForDOs(s.objects, s.objs_addrs, globals, wimpdrv_do_pbase, wimpdrv_do_pend);
    assert wimpdrv_do_id.oid in dest_objs;

    // Prove dest_objs == {wimpdrv_do_id.oid}
    if(dest_objs != {wimpdrv_do_id.oid})
    {
        var o_id :| o_id in dest_objs && o_id != wimpdrv_do_id.oid;
        assume false;
    }
    assert dest_objs == {wimpdrv_do_id.oid};
}




/*********************** Private Functions ********************/
// Function: Given a secure USB TD (with type QTD32), returns all active object overlaps with the wimp driver's DO 
// associated with the USB TD <usbtd_slot_id>
// [NOTE] This function do not return inactive objects, because they cannot be accessed by definition
function WSM_SecureUSBTD_QTD32_GetAllActiveObjsOverlappedWithDataBufs(s:state, usbtd_slot_id:uint32) : (result:set<Object_ID>)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QTD32
        // Requirement: Given USB TD is a secure USB TD, and is a QTD32

    ensures WK_ValidObjs_ObjIDs(s.objects)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            wimpdrv_valid_slot_id(drv_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
            var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
            WK_ValidPMemRegion(wimpdrv_do_pbase, wimpdrv_do_pend)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
            var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
            forall id :: id in result 
                <==> (id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion(s.objects, s.objs_addrs, globals, wimpdrv_do_pbase, wimpdrv_do_pend) &&
                      WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id))
        // Property: Returns all active object overlaps with the wimp driver's DO associated with the USB TD <usbtd_slot_id>
{
    reveal WK_ValidObjs();
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, usbtd_slot_id);

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals, drv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(usbtd_slot_id);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot_id, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 7 * UINT32_BYTES);
    var r_buf0_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 3 * UINT32_BYTES), 0xFFFFF000); // According to EHCI specification, Section 3.5
    var r_buf1_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0xFFFFF000);
    var r_buf2_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0xFFFFF000);
    var r_buf3_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 6 * UINT32_BYTES), 0xFFFFF000);
    var r_buf4_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 7 * UINT32_BYTES), 0xFFFFF000);

    // Prove the memory region as the transfers destinations must be inside the target wimp driver's DO.  
    assert (is_valid_addr(r_buf0_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf0_p, r_buf0_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf1_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf1_p, r_buf1_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf2_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf2_p, r_buf2_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf3_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf3_p, r_buf3_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf4_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf4_p, r_buf4_p + PAGE_4K_SZ));

    // Get all active objects targeted by the data buffer transfers
    // [NOTE] Here we use [wimpdrv_do_pbase, wimpdrv_do_pend) instead of <r_buf0_*>, so we should get a bigger set of 
    // <active_objs_overlapped_with_pmem>. This is fine as we will prove later that <active_objs_overlapped_with_pmem>
    // contains only the target wimp driver's DO. 
    var active_objs_overlapped_with_pmem:set<Object_ID> := (
        set id:Object_ID | id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion(s.objects, s.objs_addrs, globals, wimpdrv_do_pbase, wimpdrv_do_pend) &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id)
    );

    active_objs_overlapped_with_pmem
}

// Function: Given a secure USB TD (with type QH32), returns all active object overlaps with the wimp driver's DO 
// associated with the USB TD <usbtd_slot_id>
// [NOTE] This function do not return inactive objects, because they cannot be accessed by definition
function WSM_SecureUSBTD_QH32_GetAllActiveObjsOverlappedWithDataBufs(s:state, usbtd_slot_id:uint32) : (result:set<Object_ID>)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QH32
        // Requirement: Given USB TD is a secure USB TD, and is a QH32

    ensures WK_ValidObjs_ObjIDs(s.objects)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            wimpdrv_valid_slot_id(drv_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
            var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
            WK_ValidPMemRegion(wimpdrv_do_pbase, wimpdrv_do_pend)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
            var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
            forall id :: id in result 
                <==> (id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion(s.objects, s.objs_addrs, globals, wimpdrv_do_pbase, wimpdrv_do_pend) &&
                      WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id))
        // Property: Returns all active object overlaps with the wimp driver's DO associated with the USB TD <usbtd_slot_id>
{
    reveal WK_ValidObjs();
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, usbtd_slot_id);

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
    var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals, drv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);

    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(usbtd_slot_id);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot_id, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 11 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6
    var r_buf0_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 7 * UINT32_BYTES), 0xFFFFF000); 
    var r_buf1_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 8 * UINT32_BYTES), 0xFFFFF000);
    var r_buf2_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 9 * UINT32_BYTES), 0xFFFFF000);
    var r_buf3_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 10 * UINT32_BYTES), 0xFFFFF000);
    var r_buf4_p:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 11 * UINT32_BYTES), 0xFFFFF000);

    // Prove the memory region as the transfers destinations must be inside the target wimp driver's DO.  
    assert (is_valid_addr(r_buf0_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf0_p, r_buf0_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf1_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf1_p, r_buf1_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf2_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf2_p, r_buf2_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf3_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf3_p, r_buf3_p + PAGE_4K_SZ)) &&
        (is_valid_addr(r_buf4_p + PAGE_4K_SZ) && is_mem_region_inside(wimpdrv_do_pbase, wimpdrv_do_pend, r_buf4_p, r_buf4_p + PAGE_4K_SZ));

    // Get all active objects targeted by the data buffer transfers
    // [NOTE] Here we use [wimpdrv_do_pbase, wimpdrv_do_pend) instead of <r_buf0_*>, so we should get a bigger set of 
    // <active_objs_overlapped_with_pmem>. This is fine as we will prove later that <active_objs_overlapped_with_pmem>
    // contains only the target wimp driver's DO. 
    var active_objs_overlapped_with_pmem:set<Object_ID> := (
        set id:Object_ID | id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion(s.objects, s.objs_addrs, globals, wimpdrv_do_pbase, wimpdrv_do_pend) &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id)
    );

    active_objs_overlapped_with_pmem
}