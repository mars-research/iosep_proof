include "../../../state_properties_OpsSaneStateSubset.s.dfy"
include "../../../utils/model/utils_objaddrs.s.dfy"
include "../../../drv/drv.i.dfy"
include "../usb_tds_ops/secure_usbtd.i.dfy"
include "../public/usb_lemmas.i.dfy"

/*********************** Axioms ********************/
// [HW] Axiom (wel known): Exist a function to calculate transfers to a USBPDev's FDs and DOs defined in secure USB TD
// [NOTE] USB TDs can define transfers to USBPDev's objects according to their semantics
function {:axiom} WSM_SecureUSBTD_CalcTransfersToUSBPDev(s:state, usbtd_slot_id:word, usbpdev_id:Dev_ID) : (result:(map<FD_ID, FD_Trans_Param>, map<DO_ID, DO_Trans_Param>))
    requires InstSaneState(s)
    requires WSM_IsUSBPDevID(s.subjects, usbpdev_id)
    ensures MapGetKeys(result.0) == s.subjects.usbpdevs[usbpdev_id].fd_ids
    ensures MapGetKeys(result.1) == s.subjects.usbpdevs[usbpdev_id].do_ids

// [State/Ops Mapping] Axiom (well knwon): The returned value corresponds to the FD's content in the USBTD
// [NOTE] This axiom holds because USB TDs can straight-forward map to abstract objects
function {:axiom} WSM_USBTD_GetAbstractFDVal(s:state, fd_id:FD_ID) : (result:FD_Val)
    requires fd_id in s.objects.usbtd_fds

// [State/Ops Mapping] Axiom (well known): If only temp global variables, counters, registers, and stack are changed,  
// this function returns the same result
// [NOTE] Different counter values do not impact the mappings. This is because counters are not mapped to state variables
// in WK design. Counters are used in SIs instead.
lemma {:axiom} Lemma_WSM_USBTD_GetAbstractFDVal_Property(s1:state, s2:state, fd_id:FD_ID)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)
    requires fd_id in s1.objects.usbtd_fds
    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)
    ensures WSM_USBTD_GetAbstractFDVal(s1, fd_id) == WSM_USBTD_GetAbstractFDVal(s2, fd_id)

// [State/Ops Mapping] Axiom (well knwon): The returned value corresponds to the DO's content in the USBTD
// [NOTE] This axiom holds because USB TDs can straight-forward map to abstract objects
function {:axiom} WSM_USBTD_GetAbstractDOVal(s:state, do_id:DO_ID) : (result:DO_Val)
    requires do_id in s.objects.usbtd_dos

// [State/Ops Mapping] Axiom (well known): If only temp global variables, counters, registers, and stack are changed,  
// this function returns the same result
// [NOTE] Different counter values do not impact the mappings. This is because counters are not mapped to state variables
// in WK design. Counters are used in SIs instead.
lemma {:axiom} Lemma_WSM_USBTD_GetAbstractDOVal_Property(s1:state, s2:state, do_id:DO_ID)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)
    requires do_id in s1.objects.usbtd_dos
    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)
    ensures WSM_USBTD_GetAbstractDOVal(s1, do_id) == WSM_USBTD_GetAbstractDOVal(s2, do_id)




/*********************** Transfer Parameters Calculation - General ********************/
// Function: Given an ID of USB TD, return its value
function WSM_USBTD_CalcTDVal(s:state, usbtd_id:TD_ID) : (result:TD_Val)
    requires OpsSaneStateSubset(s)

    requires usbtd_id in s.objects.usbtd_tds

    ensures var globals := wkm_get_globals(s.wk_mstate);
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) != WS_PartitionID(PID_INVALID)
                ==> ((forall id :: id in result.trans_params_tds ==> WSM_IsTDID(s.objects, id)) && 
                    (forall id :: id in result.trans_params_fds ==> WSM_IsFDID(s.objects, id)) &&
                    (forall id :: id in result.trans_params_dos ==> WSM_IsDOID(s.objects, id)))
        // Property: If the TD is active, then the referenced objects must be exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) != WS_PartitionID(PID_INVALID)
                ==> (forall id :: id in result.trans_params_tds
                        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid))
    ensures var globals := wkm_get_globals(s.wk_mstate);
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) != WS_PartitionID(PID_INVALID)
                ==> (forall id :: id in result.trans_params_fds
                        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid))
    ensures var globals := wkm_get_globals(s.wk_mstate);
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) != WS_PartitionID(PID_INVALID)
                ==> (forall id :: id in result.trans_params_dos
                        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid))
        // Property: If the TD is active, then the referenced objects must be in the same partition with the given USB 
        // TD <usbtd_id>
    ensures var globals := wkm_get_globals(s.wk_mstate);
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) != WS_PartitionID(PID_INVALID)
                ==> (forall id :: id in result.trans_params_tds ==> result.trans_params_tds[id].amodes == {R})
        // Property: If the TD is active, then the USBTD pointers fields only define read transfers to TDs
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();

    var globals := wkm_get_globals(s.wk_mstate);

    // Get usbtd_idword
    var usbtd_idword:word := USBTD_ID_ToIDWord(s.subjects, s.objects, s.id_mappings, usbtd_id);

    if(usbtd_idword_in_record(globals, usbtd_idword)) then
        var usbtd_slot_id := usbtd_get_slot_by_idword(globals, usbtd_idword);
        var flags := usbtd_map_get_flags(globals, usbtd_slot_id);
        var td_type := usbtd_map_get_type(globals, usbtd_slot_id);

        // Prove WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id);
        reveal WK_ValidObjs_ObjIDs();
        Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_id);
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id);
        var usbtd_pid := usbtd_map_get_pid(globals, usbtd_slot_id);
        
        if(usbtd_pid != WS_PartitionID(PID_INVALID)) then
            // If USB TD is active, then parse
            assert usbtd_slot_valid_type(globals, usbtd_slot_id);
            if(flags == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)) then
                // [NOTE] In order to correctly map the USB TD, a secure USB TDs must not be able to modify any USBPDevs' USB addresses
                reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();
                Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
                assert td_type == USBTDs_TYPE_QTD32 || td_type == USBTDs_TYPE_QH32;
                if(td_type == USBTDs_TYPE_QTD32) then
                    WSM_SecureUSBTD_QTD32_CalcTDVal(s, usbtd_slot_id)
                else
                    assert td_type == USBTDs_TYPE_QH32;
                    WSM_SecureUSBTD_QH32_CalcTDVal(s, usbtd_slot_id)
            else
                reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();
                assert usbtd_has_clear_content(globals, usbtd_slot_id, td_type);
                WSM_EmptyUSBTD_CalcTDVal(globals, usbtd_slot_id)
        else
            // The USB TD is inactive, return dummy value
            TD_Val(map[], map[], map[])
    else
        reveal WK_ValidObjs_ObjIDs();
        Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_id);
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_id.oid) == WS_PartitionID(PID_INVALID);
        // The USB TD is inactive, return dummy value
        TD_Val(map[], map[], map[])
}


function WSM_EmptyUSBTD_CalcTDVal(globals:globalsmap, usbtd_slot_id:uint32) : (result:TD_Val)
    requires WK_ValidGlobalVars_Decls(globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
    requires var td_type := usbtd_map_get_type(globals, usbtd_slot_id);
             (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32) || 
             (td_type == USBTDs_TYPE_iTD32) || (td_type == USBTDs_TYPE_siTD32)
    requires var td_type := usbtd_map_get_type(globals, usbtd_slot_id);
             usbtd_has_clear_content(globals, usbtd_slot_id, td_type)

    ensures result == TD_Val(map[], map[], map[])
{
    TD_Val(map[], map[], map[])
}




/*********************** Transfer Parameters Calculation - Secure QH32 ********************/
// Function: Map the content of a secure QH32 to an abstract TD
function WSM_SecureUSBTD_QH32_CalcTDVal(s:state, usbtd_slot_id:uint32) : (result:TD_Val)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QH32
        // Requirement: Given USB TD is a secure USB TD, and is a QH32

    ensures forall id :: id in result.trans_params_tds
                ==> WSM_IsTDID(s.objects, id)
    ensures forall id :: id in result.trans_params_fds
                ==> WSM_IsFDID(s.objects, id)
    ensures forall id :: id in result.trans_params_dos
                ==> WSM_IsDOID(s.objects, id)
        // Property: The referenced objects must be exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.trans_params_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.trans_params_fds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.trans_params_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The referenced objects must be in the same partition with the given USB TD <usbtd_slot_id>
    ensures forall id :: id in result.trans_params_tds
                ==> result.trans_params_tds[id].amodes == {R}
        // Property: The USBTD pointers fields only define read transfers to TDs
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    // Prove <usbtd_slot_id> is active
    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, usbtd_slot_id);
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();

    var temp1 := WSM_SecureUSBTD_CalcTDVal_ForSelfFDAndDO(s, usbtd_slot_id);
    var trans_params_fds1 := temp1.0;
    var trans_params_dos1 := temp1.1;
    var trans_params_tds2 := WSM_SecureUSBTD_QH32_CalcTDVal_ForUSBTDPtrs(s, usbtd_slot_id);
    var trans_params_dos3 := WSM_SecureUSBTD_QH32_CalcTDVal_ForDataBufs(s, usbtd_slot_id);
    var temp2 := WSM_SecureUSBTD_QH32_CalcTDVal_ForUSBPDev(s, usbtd_slot_id);
    var trans_params_fds4 := temp2.0;
    var trans_params_dos4 := temp2.1;

    var result_trans_params_tds := trans_params_tds2;
    var result_trans_params_fds := MapConcat(trans_params_fds1, trans_params_fds4);
    var result_trans_params_dos := MapConcat(MapConcat(trans_params_dos1, trans_params_dos3), trans_params_dos4);

    TD_Val(result_trans_params_tds, result_trans_params_fds, result_trans_params_dos)
}

function WSM_SecureUSBTD_QH32_CalcTDVal_ForUSBTDPtrs(s:state, usbtd_slot_id:uint32) : (trans_params_tds:map<TD_ID, TD_Trans_Param>)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QH32
        // Requirement: Given USB TD is a secure USB TD, and is a QH32

    ensures forall id :: id in trans_params_tds
                ==> id in s.objects.usbtd_tds
    ensures forall id :: id in trans_params_tds
                ==> trans_params_tds[id].amodes == {R}
        // Property: The USBTD pointers fields only define read transfers to USB TDs
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in trans_params_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The given USB TD <usbtd_slot_id> refs objects in the same partition only
{
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, usbtd_slot_id);

    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(usbtd_slot_id);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot_id, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qh_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qh_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

    // Prove referenced USB TDs are active, if the termination flag is not set
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();

    var trans_params_next_qh:map<TD_ID, TD_Trans_Param> := WSM_SecureUSBTD_CalcUSBTDPtrPair(s, next_qh_p_Tflag, next_qh_slot);
    var trans_params_next_qtd:map<TD_ID, TD_Trans_Param> := WSM_SecureUSBTD_CalcUSBTDPtrPair(s, next_qtd_p_Tflag, next_qtd_slot);
    var trans_params_alt_next_qtd:map<TD_ID, TD_Trans_Param> := WSM_SecureUSBTD_CalcUSBTDPtrPair(s, alt_next_qtd_p_Tflag, alt_next_qtd_slot);

    var result := MapConcat_AllowSameKVPair(trans_params_next_qh, MapConcat_AllowSameKVPair(trans_params_next_qtd, trans_params_alt_next_qtd));

    // Prove the refered DO ID must be in the same partition with the given USB TD
    assert next_qh_p_Tflag != 1 ==> usbtd_map_get_pid(globals, usbtd_slot_id) == usbtd_map_get_pid(globals, next_qh_slot);
    assert next_qtd_p_Tflag != 1 ==> usbtd_map_get_pid(globals, usbtd_slot_id) == usbtd_map_get_pid(globals, next_qtd_slot);
    assert alt_next_qtd_p_Tflag != 1 ==> usbtd_map_get_pid(globals, usbtd_slot_id) == usbtd_map_get_pid(globals, alt_next_qtd_slot);

    result
}

function WSM_SecureUSBTD_QH32_CalcTDVal_ForUSBPDev(s:state, usbtd_slot_id:uint32) : (result:(map<FD_ID, FD_Trans_Param>, map<DO_ID, DO_Trans_Param>))
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QH32
        // Requirement: Given USB TD is a secure USB TD, and is a QH32

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot_id);
            usbpdev_valid_slot_id(usbpdev_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot_id);
            var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, usbpdev_slot);
            usb_is_usbpdev_addr_valid(usbpdev_addr_raw)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot_id);
            var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr) &&
            usbpdev_addr != usb_parse_usbpdev_addr(empty_addr)
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot_id);
            var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
            WSM_IsUSBPDevID(s.subjects, usbpdev_id) &&
            MapGetKeys(result.0) == s.subjects.usbpdevs[usbpdev_id].fd_ids &&
            MapGetKeys(result.1) == s.subjects.usbpdevs[usbpdev_id].do_ids
        // Property: Parsed the ID of the referenced USBPDev's internal FDs and DOs correctly 
    ensures forall id :: id in result.0
                ==> id in s.objects.usbpdev_fds
    ensures forall id :: id in result.1
                ==> id in s.objects.usbpdev_dos
        // Property: The referenced USBPDev's internal FDs and DOs must exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.0
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.1
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The PID of the returned FD and DO equals to the PID stored in <usbtd_slot_id>
{
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);

    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, usbtd_slot_id);

    var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot_id);
    var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, usbpdev_slot);
    var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
    var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);
    Lemma_USBPDevs_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, globals, usbpdev_slot);
    assert WSM_IsUSBPDevID(s.subjects, usbpdev_id);

    // Prove the refered objects must be in the same partition with the given USB TD
    Lemma_USBPDev_DevID_ToAddr_ProveCorrectness(s.subjects, s.objects, s.id_mappings, usbpdev_addr, usbpdev_id);
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidGlobalVarValues_USBPDevs();
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, usbpdev_id.sid) == usbtd_map_get_pid(globals, usbtd_slot_id);
    Lemma_USBPDev_InternalFDsAndDOsHaveSamePIDWithDevice(s.subjects, s.objects, s.id_mappings, globals, usbpdev_id);

    WSM_SecureUSBTD_CalcTransfersToUSBPDev(s, usbtd_slot_id, usbpdev_id)
}

function WSM_SecureUSBTD_QH32_CalcTDVal_ForDataBufs(s:state, usbtd_slot_id:uint32) : (trans_params_dos:map<DO_ID, DO_Trans_Param>)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == 
                SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QH32
        // Requirement: Given USB TD is a secure USB TD, and is a QH32

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            wimpdrv_valid_slot_id(drv_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY &&
            WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword) in s.subjects.wimp_drvs
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            MapGetKeys(trans_params_dos) == {wimpdrv_do_id}
        // Property: The result transfer parameters contains the target wimp driver's DO only
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in trans_params_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The given USB TD <usbtd_slot_id> refs objects in the same partition only
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
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals, drv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    
    // Get all active objects targeted by the data buffer transfers
    var dest_objs := WSM_SecureUSBTD_QH32_GetAllActiveObjsOverlappedWithDataBufs(s, usbtd_slot_id);

    // Prove the memory region only belongs to the wimp driver
    Lemma_SecureUSBTD_QH32_DataBuf_RefsOnlyWimpDrvDOAmongAllActiveObjs(s, usbtd_slot_id);

    // Output the corresponding TD_Val
    var do_new_vals:set<DO_Val> := WimpDrv_DO_GetValueRangeOfDO(s.objects, wimpdrv_do_id);
    var result := map[wimpdrv_do_id := DO_Trans_Param({R,W}, do_new_vals)];
    
    // Prove the refered DO ID must be in the same partition with the given USB TD
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid, wimpdrv_do_id.oid);
    Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(s.subjects, s.objects, s.id_mappings, wimpdrv_idword, wimpdrv_id);
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid) == usbtd_map_get_pid(globals, usbtd_slot_id);
    assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id);

    result
}




/*********************** Transfer Parameters Calculation - Secure QTD32 ********************/
// Function: Map the content of a secure qTD32 to an abstract TD
function WSM_SecureUSBTD_QTD32_CalcTDVal(s:state, usbtd_slot_id:uint32) : (result:TD_Val)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QTD32
        // Requirement: Given USB TD is a secure USB TD, and is a QTD32

    ensures forall id :: id in result.trans_params_tds
                ==> WSM_IsTDID(s.objects, id)
    ensures forall id :: id in result.trans_params_fds
                ==> WSM_IsFDID(s.objects, id)
    ensures forall id :: id in result.trans_params_dos
                ==> WSM_IsDOID(s.objects, id)
        // Property: The referenced objects must be exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.trans_params_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.trans_params_fds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.trans_params_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The referenced objects must be in the same partition with the given USB TD <usbtd_slot_id>
    ensures forall id :: id in result.trans_params_tds
                ==> result.trans_params_tds[id].amodes == {R}
        // Property: The USBTD pointers fields only define read transfers to TDs
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    // Prove <usbtd_slot_id> is active
    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, usbtd_slot_id);
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();

    var temp1 := WSM_SecureUSBTD_CalcTDVal_ForSelfFDAndDO(s, usbtd_slot_id);
    var trans_params_fds1 := temp1.0;
    var trans_params_dos1 := temp1.1;
    var trans_params_tds2 := WSM_SecureUSBTD_QTD32_CalcTDVal_ForUSBTDPtrs(s, usbtd_slot_id);
    var trans_params_dos3 := WSM_SecureUSBTD_QTD32_CalcTDVal_ForDataBufs(s, usbtd_slot_id);

    var result_trans_params_tds := trans_params_tds2;
    var result_trans_params_fds := trans_params_fds1;
    var result_trans_params_dos := MapConcat(trans_params_dos1, trans_params_dos3);

    TD_Val(result_trans_params_tds, result_trans_params_fds, result_trans_params_dos)
}

function WSM_SecureUSBTD_QTD32_CalcTDVal_ForUSBTDPtrs(s:state, usbtd_slot_id:uint32) : (trans_params_tds:map<TD_ID, TD_Trans_Param>)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QTD32
        // Requirement: Given USB TD is a secure USB TD, and is a QTD32

    ensures forall id :: id in trans_params_tds
                ==> id in s.objects.usbtd_tds
    ensures forall id :: id in trans_params_tds
                ==> trans_params_tds[id].amodes == {R}
        // Property: The USBTD pointers fields only define read transfers to USB TDs
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in trans_params_tds
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The given USB TD <usbtd_slot_id> refs objects in the same partition only
{
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();

    var globals := wkm_get_globals(s.wk_mstate);
    Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, usbtd_slot_id);

    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(usbtd_slot_id);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot_id, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
    // According to EHCI specification, Section 3.5. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

    // Prove referenced USB TDs are active, if the termination flag is not set
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();

    var trans_params_next_qtd:map<TD_ID, TD_Trans_Param> := WSM_SecureUSBTD_CalcUSBTDPtrPair(s, next_qtd_p_Tflag, next_qtd_slot);
    var trans_params_alt_next_qtd:map<TD_ID, TD_Trans_Param> := WSM_SecureUSBTD_CalcUSBTDPtrPair(s, alt_next_qtd_p_Tflag, alt_next_qtd_slot);

    var result := MapConcat_AllowSameKVPair(trans_params_next_qtd, trans_params_alt_next_qtd);

    // Prove the refered DO ID must be in the same partition with the given USB TD
    assert next_qtd_p_Tflag != 1 ==> usbtd_map_get_pid(globals, usbtd_slot_id) == usbtd_map_get_pid(globals, next_qtd_slot);
    assert alt_next_qtd_p_Tflag != 1 ==> usbtd_map_get_pid(globals, usbtd_slot_id) == usbtd_map_get_pid(globals, alt_next_qtd_slot);

    result
}

function WSM_SecureUSBTD_QTD32_CalcTDVal_ForDataBufs(s:state, usbtd_slot_id:uint32) : (trans_params_dos:map<DO_ID, DO_Trans_Param>)
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == 
                SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_type(wkm_get_globals(s.wk_mstate), usbtd_slot_id) == USBTDs_TYPE_QTD32
        // Requirement: Given USB TD is a secure USB TD, and is a QTD32

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            wimpdrv_valid_slot_id(drv_slot)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY &&
            WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword) in s.subjects.wimp_drvs
        // Properties needed by the following properties
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, usbtd_slot_id);
            var wimpdrv_idword := wimpdrv_get_id_word(globals, drv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
            MapGetKeys(trans_params_dos) == {wimpdrv_do_id}
        // Property: The result transfer parameters contains the target wimp driver's DO only
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in trans_params_dos
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The given USB TD <usbtd_slot_id> refs objects in the same partition only
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
    var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(globals, drv_slot);
    var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(globals, drv_slot);
    Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals, drv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    
    // Get all active objects targeted by the data buffer transfers
    var dest_objs := WSM_SecureUSBTD_QTD32_GetAllActiveObjsOverlappedWithDataBufs(s, usbtd_slot_id);

    // Prove the memory region only belongs to the wimp driver
    Lemma_SecureUSBTD_QTD32_DataBuf_RefsOnlyWimpDrvDOAmongAllActiveObjs(s, usbtd_slot_id);

    // Output the corresponding TD_Val
    var do_new_vals:set<DO_Val> := WimpDrv_DO_GetValueRangeOfDO(s.objects, wimpdrv_do_id);
    var result := map[wimpdrv_do_id := DO_Trans_Param({R,W}, do_new_vals)];
    
    // Prove the refered DO ID must be in the same partition with the given USB TD
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_idword);
    Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid, wimpdrv_do_id.oid);
    Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(s.subjects, s.objects, s.id_mappings, wimpdrv_idword, wimpdrv_id);
    assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid) == usbtd_map_get_pid(globals, usbtd_slot_id);
    assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id);

    result
}




/*********************** Util Functions ********************/
function WSM_SecureUSBTD_CalcTDVal_ForSelfFDAndDO(
    s:state, usbtd_slot_id:uint32
) : (result:(map<FD_ID, FD_Trans_Param>, map<DO_ID, DO_Trans_Param>))
    requires InstSaneState(s)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
    requires usbtd_map_get_pid(wkm_get_globals(s.wk_mstate), usbtd_slot_id) != WS_PartitionID(PID_INVALID)
        // Requirement: The USB TD must be registered and is active

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot_id);
            usbtd_idword in s.id_mappings.usbtd_to_fd && 
            var usbtd_mapped_fdid:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
            MapGetKeys(result.0) == {usbtd_mapped_fdid}
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot_id);
            usbtd_idword in s.id_mappings.usbtd_to_do && 
            var usbtd_mapped_doid:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];
            MapGetKeys(result.1) == {usbtd_mapped_doid}
        // Property: Parsed the ID of the referenced USB FD and DO correctly 
    ensures forall id :: id in result.0
                ==> id in s.objects.usbtd_fds
    ensures forall id :: id in result.1
                ==> id in s.objects.usbtd_dos
        // Property: The mapped USB FDs must exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.0
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result.1
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot_id)
        // Property: The PID of the returned FD and DO equals to the PID stored in <usbtd_slot_id>
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    var globals := wkm_get_globals(s.wk_mstate);

    var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot_id);
    assert usbtd_slot_valid_type(globals, usbtd_slot_id);
    assert usbtd_idword != USBTD_ID_INVALID;
    var usbtd_mapped_fdid:FD_ID := s.id_mappings.usbtd_to_fd[usbtd_idword];
    var usbtd_mapped_doid:DO_ID := s.id_mappings.usbtd_to_do[usbtd_idword];

    // Prove usbtd_mapped_fdid and usbtd_mapped_doid exists in the system
    Lemma_USBTD_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, globals, usbtd_slot_id);
    assert usbtd_mapped_fdid in s.objects.usbtd_fds;
    assert usbtd_mapped_doid in s.objects.usbtd_dos;

    // Prove the PID of the returned TD equals to the PID stored in <usbtd_slot_id>
    var usbtd_mapped_fd_newvals := USBTD_MappedFD_GetValueRange(s.objects, usbtd_mapped_fdid);
    var usbtd_mapped_do_newvals := USBTD_MappedDO_GetValueRange(s.objects, usbtd_mapped_doid);
    var trans_param_fds := map[usbtd_mapped_fdid := FD_Trans_Param({R, W}, usbtd_mapped_fd_newvals)];
    var trans_param_dos := map[usbtd_mapped_doid := DO_Trans_Param({R, W}, usbtd_mapped_do_newvals)];
    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedFD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_mapped_fdid);
    Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedDO(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_mapped_doid);
    assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_mapped_fdid.oid) == usbtd_map_get_pid(globals, usbtd_slot_id); 

    (trans_param_fds, trans_param_dos)
}

// Function: Given a pair of <next_usbtd_flag, next_usbtd_slot> parsed from USB TDs, in which next_usbtd_flag == 1 or
// USB TD slot next_usbtd_slot contains a secure USB TD, return the corresponding transfers defined in this pair
function WSM_SecureUSBTD_CalcUSBTDPtrPair(s:state, next_usbtd_flag:uint32, next_usbtd_slot:uint32) : (trans_params_tds:map<TD_ID, TD_Trans_Param>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))
    
    requires next_usbtd_flag == 1 || usbtd_map_valid_slot_id(next_usbtd_slot)
    requires next_usbtd_flag != 1
                ==> (usbtd_map_valid_slot_id(next_usbtd_slot) &&
                    TestBit(usbtd_map_get_flags(wkm_get_globals(s.wk_mstate), next_usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit))
        // Requirement: If next_usbtd_flag is not equal to 1, then the next USB TD is secure
    requires next_usbtd_flag != 1
                ==> usbtd_map_get_pid(wkm_get_globals(s.wk_mstate), next_usbtd_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: If next_usbtd_flag is not equal to 1, then the next USB TD is active

    ensures var globals := wkm_get_globals(s.wk_mstate);
            next_usbtd_flag != 1
                ==> (
                    var usbtd_idword := usbtd_map_get_idword(globals, next_usbtd_slot);
                    usbtd_idword in s.id_mappings.usbtd_to_td && 
                    var usbtd_mapped_tdid:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
                    MapGetKeys(trans_params_tds) == {usbtd_mapped_tdid}
                )
        // Property: Parsed the ID of the referenced USB TD correctly 
    ensures forall id :: id in trans_params_tds
                ==> id in s.objects.usbtd_tds
        // Property: The referenced USB TDs must exist in the system
    ensures var globals := wkm_get_globals(s.wk_mstate);
            next_usbtd_flag != 1
                ==> (forall id :: id in trans_params_tds
                        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, next_usbtd_slot)
                    )
        // Property: If the termination flag is not set, then the PID of the returned TD equals to the PID stored in <next_usbtd_slot>
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    var globals := wkm_get_globals(s.wk_mstate);

    if(next_usbtd_flag == 1) then
        map[]
    else
        var usbtd_idword := usbtd_map_get_idword(globals, next_usbtd_slot);
        assert usbtd_slot_valid_type(globals, next_usbtd_slot);
        assert usbtd_idword != USBTD_ID_INVALID;
        var usbtd_mapped_tdid:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];

        // Prove usbtd_mapped_tdid in s.objects.usbtd_tds
        Lemma_USBTD_ExistInSystem_IfRegisteredAndActive(s.subjects, s.objects, s.id_mappings, globals, next_usbtd_slot);
        assert usbtd_mapped_tdid in s.objects.usbtd_tds;

        // Prove the PID of the returned TD equals to the PID stored in <next_usbtd_slot>
        var result := map[usbtd_mapped_tdid := TD_Trans_Param({R}, {})];
        Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(s.subjects, s.objects, s.id_mappings, usbtd_idword, usbtd_mapped_tdid);
        assert WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, usbtd_mapped_tdid.oid) == usbtd_map_get_pid(globals, next_usbtd_slot); 

        result
}