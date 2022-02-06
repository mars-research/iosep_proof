include "../../state_properties_OpsSaneStateSubset.s.dfy"
include "../../arch/common/arch_mem.i.dfy"

/*********************** Axioms ********************/
// [TODO][Axiom][Assumption] s.objects.usbtd_* are external objects
lemma {:axiom} Lemma_USBTDsAreExternalObjs(s:state)
    requires ValidState(s)

    ensures forall s_id, id :: s_id in WSM_AllSubjsIDs(s.subjects) &&
                    id in s.objects.usbtd_tds
                ==> !WSM_DoOwnObj(s.subjects, s_id, id.oid)
    ensures forall s_id, id :: s_id in WSM_AllSubjsIDs(s.subjects) &&
                    id in s.objects.usbtd_fds
                ==> !WSM_DoOwnObj(s.subjects, s_id, id.oid)
    ensures forall s_id, id :: s_id in WSM_AllSubjsIDs(s.subjects) &&
                    id in s.objects.usbtd_dos
                ==> !WSM_DoOwnObj(s.subjects, s_id, id.oid)




/*********************** Lemmas - Subjects ********************/
// Predicate: In the two states, the subject IDs are same
predicate WSM_SubjIDsAreSame(subjs1:WSM_Subjects, subjs2:WSM_Subjects)
{
    MapGetKeys(subjs1.wimp_drvs) == MapGetKeys(subjs2.wimp_drvs) &&
    MapGetKeys(subjs1.wimp_drvs) == MapGetKeys(subjs2.wimp_drvs) &&
    MapGetKeys(subjs1.usbpdevs) == MapGetKeys(subjs2.usbpdevs) &&
    MapGetKeys(subjs1.os_drvs) == MapGetKeys(subjs2.os_drvs) &&
    MapGetKeys(subjs1.os_devs) == MapGetKeys(subjs2.os_devs)
}

// Lemma: PEHCIs subject IDs and object IDs are unchanged in operations
lemma Lemma_PEHCIsIDsObjIDsAreUnchanged(s:state, r:state)
    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>

    requires WSM_ObjIDsAreSame(s.objects, r.objects)
    requires WSM_SubjIDsAreSame(s.subjects, r.subjects)

    requires s.activate_conds == r.activate_conds
    requires forall id :: id in s.subjects.os_devs
                ==> (s.subjects.os_devs[id].hcoded_td_id == r.subjects.os_devs[id].hcoded_td_id &&
                     s.subjects.os_devs[id].td_ids == r.subjects.os_devs[id].td_ids &&
                     s.subjects.os_devs[id].fd_ids == r.subjects.os_devs[id].fd_ids &&
                     s.subjects.os_devs[id].do_ids == r.subjects.os_devs[id].do_ids)

    ensures WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds) == WSM_AllDevIDs_pEHCIs(r.subjects, r.activate_conds)
    ensures var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
            WSM_TDsOwnedByOSDevs(s, pehci_ids) == WSM_TDsOwnedByOSDevs(r, pehci_ids) &&
            WSM_FDsOwnedByOSDevs(s, pehci_ids) == WSM_FDsOwnedByOSDevs(r, pehci_ids) &&
            WSM_DOsOwnedByOSDevs(s, pehci_ids) == WSM_DOsOwnedByOSDevs(r, pehci_ids)
{
    // Dafny can automatically prove this lemma
}  

// Lemma: OS drivers and devices have unchanged PIDs, if s.subjects is unchanged
lemma Lemma_OSSubjsHaveUnchangedPIDs_IfSubjectsAreSame(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)

    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)

    requires s.subjects == s'.subjects

    ensures forall id :: id in s.subjects.os_devs
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid) == 
                    WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.sid)
    ensures forall id :: id in s.subjects.os_drvs
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid) == 
                    WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.sid)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();

    forall id | id in s.subjects.os_devs
        ensures WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid) == 
                WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.sid)
    {
        assert WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid) == SubjPID_OSDev(s.subjects, id);
        assert WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id.sid) == SubjPID_OSDev(s'.subjects, id);
    }
}

// Lemma: WimpDrv_DrvID_ToIDWord converts word ID to Drv_ID correctly
lemma Lemma_WimpDrv_DrvID_ToIDWord_ProveCorrectness(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, wimpdrv_id_word:word, wimpdrv_id:Drv_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_id_word) in subjs.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system
    requires wimpdrv_id == WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_id_word)

    ensures WimpDrv_DrvID_ToIDWord(subjs, objs, id_mappings, wimpdrv_id) == wimpdrv_id_word
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();
}

// Lemma: USBPDev_DevID_ToAddr converts word ID to Drv_ID correctly
lemma Lemma_USBPDev_DevID_ToAddr_ProveCorrectness(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, usbpdev_addr:USBPDev_Addr, usbpdev_id:Dev_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             usbpdev_addr != usb_parse_usbpdev_addr(addr)

    requires Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr) in subjs.usbpdevs
        // Requirement: The USBPDev being accessed must be exist in the system
    requires usbpdev_id == Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr)

    ensures USBPDev_DevID_ToAddr(subjs, objs, id_mappings, usbpdev_id) == usbpdev_addr
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_USBPDevIDsMustMapToAddrs();
}

// Lemma: For wimp drivers that are currently registered in WK, WSM_SubjPID has the same output with wimpdrv_get_pid
lemma Lemma_SubjPID_RegisteredWimpDrv_SubjPIDEqualsToPIDInRecord(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, wimpdrv_slot:word, wimpdrv_sid:Subject_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_id_word) in subjs.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete

    requires var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
             var wimpdrv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_id_word);
             wimpdrv_sid == wimpdrv_id.sid

    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, wimpdrv_sid) == wimpdrv_get_pid(globals, wimpdrv_slot)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();

    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_id_word);
    var subj_pid := WSM_SubjPID(subjs, objs, id_mappings, globals, wimpdrv_sid);

    assert subj_pid == SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, wimpdrv_id);

    assert WimpDrv_DrvID_ToIDWord(subjs, objs, id_mappings, wimpdrv_id) == wimpdrv_id_word;
    assert subj_pid == SubjPID_WimpDrv_ByIDWord(globals, wimpdrv_id_word);
}

// Lemma: For USBPDevs that are currently registered in WK, WSM_SubjPID has the same output with usbpdev_get_pid
lemma Lemma_SubjPID_RegisteredUSBPDev_SubjPIDEqualsToPIDInRecord(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbpdev_slot:word, usbpdev_sid:Subject_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(subjs, usbpdev_id)
            ==> subjs.usbpdevs[usbpdev_id].active_in_os == false
        // Properties specific to USBPDev

    requires usbpdev_valid_slot_id(usbpdev_slot)
    requires var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
            var empty_addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(empty_addr_raw) &&
            usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
            usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr_raw)
    requires var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
             var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr);
             usbpdev_id in subjs.usbpdevs
        // Requirement: The USBPDev must be exist in the system

    requires usbpdev_get_updateflag(globals, usbpdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete

    requires var usbpdev_addr_raw := usbpdev_get_addr(globals, usbpdev_slot);
             var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr);
             usbpdev_sid == usbpdev_id.sid

    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, usbpdev_sid) == usbpdev_get_pid(globals, usbpdev_slot)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_USBPDevIDsMustMapToAddrs();
}

// Lemma: For eEHCIs that are currently registered in WK, WSM_SubjPID has the same output with wimpdrv_get_pid
lemma Lemma_SubjPID_RegisteredEEHCI_SubjPIDEqualsToPIDInRecord(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, eehci_slot:word, eehci_sid:Subject_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires eehci_valid_slot_id(eehci_slot)
    requires var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             eehci_idword != eEHCI_ID_INVALID
    requires var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(subjs, objs, id_mappings, eehci_idword);
             eehci_id in subjs.eehcis
        // Requirement: The eEHCIs being accessed must be exist in the system

    requires var eehci_idword := eehci_mem_get_eehci_id(globals, eehci_slot);
             var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(subjs, objs, id_mappings, eehci_idword);
             eehci_sid == eehci_id.sid

    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, eehci_sid) == eehci_info_get_pid(globals, eehci_slot)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_EEHCIIDsMustMapToIDWords();
}

lemma Lemma_SubjPID_WimpDrvNotInRecord_SubjPIDEqualsToNULL(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, wimpdrv_idword:uint32, wimpdrv_sid:Subject_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires wimpdrv_idword != WimpDrv_ID_RESERVED_EMPTY
    requires WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_idword) in subjs.wimp_drvs 

    requires forall i:word :: wimpdrv_valid_slot_id(i)
                ==> wimpdrv_get_id_word(globals, i) != wimpdrv_idword
        // Requirement: The wimp driver is not in record

    requires var wimpdrv_id := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_idword);
             wimpdrv_sid == wimpdrv_id.sid

    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, wimpdrv_sid) == WS_PartitionID(PID_INVALID)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();
}

lemma Lemma_SubjPID_USBPDevNotInRecord_SubjPIDEqualsToNULL(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, 
    usbpdev_addr_low:word, usbpdev_addr_high:word, usbpdev_sid:Subject_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(subjs, usbpdev_id)
            ==> subjs.usbpdevs[usbpdev_id].active_in_os == false

    requires var usbpdev_addr_raw := UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low);
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
             usb_is_usbpdev_addr_valid(empty_addr) &&
             usb_parse_usbpdev_addr(usbpdev_addr_raw) != usb_parse_usbpdev_addr(empty_addr)
    requires var usbpdev_addr_raw := UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low);
             var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr);
             usbpdev_id in subjs.usbpdevs

    requires forall i:word :: usbpdev_valid_slot_id(i)
                ==> !(usbpdev_get_addr_low(globals, i) == usbpdev_addr_low &&
                        usbpdev_get_addr_high(globals, i) == usbpdev_addr_high)
        // Requirement: The USBPDev is not in record

    requires var usbpdev_addr_raw := UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low);
             var usbpdev_addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
             var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr);
             usbpdev_sid == usbpdev_id.sid

    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, usbpdev_sid) == WS_PartitionID(PID_INVALID)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_USBPDevIDsMustMapToAddrs();

    var dev_pid := WSM_SubjPID(subjs, objs, id_mappings, globals, usbpdev_sid);
    assert dev_pid == SubjPID_USBPDev_ByDevID(subjs, objs, id_mappings, globals, Dev_ID(usbpdev_sid));

    var usbpdev_addr := USBPDev_DevID_ToAddr(subjs, objs, id_mappings, Dev_ID(usbpdev_sid));
    assert dev_pid == SubjPID_USBPDev_ByAddr(subjs, objs, id_mappings, globals, usbpdev_addr);

    var usbpdev_addr_raw := UInt64_FromTwoUInt32s(usbpdev_addr_high, usbpdev_addr_low);
    assert usbpdev_addr == usb_parse_usbpdev_addr(usbpdev_addr_raw);

    Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr();
    assert !usbpdev_addr_in_record(globals, usbpdev_addr);
}

lemma Lemma_SubjPID_EEHCINotInRecord_SubjPIDEqualsToNULL(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, 
    eehci_idword:word, eehci_sid:Subject_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires eehci_idword != eEHCI_ID_INVALID
    requires var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(subjs, objs, id_mappings, eehci_idword);
             eehci_id in subjs.eehcis

    requires forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_mem_get_eehci_id(globals, i) != eehci_idword
        // Requirement: The eEHCI is not in record

    requires var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(subjs, objs, id_mappings, eehci_idword);
             eehci_sid == eehci_id.sid

    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, eehci_sid) == WS_PartitionID(PID_INVALID)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_EEHCIIDsMustMapToIDWords();
}

// Lemma: If <s.subjects> is unchanged, and Wimp drivers, eEHCIs, USBPDevs' ID words, flags and PIDs are unchanged, 
// then WSM_SubjPID is unchanged
lemma Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)

    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    requires forall i :: wimpdrv_valid_slot_id(i)
                ==> (wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), i) == wimpdrv_get_id_word(wkm_get_globals(s'.wk_mstate), i) &&
                     wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), i) == wimpdrv_do_get_flag(wkm_get_globals(s'.wk_mstate), i) &&
                     wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), i) == wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), i))
    requires forall i :: usbpdev_valid_slot_id(i)
                ==> (usbpdev_get_addr(wkm_get_globals(s.wk_mstate), i) == usbpdev_get_addr(wkm_get_globals(s'.wk_mstate), i) &&
                     usbpdev_get_updateflag(wkm_get_globals(s.wk_mstate), i) == usbpdev_get_updateflag(wkm_get_globals(s'.wk_mstate), i) &&
                     usbpdev_get_pid(wkm_get_globals(s.wk_mstate), i) == usbpdev_get_pid(wkm_get_globals(s'.wk_mstate), i))
    requires forall i :: eehci_valid_slot_id(i)
                ==> (eehci_mem_get_eehci_id(wkm_get_globals(s.wk_mstate), i) == eehci_mem_get_eehci_id(wkm_get_globals(s'.wk_mstate), i) &&
                     eehci_info_get_pid(wkm_get_globals(s.wk_mstate), i) == eehci_info_get_pid(wkm_get_globals(s'.wk_mstate), i))
        // Requirement: Wimp drivers, eEHCIs, USBPDevs' ID words, flags and PIDs are unchanged

    ensures forall id :: WSM_IsSubjID(s.subjects, id)
                ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) == WSM_SubjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall id | WSM_IsSubjID(s.subjects, id)
        ensures WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id)
    {
        if(Drv_ID(id) in subjs.os_drvs)
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (Dev_ID(id) in subjs.os_devs)
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (WSM_IsWimpDrvID(subjs, Drv_ID(id)))
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else if (WSM_IsUSBPDevID(subjs, Dev_ID(id)))
        {
            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
        else
        {
            assert WSM_IsEEHCIDevID(subjs, Dev_ID(id));

            assert WSM_SubjPID(subjs, objs, id_mappings, globals, id) == WSM_SubjPID(subjs', objs', id_mappings', globals', id);
        }
    }
}

// Lemma: If a wimp driver owns an active DO, then the wimp driver must be registered
lemma Lemma_OwnerOfActiveWimpDrvDO_MustHaveIDWordInRecord(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, drv_id:Drv_ID, o_id:Object_ID)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(subjs, objs, id_mappings, globals)

    requires WSM_IsWimpDrvDO(objs, o_id)
    requires WSM_IsActiveObj(subjs, objs, id_mappings, globals, o_id)
        // The object is a wimp driver's DO and is active
    requires drv_id == WimpDrvDO_FindOwner(subjs, objs, o_id)

    ensures var id_word := WimpDrv_DrvID_ToIDWord(subjs, objs, id_mappings, drv_id);
            wimpdrv_idword_in_record(globals, id_word)
{
    assert WSM_DoOwnObj(subjs, drv_id.sid, o_id);
    Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, drv_id.sid, o_id);
    assert WSM_IsActiveSubj(subjs, objs, id_mappings, globals, drv_id.sid);
}

// Lemma: Registered and active wimp drivers must exist in the system
lemma Lemma_WimpDrv_DORegionMatchInfoInObjsAddrs(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, wimpdrv_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(globals)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
    requires WK_ValidObjAddrs_WimpDrv_DOPAddrs(subjs, objs, id_mappings, objs_addrs, globals)
    
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(globals, wimpdrv_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The wimp driver must be registered and is active

    ensures forall wimpdrv_do_id, pmem :: WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && 
                pmem in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
            ==> (wimpdrv_do_get_paddr_base(globals, wimpdrv_slot) == pmem.paddr_start &&
                wimpdrv_do_get_paddr_end(globals, wimpdrv_slot) == pmem.paddr_end)
{
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var wimpdrv_idword := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(subjs, objs, id_mappings, wimpdrv_idword);

    assert wimpdrv_idword in id_mappings.wimpdrv_ids;
    assert wimpdrv_get_pid(globals, wimpdrv_slot) != WS_PartitionID(PID_INVALID);

    // Apply WK_ValidObjAddrs_WimpDrv_DOPAddrs
    assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(subjs, objs, id_mappings, objs_addrs, globals);
    assert WSM_IsWimpDrvID(subjs, wimpdrv_id);

    forall wimpdrv_do_id, pmem | WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) && 
                pmem in objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
        ensures wimpdrv_do_get_paddr_base(globals, wimpdrv_slot) == pmem.paddr_start
        ensures wimpdrv_do_get_paddr_end(globals, wimpdrv_slot) == pmem.paddr_end
}

lemma Lemma_USBPDev_PIDsAreUnchanged_IfGWimpUSBPDevInfoIsUnchanged(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals1:globalsmap, globals2:globalsmap
)
    requires WK_ValidGlobalState(globals1)
    requires WK_ValidGlobalState(globals2)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())

    ensures forall dev_id :: WSM_IsUSBPDevID(subjs, dev_id)
                ==> SubjPID_USBPDev_ByDevID(subjs, objs, id_mappings, globals1, dev_id) ==
                    SubjPID_USBPDev_ByDevID(subjs, objs, id_mappings, globals2, dev_id)
{
    // Dafny can automatically prove this lemma
}




/*********************** Lemmas - Objects ********************/
// Predicate: In the two states, the object IDs are same
predicate WSM_ObjIDsAreSame(objs1:WSM_Objects, objs2:WSM_Objects)
{
    MapGetKeys(objs1.os_tds) == MapGetKeys(objs2.os_tds) &&
    MapGetKeys(objs1.os_fds) == MapGetKeys(objs2.os_fds) &&
    MapGetKeys(objs1.os_dos) == MapGetKeys(objs2.os_dos) &&

    MapGetKeys(objs1.eehci_hcoded_tds) == MapGetKeys(objs2.eehci_hcoded_tds) &&
    objs1.eehci_other_tds == objs2.eehci_other_tds &&
    objs1.eehci_fds == objs2.eehci_fds &&
    objs1.eehci_dos == objs2.eehci_dos &&

    MapGetKeys(objs1.usbpdev_tds) == MapGetKeys(objs2.usbpdev_tds) &&
    MapGetKeys(objs1.usbpdev_fds) == MapGetKeys(objs2.usbpdev_fds) &&
    MapGetKeys(objs1.usbpdev_dos) == MapGetKeys(objs2.usbpdev_dos) &&
    MapGetKeys(objs1.wimpdrv_dos) == MapGetKeys(objs2.wimpdrv_dos) &&

    objs1.usbtd_tds == objs2.usbtd_tds &&
    objs1.usbtd_fds == objs2.usbtd_fds &&
    objs1.usbtd_dos == objs2.usbtd_dos
}

// Predicate: Does the given object not overlap with the given physical memory range [paddr_start, paddr_end) 
predicate obj_exclude_pmem_region(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, id:Object_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires WSM_IsObjID(objs, id)
    requires paddr_start <= paddr_end
{
    reveal WK_ValidObjsAddrs();

    assert TD_ID(id) in objs_addrs.tds_addrs || FD_ID(id) in objs_addrs.fds_addrs || DO_ID(id) in objs_addrs.dos_addrs;

    if (TD_ID(id) in objs_addrs.tds_addrs) then
        forall pmem :: pmem in objs_addrs.tds_addrs[TD_ID(id)].paddrs
            ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
    else if (FD_ID(id) in objs_addrs.fds_addrs) then
        forall pmem :: pmem in objs_addrs.fds_addrs[FD_ID(id)].paddrs
            ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
    else
        assert DO_ID(id) in objs_addrs.dos_addrs;
        forall pmem :: pmem in objs_addrs.dos_addrs[DO_ID(id)].paddrs
            ==> !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
}

// Predicate: The given wimp driver has been registered in <g_wimpdrv_info> and its DO contains the given memory region
predicate wimpdrv_DO_include_mem_region(globals:globalsmap, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_WimpDrvs_ValidGlobalVarValues(globals)
    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
{
    var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot);
    var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot);

    wimpdrv_do_get_flag(globals, wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete &&
    is_mem_region_inside(do_paddr_base, do_paddr_end, paddr_start, paddr_end)
}

lemma Lemma_WSM_IsWimpDrvDOID_Property(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, id:DO_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsWimpDrvDOID(objs, id)

    ensures !WSM_IsOSObj(objs, id.oid)
    ensures !WSM_IsEEHCIObj(objs, id.oid)
    ensures !WSM_IsUSBPDevObj(objs, id.oid)
    ensures !WSM_IsUSBTDMappedObj(objs, id.oid)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
}

// Lemma: In a valid state, if a wimp driver is in the system, then its DO must also exist in the system
lemma Lemma_wimpdrv_in_system_ProveItsDOMustBeInSystem(s:state, drv_id:Drv_ID)
    requires ValidState(s)
    requires drv_id in s.subjects.wimp_drvs
    ensures var wimpdrv_do_id := s.subjects.wimp_drvs[drv_id].do_id;
            WSM_IsWimpDrvDOID(s.objects, wimpdrv_do_id)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
}

// Lemma: Prove the given TD fulfills <obj_exclude_pmem_region>
lemma Lemma_obj_exclude_pmem_region_Prove_ForTD(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, id:Object_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
    requires WK_ValidObjs_ObjIDs(objs)

    requires WSM_IsObjID(objs, id)
    requires paddr_start <= paddr_end

    requires TD_ID(id) in objs_addrs.tds_addrs
    requires forall pmem :: pmem in objs_addrs.tds_addrs[TD_ID(id)].paddrs
            ==> (pmem.paddr_start <= pmem.paddr_end &&
                !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end))

    ensures obj_exclude_pmem_region(objs, objs_addrs, globals, id, paddr_start, paddr_end)
{
    reveal WK_ValidObjsAddrs();
    reveal WK_ValidObjs_ObjIDs();
}

// Lemma: Prove the given FD fulfills <obj_exclude_pmem_region>
lemma Lemma_obj_exclude_pmem_region_Prove_ForFD(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, id:Object_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
    requires WK_ValidObjs_ObjIDs(objs)

    requires WSM_IsObjID(objs, id)
    requires paddr_start <= paddr_end

    requires FD_ID(id) in objs_addrs.fds_addrs
    requires forall pmem :: pmem in objs_addrs.fds_addrs[FD_ID(id)].paddrs
            ==> (pmem.paddr_start <= pmem.paddr_end &&
                !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end))

    ensures obj_exclude_pmem_region(objs, objs_addrs, globals, id, paddr_start, paddr_end)
{
    reveal WK_ValidObjsAddrs();
    reveal WK_ValidObjs_ObjIDs();
}

// Lemma: Prove the given DO fulfills <obj_exclude_pmem_region>
lemma Lemma_obj_exclude_pmem_region_Prove_ForDO(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, id:Object_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)
    requires WK_ValidObjs_ObjIDs(objs)

    requires WSM_IsObjID(objs, id)
    requires paddr_start <= paddr_end

    requires DO_ID(id) in objs_addrs.dos_addrs
    requires forall pmem :: pmem in objs_addrs.dos_addrs[DO_ID(id)].paddrs
            ==> (pmem.paddr_start <= pmem.paddr_end &&
                !is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end))

    ensures obj_exclude_pmem_region(objs, objs_addrs, globals, id, paddr_start, paddr_end)
{
    reveal WK_ValidObjsAddrs();
    reveal WK_ValidObjs_ObjIDs();
}

// Lemma: Internal objects must have the same PID with its owner subject
lemma Lemma_ObjPID_SamePIDWithOwnerSubject(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, s_id:Subject_ID, o_id:Object_ID)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(subjs, objs, id_mappings, globals)

    requires WSM_IsSubjID(subjs, s_id)
    requires WSM_IsObjID(objs, o_id)
    requires WSM_DoOwnObj(subjs, s_id, o_id)
    
    ensures WSM_SubjPID(subjs, objs, id_mappings, globals, s_id) == WSM_ObjPID(subjs, objs, id_mappings, globals, o_id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition();
    reveal WK_ValidSubjs_eEHCIs();

    var subj_pid := WSM_SubjPID(subjs, objs, id_mappings, globals, s_id);
    var obj_pid := WSM_ObjPID(subjs, objs, id_mappings, globals, o_id);

    if(Drv_ID(s_id) in subjs.os_drvs) 
    {
        assert WSM_IsOSObj(objs, o_id);
        assert subj_pid == obj_pid;
    }
    else if (Dev_ID(s_id) in subjs.os_devs)
    {
        assert WSM_IsOSObj(objs, o_id);
        assert subj_pid == obj_pid;
    }
    else if (WSM_IsWimpDrvID(subjs, Drv_ID(s_id)))
    {
        assert WSM_IsWimpDrvDO(objs, o_id);
        assert subj_pid == obj_pid;
    }
    else if (WSM_IsUSBPDevID(subjs, Dev_ID(s_id)))
    {
        assert WSM_IsUSBPDevObj(objs, o_id);
        assert subj_pid == obj_pid;
    }
    else
    {
        assert WSM_IsEEHCIDevID(subjs, Dev_ID(s_id));

        assert WSM_IsEEHCIObj(objs, o_id);
        assert subj_pid == obj_pid;
    }
}

lemma Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbtd_slot:word, o_id:Object_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
             usbtd_idword != USBTD_ID_INVALID
    requires WSM_IsUSBTDMappedObj(objs, o_id)
    requires var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
             USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, o_id) == usbtd_idword
        // Requirement: The USB TD mapped object must be exist in the system

    ensures WSM_ObjPID(subjs, objs, id_mappings, globals, o_id) == usbtd_map_get_pid(globals, usbtd_slot)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
}

lemma Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord_TDsFDsDOs(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, 
    usbtd_slot:word, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
             usbtd_idword != USBTD_ID_INVALID
    requires forall id :: id in td_ids
                ==> WSM_IsUSBTDMappedObj(objs, id.oid)
    requires forall id :: id in fd_ids
                ==> WSM_IsUSBTDMappedObj(objs, id.oid)
    requires forall id :: id in do_ids
                ==> WSM_IsUSBTDMappedObj(objs, id.oid)
    requires var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
             forall id :: id in td_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid) == usbtd_idword
    requires var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
             forall id :: id in fd_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid) == usbtd_idword
    requires var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
             forall id :: id in do_ids
                ==> USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid) == usbtd_idword
        // Requirement: The USB TD mapped object must be exist in the system

    ensures forall id :: id in td_ids
                ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot)
    ensures forall id :: id in fd_ids
                ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot)
    ensures forall id :: id in do_ids
                ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot)
{
    forall id | id in td_ids
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot)
    {
        Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(subjs, objs, id_mappings, globals, usbtd_slot, id.oid);
    }

    forall id | id in fd_ids
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot)
    {
        Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(subjs, objs, id_mappings, globals, usbtd_slot, id.oid);
    }

    forall id | id in do_ids
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == usbtd_map_get_pid(globals, usbtd_slot)
    {
        Lemma_ObjPID_RegisteredUSBTD_ObjPIDEqualsToPIDInRecord(subjs, objs, id_mappings, globals, usbtd_slot, id.oid);
    }
}


lemma Lemma_ObjPID_UnRegisteredUSBTD_ObjPIDEqualsToInvalid(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbtd_idword:word, o_id:Object_ID
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
                    usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
                ==> usbtd_map_get_idword(globals, i) != usbtd_idword
        // Requirement: <usbtd_idword> is not registered yet
    requires WSM_IsUSBTDMappedObj(objs, o_id)
    requires USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, o_id) == usbtd_idword
        // Requirement: The USB TD mapped object must be exist in the system

    ensures WSM_ObjPID(subjs, objs, id_mappings, globals, o_id) == WS_PartitionID(PID_INVALID)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
}

// Lemma: For a sane (valid and secure) state, if a wimp driver's DO is being accessed (certainly by paddrs), then the  
// same subject must not be accessing other objects
lemma Lemma_subjects_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs(
    s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
    requires wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)

    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The wimp driver must be registered and active

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            forall o_id :: WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                    WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id)
                ==> obj_exclude_pmem_region(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate), o_id, paddr_start, paddr_end)
        // Property: if a wimp driver's DO is being accessed, then the same subject must not be accessing other objects
{
    reveal WK_ValidObjsAddrs();
    reveal WK_ValidObjs_ObjIDs();

    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_id := WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    // Prove the wimp driver's DO is active
    assert WSM_DoOwnObj(s.subjects, wimpdrv_id.sid, wimpdrv_do_id.oid);
    Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_id.sid, wimpdrv_do_id.oid);
    Lemma_SubjPID_RegisteredWimpDrv_SubjPIDEqualsToPIDInRecord(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_slot, wimpdrv_id.sid);
    assert WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, wimpdrv_do_id.oid);

    forall o_id | WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, o_id)
        ensures obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end)
    {
        if(WSM_IsOSObj(s.objects, o_id))
        {
            Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForOSObj(s, wimpdrv_slot, paddr_start, paddr_end);
        }
        else if(WSM_IsEEHCIObj(s.objects, o_id))
        {
            Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForEEHCIObj(s, wimpdrv_slot, paddr_start, paddr_end);
        }
        else if(WSM_IsUSBPDevObj(s.objects, o_id))
        {
            Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForUSBPDevObj(s, wimpdrv_slot, paddr_start, paddr_end);
        }
        else if(WSM_IsWimpDrvDO(s.objects, o_id))
        {
            Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForOtherWimpDrvObj(s, wimpdrv_slot, paddr_start, paddr_end);
        }
        else
        {
            assert WSM_IsUSBTDMappedObj(s.objects, o_id);
            Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForUSBTDMappedObj(s, wimpdrv_slot, paddr_start, paddr_end);
        }
    }
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WSM_ObjPID is unchanged
lemma Lemma_WSM_ObjPID_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: id in s'.objects.os_tds
                ==> s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    requires forall id :: id in s'.objects.os_fds
                ==> s.objects.os_fds[id].pid == s'.objects.os_fds[id].pid
    requires forall id :: id in s'.objects.os_dos
                ==> s.objects.os_dos[id].pid == s'.objects.os_dos[id].pid
        // Requirement: OS objects' PIDs are unchanged

    ensures forall o_id :: WSM_IsObjID(s.objects, o_id) <==> WSM_IsObjID(s'.objects, o_id)
    ensures forall o_id :: WSM_IsObjID(s.objects, o_id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), o_id)
        // Requirement: Object PIDs are unchanged
{
    // Dafny can automatically prove this lemma
}

// Lemma: If the given <usbtd_idword> maps to the given <usbtd_mapped_tdid>, then 
// USBTDMappedObj_IDToUSBTDIDWord converts TD ID to USB TD's ID word correctly
lemma Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedTD(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, usbtd_idword:word, usbtd_mapped_tdid:TD_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires usbtd_idword != USBTD_ID_INVALID
    requires usbtd_idword in id_mappings.usbtd_to_td
    requires usbtd_mapped_tdid == id_mappings.usbtd_to_td[usbtd_idword]
    requires usbtd_mapped_tdid in objs.usbtd_tds
        // Requirement: The mapped TD must be exist in the system

    ensures USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, usbtd_mapped_tdid.oid) == usbtd_idword
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    if(USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, usbtd_mapped_tdid.oid) != usbtd_idword)
    {
        var t_usbtd_idword:word :| t_usbtd_idword != usbtd_idword &&
                    (
                        (t_usbtd_idword in id_mappings.usbtd_to_td &&
                        id_mappings.usbtd_to_td[t_usbtd_idword] == TD_ID(usbtd_mapped_tdid.oid)) ||
                        (t_usbtd_idword in id_mappings.usbtd_to_fd &&
                        id_mappings.usbtd_to_fd[t_usbtd_idword] == FD_ID(usbtd_mapped_tdid.oid)) ||
                        (t_usbtd_idword in id_mappings.usbtd_to_do &&
                        id_mappings.usbtd_to_do[t_usbtd_idword] == DO_ID(usbtd_mapped_tdid.oid))
                    );

        assert false;
    }
}

// Lemma: If the given <usbtd_idword> maps to the given <usbtd_mapped_fdid>, then 
// USBTDMappedObj_IDToUSBTDIDWord converts TD ID to USB TD's ID word correctly
lemma Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedFD(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, usbtd_idword:word, usbtd_mapped_fdid:FD_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires usbtd_idword != USBTD_ID_INVALID
    requires usbtd_idword in id_mappings.usbtd_to_fd
    requires usbtd_mapped_fdid == id_mappings.usbtd_to_fd[usbtd_idword]
    requires usbtd_mapped_fdid in objs.usbtd_fds
        // Requirement: The mapped FD must be exist in the system

    ensures USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, usbtd_mapped_fdid.oid) == usbtd_idword
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    if(USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, usbtd_mapped_fdid.oid) != usbtd_idword)
    {
        var t_usbtd_idword:word :| t_usbtd_idword != usbtd_idword &&
                    (
                        (t_usbtd_idword in id_mappings.usbtd_to_td &&
                        id_mappings.usbtd_to_td[t_usbtd_idword] == TD_ID(usbtd_mapped_fdid.oid)) ||
                        (t_usbtd_idword in id_mappings.usbtd_to_fd &&
                        id_mappings.usbtd_to_fd[t_usbtd_idword] == FD_ID(usbtd_mapped_fdid.oid)) ||
                        (t_usbtd_idword in id_mappings.usbtd_to_do &&
                        id_mappings.usbtd_to_do[t_usbtd_idword] == DO_ID(usbtd_mapped_fdid.oid))
                    );

        assert false;
    }
}

// Lemma: If the given <usbtd_idword> maps to the given <usbtd_mapped_doid>, then 
// USBTDMappedObj_IDToUSBTDIDWord converts TD ID to USB TD's ID word correctly
lemma Lemma_USBTDMappedObj_IDToUSBTDIDWord_ProveCorrectness_ForMappedDO(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, usbtd_idword:word, usbtd_mapped_doid:DO_ID)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires usbtd_idword != USBTD_ID_INVALID
    requires usbtd_idword in id_mappings.usbtd_to_do
    requires usbtd_mapped_doid == id_mappings.usbtd_to_do[usbtd_idword]
    requires usbtd_mapped_doid in objs.usbtd_dos
        // Requirement: The mapped DO must be exist in the system

    ensures USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, usbtd_mapped_doid.oid) == usbtd_idword
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    if(USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, usbtd_mapped_doid.oid) != usbtd_idword)
    {
        var t_usbtd_idword:word :| t_usbtd_idword != usbtd_idword &&
                    (
                        (t_usbtd_idword in id_mappings.usbtd_to_td &&
                        id_mappings.usbtd_to_td[t_usbtd_idword] == TD_ID(usbtd_mapped_doid.oid)) ||
                        (t_usbtd_idword in id_mappings.usbtd_to_fd &&
                        id_mappings.usbtd_to_fd[t_usbtd_idword] == FD_ID(usbtd_mapped_doid.oid)) ||
                        (t_usbtd_idword in id_mappings.usbtd_to_do &&
                        id_mappings.usbtd_to_do[t_usbtd_idword] == DO_ID(usbtd_mapped_doid.oid))
                    );

        assert false;
    }
}

lemma Lemma_AllIDsOfTDsFDsDOs_MustBeInAllObjIDs(s:state, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires forall td_id :: td_id in td_ids ==> td_id in WSM_AllTDIDs(s.objects)
    requires forall fd_id :: fd_id in fd_ids ==> fd_id in WSM_AllFDIDs(s.objects)
    requires forall do_id :: do_id in do_ids ==> do_id in WSM_AllDOIDs(s.objects)

    ensures TDIDsToObjIDs(td_ids) <= WSM_AllObjIDs(s.objects)
    ensures FDIDsToObjIDs(fd_ids) <= WSM_AllObjIDs(s.objects)
    ensures DOIDsToObjIDs(do_ids) <= WSM_AllObjIDs(s.objects)
    ensures var obj_ids := TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids);
            obj_ids <= WSM_AllObjIDs(s.objects);
{
    // Dafny can automatically prove this lemma
}




/*********************** Private Lemmas ********************/
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s:state, wimpdrv_slot:word)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            var do_paddr_base := wimpdrv_do_get_paddr_base(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var do_paddr_end := wimpdrv_do_get_paddr_end(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                            ==> (pmem2.paddr_start == do_paddr_base && pmem2.paddr_end == do_paddr_end)
{
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);
}

lemma Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForOSObj(
    s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
    requires wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)

    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
             WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            forall o_id :: WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                    WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) &&
                    WSM_IsOSObj(s.objects, o_id)
                ==> obj_exclude_pmem_region(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate), o_id, paddr_start, paddr_end)
        // Property: If the object is an active OS object, then the object is not in the memory region 
        // [paddr_start, paddr_end), which is inside a wimp driver's DO
{
    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    forall o_id | WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, o_id) &&
                 WSM_IsOSObj(s.objects, o_id)
        ensures obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end)
    {
        assert WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);
        assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);
        reveal WK_SecureObjsAddrs_MemSeparation();
        reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

        var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot);
        var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot);
        assert is_mem_region_inside(do_paddr_base, do_paddr_end, paddr_start, paddr_end);

        if(WSM_IsOSTDID(s.objects, TD_ID(o_id)))
        {
            forall pmem1 | pmem1 in s.objs_addrs.tds_addrs[TD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForTD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else if(WSM_IsOSFDID(s.objects, FD_ID(o_id)))
        {
            forall pmem1 | pmem1 in s.objs_addrs.fds_addrs[FD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForFD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else
        {
            assert WSM_IsOSDOID(s.objects, DO_ID(o_id));

            forall pmem1 | pmem1 in s.objs_addrs.dos_addrs[DO_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForDO(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
    }
}

lemma Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForEEHCIObj(
    s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
    requires wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)

    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
             WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            forall o_id :: WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                    WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) &&
                    WSM_IsEEHCIObj(s.objects, o_id)
                ==> obj_exclude_pmem_region(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate), o_id, paddr_start, paddr_end)
        // Property: If the object is an active OS object, then the object is not in the memory region 
        // [paddr_start, paddr_end), which is inside a wimp driver's DO
{
    reveal WK_ValidObjsAddrs();

    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    forall o_id | WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, o_id) &&
                 WSM_IsEEHCIObj(s.objects, o_id)
        ensures obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end)
    {
        assert WK_ValidObjsAddrs_Separation(s.objects, s.objs_addrs, globals);
        assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);

        var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot);
        var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot);
        assert is_mem_region_inside(do_paddr_base, do_paddr_end, paddr_start, paddr_end);

        if(TD_ID(o_id) in s.objects.eehci_other_tds)
        {
            forall pmem1 | pmem1 in s.objs_addrs.tds_addrs[TD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForTD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else if(TD_ID(o_id) in s.objects.eehci_hcoded_tds)
        {
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else if(FD_ID(o_id) in s.objects.eehci_fds)
        {
            forall pmem1 | pmem1 in s.objs_addrs.fds_addrs[FD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForFD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else
        {
            assert DO_ID(o_id) in s.objects.eehci_dos;

            forall pmem1 | pmem1 in s.objs_addrs.dos_addrs[DO_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForDO(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
    }
}

lemma Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForUSBPDevObj(
    s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
    requires wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)

    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
             WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            forall o_id :: WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                    WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) &&
                    WSM_IsUSBPDevObj(s.objects, o_id)
                ==> obj_exclude_pmem_region(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate), o_id, paddr_start, paddr_end)
        // Property: If the object is an active OS object, then the object is not in the memory region 
        // [paddr_start, paddr_end), which is inside a wimp driver's DO
{
    reveal WK_ValidObjsAddrs();

    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    forall o_id | WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, o_id) &&
                 WSM_IsUSBPDevObj(s.objects, o_id)
        ensures obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end)
    {
        assert WK_ValidObjsAddrs_Separation(s.objects, s.objs_addrs, globals);
        assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);

        var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot);
        var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot);
        assert is_mem_region_inside(do_paddr_base, do_paddr_end, paddr_start, paddr_end);

        if(TD_ID(o_id) in s.objects.usbpdev_tds)
        {
            forall pmem1 | pmem1 in s.objs_addrs.tds_addrs[TD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForTD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else if(FD_ID(o_id) in s.objects.usbpdev_fds)
        {
            forall pmem1 | pmem1 in s.objs_addrs.fds_addrs[FD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForFD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else
        {
            assert DO_ID(o_id) in s.objects.usbpdev_dos;

            forall pmem1 | pmem1 in s.objs_addrs.dos_addrs[DO_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForDO(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
    }
}

// [NOTE] Needs 50s to verify
lemma {:timeLimitMultiplier 7} Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForOtherWimpDrvObj(
    s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
    requires wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)

    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
             WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            forall o_id :: WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                    WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) &&
                    WSM_IsWimpDrvDO(s.objects, o_id)
                ==> obj_exclude_pmem_region(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate), o_id, paddr_start, paddr_end)
        // Property: If the object is an active OS object, then the object is not in the memory region 
        // [paddr_start, paddr_end), which is inside a wimp driver's DO
{
    reveal WK_ValidObjsAddrs();

    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    forall o_id | WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, o_id) &&
                 WSM_IsWimpDrvDO(s.objects, o_id)
        ensures obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end)
    {
        assert WK_ValidObjsAddrs_Separation(s.objects, s.objs_addrs, globals);
        assert WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);
        assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);
        reveal WK_SecureObjsAddrs_MemSeparation();
        reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();

        var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot);
        var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot);
        assert is_mem_region_inside(do_paddr_base, do_paddr_end, paddr_start, paddr_end);

        {
            assert DO_ID(o_id) in s.objects.wimpdrv_dos;

            var temp_wimpdrv_id:Drv_ID := WimpDrvDO_FindOwner(s.subjects, s.objects, o_id);
            var temp_wimpdrv_id_word:word := WimpDrv_DrvID_ToIDWord(s.subjects, s.objects, s.id_mappings, temp_wimpdrv_id);
            Lemma_OwnerOfActiveWimpDrvDO_MustHaveIDWordInRecord(s.subjects, s.objects, s.id_mappings, globals, temp_wimpdrv_id, o_id);
            var temp_wimpdrv_slot := wimpdrv_get_slot_by_idword(globals, temp_wimpdrv_id_word);

            // Prove the wimp driver <temp_wimpdrv_id> is active
            Lemma_ObjPID_SamePIDWithOwnerSubject(s.subjects, s.objects, s.id_mappings, globals, temp_wimpdrv_id.sid, o_id);
            assert wimpdrv_get_pid(globals, temp_wimpdrv_slot) != WS_PartitionID(PID_INVALID);
            
            // Apply WK_WimpDrv_DOMustNotOverlapWithEachOther
            assert WK_WimpDrv_DOMustNotOverlapWithEachOther(globals, temp_wimpdrv_slot, wimpdrv_slot);

            forall pmem1 | pmem1 in s.objs_addrs.dos_addrs[DO_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert pmem1.paddr_start == wimpdrv_do_get_paddr_base(globals, temp_wimpdrv_slot);
                assert pmem1.paddr_end == wimpdrv_do_get_paddr_end(globals, temp_wimpdrv_slot);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForDO(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
    }
}

// [NOTE] Needs 30s to verify
lemma {:timeLimitMultiplier 5} Lemma_InstSaneState_accessing_wimpdrv_DO_ProveNotAccessingOtherObjs_ForUSBTDMappedObj(
    s:state, wimpdrv_slot:word, paddr_start:paddr, paddr_end:uint
)
    requires InstSaneState(s)

    requires wimpdrv_valid_slot_id(wimpdrv_slot)
    requires paddr_start <= paddr_end
    requires wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, paddr_start, paddr_end)

    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: The wimp driver being accessed must be exist in the system

    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot) != WS_PartitionID(PID_INVALID)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
             WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), wimpdrv_do_id.oid)

    ensures var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            forall o_id :: WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                    WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), o_id) &&
                    WSM_IsUSBTDMappedObj(s.objects, o_id)
                ==> obj_exclude_pmem_region(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate), o_id, paddr_start, paddr_end)
        // Property: If the object is an active OS object, then the object is not in the memory region 
        // [paddr_start, paddr_end), which is inside a wimp driver's DO
{
    reveal WK_ValidObjsAddrs();

    var globals := wkm_get_globals(s.wk_mstate);
    var wimpdrv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
    var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);

    forall o_id | WSM_IsObjID(s.objects, o_id) && o_id != wimpdrv_do_id.oid &&
                 WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, o_id) &&
                 WSM_IsUSBTDMappedObj(s.objects, o_id)
        ensures obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end)
    {
        assert WK_ValidObjsAddrs_Separation(s.objects, s.objs_addrs, globals);
        assert WK_ValidObjAddrs_WimpDrv_DOPAddrs(s.subjects, s.objects, s.id_mappings, s.objs_addrs, globals);

        var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot);
        var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot);
        assert is_mem_region_inside(do_paddr_base, do_paddr_end, paddr_start, paddr_end);

        if(TD_ID(o_id) in s.objects.usbtd_tds)
        {
            forall pmem1 | pmem1 in s.objs_addrs.tds_addrs[TD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForTD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else if(FD_ID(o_id) in s.objects.usbtd_fds)
        {
            forall pmem1 | pmem1 in s.objs_addrs.fds_addrs[FD_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForFD(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
        else
        {
            assert DO_ID(o_id) in s.objects.usbtd_dos;

            forall pmem1 | pmem1 in s.objs_addrs.dos_addrs[DO_ID(o_id)].paddrs
                ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, paddr_start, paddr_end)
            {
                assert forall pmem2 :: pmem2 in s.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
                        ==> !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end);

                Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_ApplyToAWimpDrv(s, wimpdrv_slot);
                assert !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end);

                Lemma_is_mem_region_overlap_ProveNotOverlappingWithIncludedMemRegion(
                    pmem1.paddr_start, pmem1.paddr_end, do_paddr_base, do_paddr_end, paddr_start, paddr_end);
            }

            Lemma_obj_exclude_pmem_region_Prove_ForDO(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
            assert obj_exclude_pmem_region(s.objects, s.objs_addrs, globals, o_id, paddr_start, paddr_end);
        }
    }
}