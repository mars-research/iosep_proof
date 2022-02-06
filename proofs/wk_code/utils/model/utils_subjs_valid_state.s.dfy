include "../../state_properties_validity_subjs_objs_mstate.s.dfy"
include "../../proof/state_map_any_state.s.dfy"

/*********************** Util Functions and Predicates - General Subjects ********************/
// Function: Return the PID of the given subject
function WSM_SubjPID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Subject_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    
    requires WSM_IsSubjID(subjs, id)
{
    if(Drv_ID(id) in subjs.os_drvs) then
        SubjPID_OSDrv(subjs, Drv_ID(id))
    else if (Dev_ID(id) in subjs.os_devs) then
        SubjPID_OSDev(subjs, Dev_ID(id))
    else if (WSM_IsWimpDrvID(subjs, Drv_ID(id))) then
        SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, Drv_ID(id))
    else if (WSM_IsUSBPDevID(subjs, Dev_ID(id))) then
        SubjPID_USBPDev_ByDevID(subjs, objs, id_mappings, globals, Dev_ID(id))
    else
        assert WSM_IsEEHCIDevID(subjs, Dev_ID(id));
        SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, Dev_ID(id))
}

// Function: Return the PID of the given OS subject
function WSM_OSSubjPID(subjs:WSM_Subjects, id:Subject_ID) : WS_PartitionID
    requires WSM_IsOSSubjID(subjs, id)
{
    if(Drv_ID(id) in subjs.os_drvs) then
        SubjPID_OSDrv(subjs, Drv_ID(id))
    else
        assert Dev_ID(id) in subjs.os_devs;
        SubjPID_OSDev(subjs, Dev_ID(id))
}

// Predicate: Is the given subject is active
predicate WSM_IsActiveSubj(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Subject_ID)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    
    requires WSM_IsSubjID(subjs, id)
{
    WSM_SubjPID(subjs, objs, id_mappings, globals, id) != WS_PartitionID(PID_INVALID)
}




/*********************** Util Functions and Predicates - OS ********************/
lemma Lemma_OSObjs_ExternalObjs_ExcludeOSDevObjs(subjs:WSM_Subjects, objs:WSM_Objects, os_tds:set<TD_ID>, os_fds:set<FD_ID>, os_dos:set<DO_ID>)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs_ObjIDs(objs)

    requires forall dev_id :: dev_id in subjs.os_devs
                ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids

    requires forall s_id, o_id :: s_id in WSM_AllSubjsIDs(subjs) &&
                    o_id in (TDIDsToObjIDs(os_tds) + FDIDsToObjIDs(os_fds) + DOIDsToObjIDs(os_dos))
                ==> !WSM_DoOwnObj(subjs, s_id, o_id)
        
    ensures forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in os_tds
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
{
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs_ObjIDs();

    forall os_dev_id, id | WSM_IsOSDevID(subjs, os_dev_id) && id in os_tds
        ensures !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
    {
        assert os_dev_id.sid in WSM_AllSubjsIDs(subjs);
        assert id.oid in (TDIDsToObjIDs(os_tds) + FDIDsToObjIDs(os_fds) + DOIDsToObjIDs(os_dos));
    }
}

lemma Lemma_OSObjs_IfSetExcludeOSDevObjs_ThenAlsoExcludeOSHCodedTDs(subjs:WSM_Subjects, os_tds:set<TD_ID>)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires forall dev_id :: dev_id in subjs.os_devs
                ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids

    requires forall os_dev_id, id :: WSM_IsOSDevID(subjs, os_dev_id) && id in os_tds
                ==> !WSM_DoOwnObj(subjs, os_dev_id.sid, id.oid)
        
    ensures forall id :: id in subjs.os_devs
                ==> subjs.os_devs[id].hcoded_td_id !in os_tds
{
    reveal WK_ValidSubjs_SubjIDs();

    forall id | id in subjs.os_devs
        ensures subjs.os_devs[id].hcoded_td_id !in os_tds
    {
        if(subjs.os_devs[id].hcoded_td_id in os_tds)
        {
            assert WSM_DoOwnObj(subjs, id.sid, subjs.os_devs[id].hcoded_td_id.oid);
            assert false;
        }
    }
}




/*********************** Util Functions and Predicates - WimpDrv ********************/
// Predicate: In <g_wimpdrv_info>, exists a slot containing the given <id_word> 
predicate wimpdrv_idword_in_record(globals:globalsmap, id_word:word)
    requires WK_ValidGlobalVars_Decls(globals)
{
    exists slot :: wimpdrv_valid_slot_id(slot) &&
                    wimpdrv_get_id_word(globals, slot) == id_word
}

// Return the unique slot that contains the <id_word> in <g_wimpdrv_info>
function wimpdrv_get_slot_by_idword(globals:globalsmap, id_word:word) : (slot:word)
    requires WK_ValidGlobalState(globals)
    requires wimpdrv_idword_in_record(globals, id_word)
    requires id_word != WimpDrv_ID_RESERVED_EMPTY

    ensures wimpdrv_valid_slot_id(slot)
    ensures p_wimpdrv_slot_idword_unique(globals, slot, id_word)
{
    var v :| wimpdrv_valid_slot_id(v) &&
                    wimpdrv_get_id_word(globals, v) == id_word;

    v
}

// Function: Return the word map to <drv_id> in id_mappings.wimpdrv_ids
function WSM_GetWimpDrvIDWord(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, drv_id:Drv_ID) : word
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsWimpDrvID(subjs, drv_id)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();
    reveal WK_ValidIDMappings();

    var wimpdrv_id_word:word :| wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
        id_mappings.wimpdrv_ids[wimpdrv_id_word] == drv_id;

    wimpdrv_id_word
}

// Return the PID of a wimp driver. 
// If the wimp driver has a record in <g_wimpdrvs_info>, and is currently registered, then return the PID in the record. 
// Otherwise, the driver must be inactive, and hence return WS_PartitionID(PID_INVALID) 
function SubjPID_WimpDrv_ByIDWord(globals:globalsmap, id_word:word) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires id_word != WimpDrv_ID_RESERVED_EMPTY
{
    if(wimpdrv_idword_in_record(globals, id_word)) then
        var drv_slot := wimpdrv_get_slot_by_idword(globals, id_word);

        if(wimpdrv_do_get_flag(globals, drv_slot) == WimpDrv_Slot_UpdateFlag_Complete) then  
                                                // The driver must finish registration
            wimpdrv_get_pid(globals, drv_slot)
        else
            WS_PartitionID(PID_INVALID)
    else
       WS_PartitionID(PID_INVALID)
}

// Return the PID of a wimp driver. 
// If the wimp driver has a record in <g_wimpdrvs_info>, and is currently registered, then return the PID in the record. 
// Otherwise, the driver must be inactive, and hence return WS_PartitionID(PID_INVALID) 
function SubjPID_WimpDrv_ByDrvID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, drv_id:Drv_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsWimpDrvID(subjs, drv_id)
{
    var drv_id_word := WimpDrv_DrvID_ToIDWord(subjs, objs, id_mappings, drv_id);

    SubjPID_WimpDrv_ByIDWord(globals, drv_id_word)
}

// Function: Given a wimpdrv's <drv_id>, get the corrsponding drv_id_word 
function WimpDrv_DrvID_ToIDWord(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, drv_id:Drv_ID) : (result:word)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsWimpDrvID(subjs, drv_id)

    ensures result != WimpDrv_ID_RESERVED_EMPTY
{
    reveal WK_ValidSubjs();
    reveal WK_ValidIDMappings_WimpDrvIDsMustMapToIDWords();
    reveal WK_ValidIDMappings();

    var drv_id_word :| drv_id_word in id_mappings.wimpdrv_ids &&
                        id_mappings.wimpdrv_ids[drv_id_word] == drv_id;

    drv_id_word
}




/*********************** Util Functions and Predicates - eEHCI ********************/
// Predicate: In <g_wimpdrv_info>, exists a slot containing the given <id_word> 
predicate eehci_idword_in_record(globals:globalsmap, id_word:word)
    requires WK_ValidGlobalVars_Decls(globals)
{
    exists slot :: eehci_valid_slot_id(slot) &&
                    eehci_mem_get_eehci_id(globals, slot) == id_word
}

// Return the unique slot that contains the <id_word> in <g_wimpdrv_info>
function eehci_get_slot_by_idword(globals:globalsmap, id_word:word) : (slot:word)
    requires WK_ValidGlobalState(globals)
    requires eehci_idword_in_record(globals, id_word)
    requires id_word != eEHCI_ID_INVALID

    ensures eehci_valid_slot_id(slot)
    ensures p_eehci_slot_idword_unique(globals, slot, id_word)
{
    var v :| eehci_valid_slot_id(v) &&
                    eehci_mem_get_eehci_id(globals, v) == id_word;

    v
}

// Return the PID of an eEHCI. 
// If the eEHCI has a record in <g_eehcis_info>, return the PID in the record. Otherwise, the eEHCI must be inactive, 
// and hence return WS_PartitionID(PID_INVALID) 
function SubjPID_EEHCI_ByIDWord(globals:globalsmap, id_word:word) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires id_word != eEHCI_ID_INVALID
{
    if(eehci_idword_in_record(globals, id_word)) then
        var dev_slot := eehci_get_slot_by_idword(globals, id_word);
        eehci_info_get_pid(globals, dev_slot)
    else
       WS_PartitionID(PID_INVALID)
}

// Return the PID of an eEHCI. 
// If the eEHCI has a record in <g_eehcis_info>, return the PID in the record. Otherwise, the eEHCI must be inactive, 
// and hence return WS_PartitionID(PID_INVALID) 
function SubjPID_EEHCI_ByDevID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, dev_id:Dev_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsEEHCIDevID(subjs, dev_id)
{
    var id_word := EEHCI_DevID_ToIDWord(subjs, objs, id_mappings, dev_id);

    SubjPID_EEHCI_ByIDWord(globals, id_word)
}

// Function: Given a eehci's <dev_id>, get the corrsponding dev_id_word 
function EEHCI_DevID_ToIDWord(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, dev_id:Dev_ID) : (result:word)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsEEHCIDevID(subjs, dev_id)

    ensures result != eEHCI_ID_INVALID
{
    reveal WK_ValidSubjs();
    reveal WK_ValidIDMappings_EEHCIIDsMustMapToIDWords();
    reveal WK_ValidIDMappings();

    var id_word :| id_word in id_mappings.eehci_ids &&
                        id_mappings.eehci_ids[id_word] == dev_id;

    id_word
}




/*********************** Util Functions and Predicates - USBPDev ********************/
// Predicate: In <g_usbpdev_info>, exists a slot containing the given <usbpdev_addr> 
predicate usbpdev_addr_in_record(globals:globalsmap, usbpdev_addr:USBPDev_Addr)
    requires WK_ValidGlobalVars_Decls(globals)
{
    exists slot :: usbpdev_valid_slot_id(slot) &&
                   usbpdev_get_updateflag(globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                        // The USBPDev slot must not be in the middle of address updating
                   usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, slot)) &&
                   usb_parse_usbpdev_addr(usbpdev_get_addr(globals, slot)) == usbpdev_addr
                        // The USBPDev slot must store the expected USBPDev address
}

// Return the unique slot that contains the <usbpdev_addr> in <g_wimpdrv_info>
function usbpdev_get_slot_by_addr(globals:globalsmap, usbpdev_addr:USBPDev_Addr) : (slot:word)
    requires WK_ValidGlobalState(globals)
    requires usbpdev_addr_in_record(globals, usbpdev_addr)

    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             usbpdev_addr != usb_parse_usbpdev_addr(addr)
        // Requirement: The USBPDev slot does not contain the empty address

    ensures usbpdev_valid_slot_id(slot)
    ensures p_usbpdev_slot_addr_unique(globals, slot, usbpdev_addr)
{
    var v :| usbpdev_valid_slot_id(v) &&
             usbpdev_get_updateflag(globals, v) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
             usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, v)) &&
             usb_parse_usbpdev_addr(usbpdev_get_addr(globals, v)) == usbpdev_addr;

    Lemma_usbpdev_get_slot_by_addr_ProveProperties(globals, usbpdev_addr, v);

    v
}

// Return the PID of an USBPDev. 
// If the eEHCI has a record in <g_eehcis_info>, and finishes registration, then return the PID in the record. 
// Otherwise, the USBPDev must be inactive, and hence return WS_PartitionID(PID_INVALID)
// [TODO] Need to rewrite, if we want USB peripheral devices to be more "on-demand"
function SubjPID_USBPDev_ByAddr(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbpdev_addr:USBPDev_Addr) : WS_PartitionID
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidGlobalState(globals)
    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             usbpdev_addr != usb_parse_usbpdev_addr(addr)
        // Requirement: The USBPDev must be located at a non-empty address
{
    var dev_id:Dev_ID := Map_USBPDevAddr_ToDevID(subjs, objs, id_mappings, usbpdev_addr);
    if(WSM_IsUSBPDevID(subjs, dev_id)) then
        if(subjs.usbpdevs[dev_id].active_in_os == true) then
            WS_PartitionID(PID_RESERVED_OS_PARTITION)
        else
            if( usbpdev_addr_in_record(globals, usbpdev_addr) &&
                (
                    var dev_slot := usbpdev_get_slot_by_addr(globals, usbpdev_addr);
                    usbpdev_get_updateflag(globals, dev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
                ) // The USBPDev must finish registration/activation in WK 
            ) then
                var dev_slot := usbpdev_get_slot_by_addr(globals, usbpdev_addr);
                usbpdev_get_pid(globals, dev_slot)
            else
                WS_PartitionID(PID_INVALID)
    else
        WS_PartitionID(PID_INVALID)
}

// Return the PID of an USBPDev. 
// If the eEHCI has a record in <g_eehcis_info>, return the PID in the record. Otherwise, the eEHCI must be inactive, 
// and hence return WS_PartitionID(PID_INVALID)
function SubjPID_USBPDev_ByDevID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, dev_id:Dev_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsUSBPDevID(subjs, dev_id)
{
    var addr := USBPDev_DevID_ToAddr(subjs, objs, id_mappings, dev_id);

    SubjPID_USBPDev_ByAddr(subjs, objs, id_mappings, globals, addr)
}


// Function: Given a USBPDev's <dev_id>, get the corrsponding USBPDev_Addr 
function USBPDev_DevID_ToAddr(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, dev_id:Dev_ID) : (result:USBPDev_Addr)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsUSBPDevID(subjs, dev_id)

    ensures var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             result != usb_parse_usbpdev_addr(addr)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidIDMappings_USBPDevIDsMustMapToAddrs();
    reveal WK_ValidIDMappings();

    var addr :| addr in id_mappings.usbpdev_ids &&
                        id_mappings.usbpdev_ids[addr] == dev_id;

    var addr_raw := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
    assert addr != usb_parse_usbpdev_addr(addr_raw);

    addr
}




/*********************** Private Lemmas ********************/
lemma Lemma_usbpdev_get_slot_by_addr_ProveProperties(globals:globalsmap, usbpdev_addr:USBPDev_Addr, slot:word)
    requires WK_ValidGlobalState(globals)
    requires usbpdev_addr_in_record(globals, usbpdev_addr)

    requires usbpdev_valid_slot_id(slot) &&
             usbpdev_get_updateflag(globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                // The USBPDev slot must not be in the middle of address updating
             usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, slot)) &&
             usb_parse_usbpdev_addr(usbpdev_get_addr(globals, slot)) == usbpdev_addr
        // Requirement: The USBPDev slot contains the given <usbpdev_addr>

    requires var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(addr) &&
             usbpdev_addr != usb_parse_usbpdev_addr(addr)
        // Requirement: The USBPDev slot does not contain the empty address

    ensures p_usbpdev_slot_addr_unique(globals, slot, usbpdev_addr) 
{
    reveal usb_is_usbpdev_addr_valid();

    assert P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals);
    forall i | usbpdev_valid_slot_id(i) && i != slot &&
               usbpdev_get_updateflag(globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                !(usbpdev_get_addr_low(globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
                usbpdev_get_addr_high(globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH) &&
                usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, i))
        ensures usb_parse_usbpdev_addr(usbpdev_get_addr(globals, i)) != usbpdev_addr
    {
        Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr();
        if(usbpdev_get_addr_low(globals, slot) == WimpUSBPDev_ADDR_EMPTY_LOW &&
            usbpdev_get_addr_high(globals, slot) == WimpUSBPDev_ADDR_EMPTY_HIGH)
        {
            var id := usbpdev_get_addr(globals, slot);
            var id_low := WimpUSBPDev_ADDR_EMPTY_LOW;

            Lemma_BitAnd_Return0IfANumberIs0();
            
            assert !usb_is_usbpdev_addr_valid(id);
            assert false;
        }
        assert usb_parse_usbpdev_addr(usbpdev_get_addr(globals, i)) != usb_parse_usbpdev_addr(usbpdev_get_addr(globals, slot));
    }
}