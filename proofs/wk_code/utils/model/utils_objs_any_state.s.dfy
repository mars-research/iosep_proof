include "../../state.dfy"

/*********************** Axioms ********************/
// [State/Ops Mapping] Axiom (well known): Exist a function to map OS TDs to abstract TDs
// [NOTE] <objs> is needed, in order to correctly map strings to TD_Val. This is because the correct TD_Val depends on 
// the current value of objects referenced by this TD
function {:axiom} WSM_MapOSTDVal_ToTDVal(objs:WSM_Objects, val:OS_TD_Val) : TD_Val

// [State/Ops Mapping] Axiom (well known): If a device can issue a write transfer to a memory word, then the word must be represented 
// as a string which is further stored in TD
function {:axiom} DevWrite_WordToString(n:word) : string

// [WimpDrv] Axiom (well known): Exist a function to return the value range of the given wimp driver's DO
function {:axiom} WimpDrv_DO_GetValueRangeOfDO(objs:WSM_Objects, do_id:DO_ID) :set<DO_Val>
    requires WSM_IsWimpDrvDOID(objs, do_id)

// [USB TDs] Axiom (well knwon): Exist a function to return the value range of the given FD mapped to USB TD
function {:axiom} USBTD_MappedFD_GetValueRange(objs:WSM_Objects, fd_id:FD_ID) :set<FD_Val>
    requires fd_id in objs.usbtd_fds

// [USB TDs] Axiom (well knwon): Exist a function to return the value range of the given DO mapped to USB TD
function {:axiom} USBTD_MappedDO_GetValueRange(objs:WSM_Objects, do_id:DO_ID) :set<DO_Val>
    requires do_id in objs.usbtd_dos




/*********************** Utility Functions - General Subjects/Objects ********************/
predicate WSM_IsTDID(objs:WSM_Objects, id:TD_ID)
{
    id in objs.os_tds || id in objs.eehci_hcoded_tds || id in objs.eehci_other_tds || id in objs.usbpdev_tds || id in objs.usbtd_tds
}

predicate WSM_IsFDID(objs:WSM_Objects, id:FD_ID)
{
    id in objs.os_fds || id in objs.eehci_fds || id in objs.usbpdev_fds || id in objs.usbtd_fds 
}

predicate WSM_IsDOID(objs:WSM_Objects, id:DO_ID)
{
    id in objs.os_dos || id in objs.eehci_dos || id in objs.usbpdev_dos || id in objs.wimpdrv_dos || id in objs.usbtd_dos 
}

predicate WSM_IsWimpTDID(objs:WSM_Objects, id:TD_ID)
{
    id in objs.eehci_hcoded_tds || id in objs.eehci_other_tds || id in objs.usbpdev_tds || id in objs.usbtd_tds
}

predicate WSM_IsWimpFDID(objs:WSM_Objects, id:FD_ID)
{
    id in objs.eehci_fds || id in objs.usbpdev_fds || id in objs.usbtd_fds 
}

predicate WSM_IsWimpDOID(objs:WSM_Objects, id:DO_ID)
{
    id in objs.eehci_dos || id in objs.usbpdev_dos || id in objs.wimpdrv_dos || id in objs.usbtd_dos 
}

// Predicate: Is the given object ID belongs to an object
predicate WSM_IsObjID(objs:WSM_Objects, id:Object_ID)
{
    WSM_IsOSObj(objs, id) ||
    WSM_IsEEHCIObj(objs, id) || WSM_IsUSBPDevObj(objs, id) ||
    WSM_IsWimpDrvDO(objs, id) || WSM_IsUSBTDMappedObj(objs, id)
}

function method WSM_AllTDIDs(objs:WSM_Objects) : (result:set<TD_ID>)
    ensures forall id :: id in result
                <==> id in objs.os_tds || id in objs.eehci_hcoded_tds || id in objs.eehci_other_tds || id in objs.usbpdev_tds || id in objs.usbtd_tds
{
    MapGetKeys(objs.os_tds) + MapGetKeys(objs.eehci_hcoded_tds) + objs.eehci_other_tds + MapGetKeys(objs.usbpdev_tds) + objs.usbtd_tds
}

function method WSM_AllFDIDs(objs:WSM_Objects) : (result:set<FD_ID>)
    ensures forall id :: id in result
                <==> id in objs.os_fds || id in objs.eehci_fds || id in objs.usbpdev_fds || id in objs.usbtd_fds
{
    MapGetKeys(objs.os_fds) + objs.eehci_fds + MapGetKeys(objs.usbpdev_fds) + objs.usbtd_fds
}

function method WSM_AllDOIDs(objs:WSM_Objects) : (result:set<DO_ID>)
    ensures forall id :: id in result
                <==> id in objs.os_dos || id in objs.eehci_dos || id in objs.usbpdev_dos || id in objs.wimpdrv_dos || id in objs.usbtd_dos
{
    MapGetKeys(objs.os_dos) + objs.eehci_dos + MapGetKeys(objs.usbpdev_dos) + MapGetKeys(objs.wimpdrv_dos) + objs.usbtd_dos
}

function method WSM_AllObjIDs(objs:WSM_Objects) : (result:set<Object_ID>)
    ensures forall id :: id in result
                ==> TD_ID(id) in WSM_AllTDIDs(objs) || FD_ID(id) in WSM_AllFDIDs(objs) || DO_ID(id) in WSM_AllDOIDs(objs)
{
    (set id:TD_ID | id in WSM_AllTDIDs(objs) :: id.oid) +
    (set id:FD_ID | id in WSM_AllFDIDs(objs) :: id.oid) +
    (set id:DO_ID | id in WSM_AllDOIDs(objs) :: id.oid)
}

function ObjPID_OSObj(objs:WSM_Objects, id:Object_ID) : WS_PartitionID
    requires WSM_IsOSObj(objs, id)
{
    if(TD_ID(id) in objs.os_tds) then
        objs.os_tds[TD_ID(id)].pid
    else if (FD_ID(id) in objs.os_fds) then
        objs.os_fds[FD_ID(id)].pid
    else
        assert DO_ID(id) in objs.os_dos;
        objs.os_dos[DO_ID(id)].pid
}

function method WSM_WriteFDsVals(
    fds:map<FD_ID, FD_Val>, fd_id_val_map:map<FD_ID, FD_Val>
) : map<FD_ID, FD_Val>
    requires forall fd_id:: fd_id in fd_id_val_map ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in WSM_WriteFDsVals(fds, fd_id_val_map)
    ensures MapGetKeys(WSM_WriteFDsVals(fds, fd_id_val_map)) == MapGetKeys(fds)
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in fd_id_val_map ==> WSM_WriteFDsVals(fds, fd_id_val_map)[fd_id] == fd_id_val_map[fd_id]) &&
                    (fd_id !in fd_id_val_map ==> WSM_WriteFDsVals(fds, fd_id_val_map)[fd_id] == fds[fd_id])
        // Property: The values in <fd_id_val_map> is written into result
{
    map fd_id | fd_id in fds 
            :: if fd_id !in fd_id_val_map then fds[fd_id] else fd_id_val_map[fd_id]
}

function method WSM_WriteDOsVals(
    dos:map<DO_ID, DO_Val>, do_id_val_map:map<DO_ID, DO_Val>
) : map<DO_ID, DO_Val>
    requires forall do_id:: do_id in do_id_val_map ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in WSM_WriteDOsVals(dos, do_id_val_map)
    ensures MapGetKeys(WSM_WriteDOsVals(dos, do_id_val_map)) == MapGetKeys(dos)
    ensures forall do_id :: do_id in dos
                ==> (do_id in do_id_val_map ==> WSM_WriteDOsVals(dos, do_id_val_map)[do_id] == do_id_val_map[do_id]) &&
                    (do_id !in do_id_val_map ==> WSM_WriteDOsVals(dos, do_id_val_map)[do_id] == dos[do_id])
        // Property: The values in <do_id_val_map> is written into result
{
    map do_id | do_id in dos 
            :: if do_id !in do_id_val_map then dos[do_id] else do_id_val_map[do_id]
}

function method WSM_IsDOClearVal(dos:map<DO_ID, DO_Val>, do_id:DO_ID) : bool
    requires do_id in dos
{
    dos[do_id] == DO_Val("")
}

function method WSM_IsFDClearVal(fds:map<FD_ID, FD_Val>, fd_id:FD_ID) : bool
    requires fd_id in fds
{
    fds[fd_id] == FD_Val("")
}




/*********************** Utility Functions - OS Objects ********************/
// Predicate: Is the given object an OS object
predicate WSM_IsOSObj(objs:WSM_Objects, id:Object_ID)
{
    TD_ID(id) in objs.os_tds || FD_ID(id) in objs.os_fds || DO_ID(id) in objs.os_dos 
}

predicate WSM_IsOSTDID(objs:WSM_Objects, id:TD_ID)
{
    id in objs.os_tds
}

predicate WSM_IsOSFDID(objs:WSM_Objects, id:FD_ID)
{
    id in objs.os_fds
}

predicate WSM_IsOSDOID(objs:WSM_Objects, id:DO_ID)
{
    id in objs.os_dos
}

function method WSM_SetOSTDsPIDs(
    tds:map<TD_ID, OS_TD_State>, tds_to_modify:set<TD_ID>, new_pid:WS_PartitionID
) : (result:map<TD_ID, OS_TD_State>)
    requires forall td_id:: td_id in tds_to_modify ==> td_id in tds

    ensures forall td_id :: td_id in tds <==> td_id in result
    ensures MapGetKeys(result) == MapGetKeys(tds)
    ensures forall td_id :: td_id in tds
                ==> (td_id in tds_to_modify ==> (result[td_id].pid == new_pid && result[td_id].val == tds[td_id].val)) &&
                    (td_id !in tds_to_modify ==> result[td_id] == tds[td_id])
        // Property: In <result>, all PIDs of <tds_to_modify> are modified
{
    map td_id | td_id in tds 
            :: if td_id !in tds_to_modify then tds[td_id] else OS_TD_State(new_pid, tds[td_id].val)
}

function method WSM_SetOSFDsPIDs(
    fds:map<FD_ID, OS_FD_State>, fds_to_modify:set<FD_ID>, new_pid:WS_PartitionID
) : (result:map<FD_ID, OS_FD_State>)
    requires forall fd_id:: fd_id in fds_to_modify ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in result
    ensures MapGetKeys(result) == MapGetKeys(fds)
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in fds_to_modify ==> (result[fd_id].pid == new_pid && result[fd_id].val == fds[fd_id].val)) &&
                    (fd_id !in fds_to_modify ==> result[fd_id] == fds[fd_id])
        // Property: In <result>, all PIDs of <fds_to_modify> are modified
{
    map fd_id | fd_id in fds 
            :: if fd_id !in fds_to_modify then fds[fd_id] else OS_FD_State(new_pid, fds[fd_id].val)
}

function method WSM_SetOSDOsPIDs(
    dos:map<DO_ID, OS_DO_State>, dos_to_modify:set<DO_ID>, new_pid:WS_PartitionID
) : (result:map<DO_ID, OS_DO_State>)
    requires forall do_id:: do_id in dos_to_modify ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in result
    ensures MapGetKeys(result) == MapGetKeys(dos)
    ensures forall do_id :: do_id in dos
                ==> (do_id in dos_to_modify ==> (result[do_id].pid == new_pid && result[do_id].val == dos[do_id].val)) &&
                    (do_id !in dos_to_modify ==> result[do_id] == dos[do_id])
        // Property: In <result>, all PIDs of <dos_to_modify> are modified
{
    map do_id | do_id in dos 
            :: if do_id !in dos_to_modify then dos[do_id] else OS_DO_State(new_pid, dos[do_id].val)
}

function method WSM_ClearOSTDs(
    tds:map<TD_ID, OS_TD_State>, clear_tds:set<TD_ID>
) : (result:map<TD_ID, OS_TD_State>)
    requires forall td_id:: td_id in clear_tds ==> td_id in tds

    ensures forall td_id :: td_id in tds <==> td_id in result
    ensures forall td_id :: td_id in tds
                ==> (td_id in clear_tds ==> result[td_id].val == OS_TD_Val(map[], map[], map[], map[], map[], map[], map[], map[], map[])) &&
                    (td_id !in clear_tds ==> result[td_id] == tds[td_id])
        // Property: In <result>, all TD IDs in <clear_tds> are map to {}
    ensures forall td_id :: td_id in tds
                ==> tds[td_id].pid == result[td_id].pid
        // Property: WriteTD does not change the pids of any TDs
{
    map td_id | td_id in tds 
            :: if td_id !in clear_tds then tds[td_id] else OS_TD_State(tds[td_id].pid, OS_TD_Val(map[], map[], map[], map[], map[], map[], map[], map[], map[]))
}

function method WSM_ClearOSFDs(
    fds:map<FD_ID, OS_FD_State>, clear_fds:set<FD_ID>
) : (result:map<FD_ID, OS_FD_State>)
    requires forall fd_id:: fd_id in clear_fds ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in result
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in clear_fds ==> result[fd_id].val == FD_Val("")) &&
                    (fd_id !in clear_fds ==> result[fd_id] == fds[fd_id])
        // Property: In <result>, all FD IDs in <clear_fds> are map to {}
    ensures forall fd_id :: fd_id in fds
                ==> fds[fd_id].pid == result[fd_id].pid
        // Property: WriteFD does not change the pids of any FDs
{
    map fd_id | fd_id in fds 
            :: if fd_id !in clear_fds then fds[fd_id] else OS_FD_State(fds[fd_id].pid, FD_Val(""))
}

function method WSM_ClearOSDOs(
    dos:map<DO_ID, OS_DO_State>, clear_dos:set<DO_ID>
) : (result:map<DO_ID, OS_DO_State>)
    requires forall do_id:: do_id in clear_dos ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in result
    ensures forall do_id :: do_id in dos
                ==> (do_id in clear_dos ==> result[do_id].val == DO_Val("")) &&
                    (do_id !in clear_dos ==> result[do_id] == dos[do_id])
        // Property: In <result>, all DO IDs in <clear_dos> are map to {}
    ensures forall do_id :: do_id in dos
                ==> dos[do_id].pid == result[do_id].pid
        // Property: WriteDO does not change the pids of any DOs
{
    map do_id | do_id in dos 
            :: if do_id !in clear_dos then dos[do_id] else OS_DO_State(dos[do_id].pid, DO_Val(""))
}

function method WSM_WriteOSTDsVals(
    tds:map<TD_ID, OS_TD_State>, td_id_val_map:map<TD_ID, OS_TD_Val>
) : (result:map<TD_ID, OS_TD_State>)
    requires forall td_id :: td_id in td_id_val_map ==> td_id in tds

    ensures forall td_id :: td_id in tds <==> td_id in result
    ensures MapGetKeys(result) == MapGetKeys(tds)
    ensures forall td_id :: td_id in tds
                ==> (td_id in td_id_val_map ==> result[td_id].val == td_id_val_map[td_id]) &&
                    (td_id !in td_id_val_map ==> result[td_id] == tds[td_id])
        // Property: The values in <td_id_val_map> is written into result
    ensures forall td_id :: td_id in tds
                ==> tds[td_id].pid == result[td_id].pid
        // Property: WriteTD does not change the pids of any TDs
{
    map td_id | td_id in tds 
            :: if td_id !in td_id_val_map then tds[td_id] else OS_TD_State(tds[td_id].pid, td_id_val_map[td_id])
}

function method WSM_WriteOSFDsVals(
    fds:map<FD_ID, OS_FD_State>, fd_id_val_map:map<FD_ID, FD_Val>
) : (result:map<FD_ID, OS_FD_State>)
    requires forall fd_id :: fd_id in fd_id_val_map ==> fd_id in fds

    ensures forall fd_id :: fd_id in fds <==> fd_id in result
    ensures MapGetKeys(result) == MapGetKeys(fds)
    ensures forall fd_id :: fd_id in fds
                ==> (fd_id in fd_id_val_map ==> result[fd_id].val == fd_id_val_map[fd_id]) &&
                    (fd_id !in fd_id_val_map ==> result[fd_id] == fds[fd_id])
        // Property: The values in <fd_id_val_map> is written into result
    ensures forall fd_id :: fd_id in fds
                ==> fds[fd_id].pid == result[fd_id].pid
        // Property: WriteFD does not change the pids of any FDs
{
    map fd_id | fd_id in fds 
            :: if fd_id !in fd_id_val_map then fds[fd_id] else OS_FD_State(fds[fd_id].pid, fd_id_val_map[fd_id])
}

function method WSM_WriteOSDOsVals(
    dos:map<DO_ID, OS_DO_State>, do_id_val_map:map<DO_ID, DO_Val>
) : (result:map<DO_ID, OS_DO_State>)
    requires forall do_id:: do_id in do_id_val_map ==> do_id in dos

    ensures forall do_id :: do_id in dos <==> do_id in result
    ensures MapGetKeys(result) == MapGetKeys(dos)
    ensures forall do_id :: do_id in dos
                ==> (do_id in do_id_val_map ==> result[do_id].val == do_id_val_map[do_id]) &&
                    (do_id !in do_id_val_map ==> result[do_id] == dos[do_id])
        // Property: The values in <do_id_val_map> is written into result
    ensures forall do_id :: do_id in dos
                ==> dos[do_id].pid == result[do_id].pid
        // Property: WriteDO does not change the pids of any DOs
{
    map do_id | do_id in dos 
            :: if do_id !in do_id_val_map then dos[do_id] else OS_DO_State(dos[do_id].pid, do_id_val_map[do_id])
}




/*********************** Utility Functions - USB TD ********************/
// Predicate: Is the given object mapped by a USB TD
predicate WSM_IsUSBTDMappedObj(objs:WSM_Objects, id:Object_ID)
{
    TD_ID(id) in objs.usbtd_tds || FD_ID(id) in objs.usbtd_fds || DO_ID(id) in objs.usbtd_dos 
}




/*********************** Utility Functions - Wimp DOs ********************/
// Predicate: Is the given object a wimp driver's DO
predicate WSM_IsWimpDrvDO(objs:WSM_Objects, id:Object_ID)
{
    DO_ID(id) in objs.wimpdrv_dos
}

predicate WSM_IsWimpDrvDOID(objs:WSM_Objects, id:DO_ID)
{
    id in objs.wimpdrv_dos
}




/*********************** Utility Functions - eEHCIs' Objects ********************/
// Predicate: Is the given object an eEHCI's object
predicate WSM_IsEEHCIObj(objs:WSM_Objects, id:Object_ID)
{
    TD_ID(id) in objs.eehci_hcoded_tds || TD_ID(id) in objs.eehci_other_tds ||
    FD_ID(id) in objs.eehci_fds || DO_ID(id) in objs.eehci_dos 
}




/*********************** Utility Functions - USBPDevs' Objects ********************/
// Predicate: Is the given object a USBPDev's object
predicate WSM_IsUSBPDevObj(objs:WSM_Objects, id:Object_ID)
{
    TD_ID(id) in objs.usbpdev_tds || FD_ID(id) in objs.usbpdev_fds || DO_ID(id) in objs.usbpdev_dos 
}