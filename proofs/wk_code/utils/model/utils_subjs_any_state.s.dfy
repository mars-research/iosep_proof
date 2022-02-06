//include "../../state_properties_validity.s.dfy"
include "../../state.dfy"
include "utils_ids_any_state.s.dfy"

/*********************** Util Functions and Predicates - General Subjects ********************/
function method WSM_OwnedTDs(subjs:WSM_Subjects, s_id:Subject_ID) : set<TD_ID>
    requires WSM_IsSubjID(subjs, s_id)
{
    if(Drv_ID(s_id) in subjs.wimp_drvs) then
        {}
    else if (Drv_ID(s_id) in subjs.os_drvs) then
        subjs.os_drvs[Drv_ID(s_id)].td_ids
    else if (Dev_ID(s_id) in subjs.eehcis) then
        subjs.eehcis[Dev_ID(s_id)].td_ids
    else if (Dev_ID(s_id) in subjs.usbpdevs) then
        {subjs.usbpdevs[Dev_ID(s_id)].hcoded_td_id}
    else
        assert Dev_ID(s_id) in subjs.os_devs;
        (subjs.os_devs[Dev_ID(s_id)].td_ids)
}

function method WSM_OwnedFDs(subjs:WSM_Subjects, s_id:Subject_ID) : set<FD_ID>
    requires WSM_IsSubjID(subjs, s_id)
{
    if(Drv_ID(s_id) in subjs.wimp_drvs) then
        {}
    else if (Drv_ID(s_id) in subjs.os_drvs) then
        subjs.os_drvs[Drv_ID(s_id)].fd_ids
    else if (Dev_ID(s_id) in subjs.eehcis) then
        subjs.eehcis[Dev_ID(s_id)].fd_ids
    else if (Dev_ID(s_id) in subjs.usbpdevs) then
        OwnedFDs_USBPDev(subjs, Dev_ID(s_id))
    else
        assert Dev_ID(s_id) in subjs.os_devs;
        (subjs.os_devs[Dev_ID(s_id)].fd_ids)
}

function method WSM_OwnedDOs(subjs:WSM_Subjects, s_id:Subject_ID) : set<DO_ID>
    requires WSM_IsSubjID(subjs, s_id)
{
    if(Drv_ID(s_id) in subjs.wimp_drvs) then
        OwnedDOs_WimpDrv(subjs, Drv_ID(s_id))
    else if (Drv_ID(s_id) in subjs.os_drvs) then
        subjs.os_drvs[Drv_ID(s_id)].do_ids
    else if (Dev_ID(s_id) in subjs.eehcis) then
        subjs.eehcis[Dev_ID(s_id)].do_ids
    else if (Dev_ID(s_id) in subjs.usbpdevs) then
        OwnedDOs_USBPDev(subjs, Dev_ID(s_id))
    else
        assert Dev_ID(s_id) in subjs.os_devs;
        (subjs.os_devs[Dev_ID(s_id)].do_ids)
}

// Does the subject (id == <s_id> own the object (id == <o_id>)
function method WSM_DoOwnObj(subjs:WSM_Subjects, s_id:Subject_ID, o_id:Object_ID) : bool
    requires WSM_IsSubjID(subjs, s_id)
{
    TD_ID(o_id) in WSM_OwnedTDs(subjs, s_id) ||
    FD_ID(o_id) in WSM_OwnedFDs(subjs, s_id) ||
    DO_ID(o_id) in WSM_OwnedDOs(subjs, s_id)
}

predicate WSM_IsDevID(subjs:WSM_Subjects, dev_id:Dev_ID)
{
    WSM_IsOSDevID(subjs, dev_id) || WSM_IsUSBPDevID(subjs, dev_id) || WSM_IsEEHCIDevID(subjs, dev_id)
}




/*********************** Util Functions and Predicates - WimpDrv ********************/
// Predicate: Is the given <drv_id> in <subjs.wimp_drvs>
predicate WSM_IsWimpDrvID(subjs:WSM_Subjects, drv_id:Drv_ID)
{
    drv_id in subjs.wimp_drvs
}

function method OwnedDOs_WimpDrv(subjs:WSM_Subjects, drv_id:Drv_ID) : (result:set<DO_ID>)
    requires WSM_IsWimpDrvID(subjs, drv_id)
{
    {subjs.wimp_drvs[drv_id].do_id}
}




/*********************** Util Functions and Predicates - USBPDev ********************/
// Predicate: Is the given <dev_id> in <subjs.usbpdevs>
predicate WSM_IsUSBPDevID(subjs:WSM_Subjects, dev_id:Dev_ID)
{
    dev_id in subjs.usbpdevs
}

function method WSM_USBPDevRead_ReplaceSrcFDWithVal(
    s:state, fds_dst_src:map<FD_ID, FD_ID>
) : (fd_id_val_map:map<FD_ID, FD_Val>)
    requires forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in s.objects.usbpdev_fds && fds_dst_src[fd_id] in s.objects.usbpdev_fds

    ensures MapGetKeys(fd_id_val_map) == MapGetKeys(fds_dst_src)
    ensures forall fd_id :: fd_id in fd_id_val_map
                ==> fd_id_val_map[fd_id] == s.objects.usbpdev_fds[fds_dst_src[fd_id]]

    /* ensures WSM_DrvDevRead_ReplaceSrcFDWithVal(ws, fds_dst_src) == DM_DrvDevRead_ReplaceSrcFDWithVal(DMStateToState(ws), fds_dst_src) */
{
    map fd_id | fd_id in fds_dst_src :: s.objects.usbpdev_fds[fds_dst_src[fd_id]]
}

function method WSM_USBPDevRead_ReplaceSrcDOWithVal(
    s:state, dos_dst_src:map<DO_ID, DO_ID>
) : (do_id_val_map:map<DO_ID, DO_Val>)
    requires forall do_id :: do_id in dos_dst_src
                ==> do_id in s.objects.usbpdev_dos && dos_dst_src[do_id] in s.objects.usbpdev_dos

    ensures MapGetKeys(do_id_val_map) == MapGetKeys(dos_dst_src)
    ensures forall do_id :: do_id in do_id_val_map
                ==> do_id_val_map[do_id] == s.objects.usbpdev_dos[dos_dst_src[do_id]]

    /* ensures WSM_DrvDevRead_ReplaceSrcDOWithVal(ws, dos_dst_src) == DM_DrvDevRead_ReplaceSrcDOWithVal(DMStateToState(ws), dos_dst_src) */
{
    map do_id | do_id in dos_dst_src :: s.objects.usbpdev_dos[dos_dst_src[do_id]]
}

function method OwnedFDs_USBPDev(subjs:WSM_Subjects, dev_id:Dev_ID) : (result:set<FD_ID>)
    requires WSM_IsUSBPDevID(subjs, dev_id)
{
    subjs.usbpdevs[dev_id].fd_ids
}

function method OwnedDOs_USBPDev(subjs:WSM_Subjects, dev_id:Dev_ID) : (result:set<DO_ID>)
    requires WSM_IsUSBPDevID(subjs, dev_id)
{
    subjs.usbpdevs[dev_id].do_ids
}




/*********************** Util Functions and Predicates - eEHCI/pEHCI ********************/
// Return IDs of all physical EHCIs
// [NOTE] <s.activate_conds.ehci_activate_cond> stores the IDs of all physical EHCIs. In THIS WK implementation, wimp 
// drivers only have access to eEHCIs, but not pEHCIs. Even if a pEHCI is not multiplexed, a wimp driver gets access to 
// an eEHCI mapped to the pEHCI.
function WSM_AllDevIDs_pEHCIs(subjs:WSM_Subjects, activate_conds:WSM_Dev_Activate_Conditions) : (result:set<Dev_ID>)
    requires forall dev_id :: dev_id in activate_conds.ehci_activate_cond
                ==> dev_id in subjs.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>

    ensures forall id :: id in result
                ==> id in subjs.os_devs
{
    MapGetKeys(activate_conds.ehci_activate_cond)
}

// Predicate: Is the given <drv_id> in <subjs.wimp_drvs>
predicate WSM_IsEEHCIDevID(subjs:WSM_Subjects, dev_id:Dev_ID)
{
    dev_id in subjs.eehcis
}

function method WSM_HCodedTDsOwnedByOSDevs(s:state, dev_ids:set<Dev_ID>) : (result:set<TD_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && s.subjects.os_devs[dev_id].hcoded_td_id == id)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].hcoded_td_id in result
{
    set dev_id | dev_id in dev_ids :: s.subjects.os_devs[dev_id].hcoded_td_id
}


function method WSM_TDsOwnedByOSDevs(s:state, dev_ids:set<Dev_ID>) : (result:set<TD_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in s.subjects.os_devs[dev_id].td_ids)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].td_ids <= result
{
    var set1 := set dev_id, td_id | dev_id in dev_ids &&
                        td_id in s.subjects.os_devs[dev_id].td_ids 
                    :: td_id ;

    Lemma_WSM_TDsOwnedByOSDevs_Prove(s, dev_ids, set1);

    set1
}

function method WSM_FDsOwnedByOSDevs(s:state, dev_ids:set<Dev_ID>) : (result:set<FD_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in s.subjects.os_devs[dev_id].fd_ids)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].fd_ids <= result
{
    var set1 := set dev_id, fd_id | dev_id in dev_ids &&
                        fd_id in s.subjects.os_devs[dev_id].fd_ids 
                    :: fd_id ;

    Lemma_WSM_FDsOwnedByOSDevs_Prove(s, dev_ids, set1);

    set1
}

function method WSM_DOsOwnedByOSDevs(s:state, dev_ids:set<Dev_ID>) : (result:set<DO_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs

    ensures forall id :: id in result
                ==> (exists dev_id :: dev_id in dev_ids && id in s.subjects.os_devs[dev_id].do_ids)
    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].do_ids <= result
{
    var set1 := set dev_id, do_id | dev_id in dev_ids &&
                        do_id in s.subjects.os_devs[dev_id].do_ids 
                    :: do_id ;

    Lemma_WSM_DOsOwnedByOSDevs_Prove(s, dev_ids, set1);

    set1
}

/*function method OwnedTDs_eEHCI(subjs:WSM_Subjects, dev_id:Dev_ID) : (result:set<TD_ID>)
    requires WK_ValidSubjs_eEHCIs(subjs)
    requires WSM_IsEEHCIDevID(subjs, dev_id)

    ensures result == subjs.eehcis[dev_id].td_ids
{
    reveal WK_ValidSubjs_eEHCIs();
    
    OwnedTDs_eEHCI_ExcludeHCodedTD(subjs, dev_id) + {subjs.eehcis[dev_id].hcoded_td_id}
}*/

function method OwnedTDs_eEHCI_ExcludeHCodedTD(subjs:WSM_Subjects, dev_id:Dev_ID) : (result:set<TD_ID>)
    requires WSM_IsEEHCIDevID(subjs, dev_id)

    ensures forall e :: e in result 
                ==> (exists k :: k in subjs.eehcis[dev_id].map_td_ids && subjs.eehcis[dev_id].map_td_ids[k] == e)
    ensures forall k :: k in subjs.eehcis[dev_id].map_td_ids
                ==> subjs.eehcis[dev_id].map_td_ids[k] in result
{
    set k | k in subjs.eehcis[dev_id].map_td_ids :: subjs.eehcis[dev_id].map_td_ids[k]
}

function method OwnedFDs_eEHCI(subjs:WSM_Subjects, dev_id:Dev_ID) : (result:set<FD_ID>)
    requires WSM_IsEEHCIDevID(subjs, dev_id)

    ensures forall e :: e in result 
                ==> (exists k :: k in subjs.eehcis[dev_id].map_fd_ids && subjs.eehcis[dev_id].map_fd_ids[k] == e)
    ensures forall k :: k in subjs.eehcis[dev_id].map_fd_ids
                ==> subjs.eehcis[dev_id].map_fd_ids[k] in result
{
    set k | k in subjs.eehcis[dev_id].map_fd_ids :: subjs.eehcis[dev_id].map_fd_ids[k]
}

function method OwnedDOs_eEHCI(subjs:WSM_Subjects, dev_id:Dev_ID) : (result:set<DO_ID>)
    requires WSM_IsEEHCIDevID(subjs, dev_id)

    ensures forall e :: e in result 
                ==> (exists k :: k in subjs.eehcis[dev_id].map_do_ids && subjs.eehcis[dev_id].map_do_ids[k] == e)
    ensures forall k :: k in subjs.eehcis[dev_id].map_do_ids
                ==> subjs.eehcis[dev_id].map_do_ids[k] in result
{
    set k | k in subjs.eehcis[dev_id].map_do_ids :: subjs.eehcis[dev_id].map_do_ids[k]
}




/*********************** Util Functions and Predicates - OS ********************/
// Predicate: Is the given <drv_id> in <subjs.os_drvs>
predicate WSM_IsOSDrvID(subjs:WSM_Subjects, drv_id:Drv_ID)
{
    drv_id in subjs.os_drvs
}

// Predicate: Is the given <drv_id> in <subjs.os_devs>
predicate WSM_IsOSDevID(subjs:WSM_Subjects, dev_id:Dev_ID)
{
    dev_id in subjs.os_devs
}

function SubjPID_OSDrv(subjs:WSM_Subjects, id:Drv_ID) : WS_PartitionID
    requires id in subjs.os_drvs
{
    subjs.os_drvs[id].pid
}

function SubjPID_OSDev(subjs:WSM_Subjects, id:Dev_ID) : WS_PartitionID
    requires id in subjs.os_devs
{
    subjs.os_devs[id].pid
}

function method WSM_OSSetDrvsPIDs(
    os_drvs:map<Drv_ID, OS_Drv>, drv_ids_to_modify:set<Drv_ID>, new_pid:WS_PartitionID
) : (result:map<Drv_ID, OS_Drv>)
    requires forall id:: id in drv_ids_to_modify ==> id in os_drvs

    ensures forall id :: id in os_drvs <==> id in result
    ensures MapGetKeys(result) == MapGetKeys(os_drvs)
    ensures forall id :: id in os_drvs
                ==> (id in drv_ids_to_modify ==> (result[id].pid == new_pid && result[id].td_ids == os_drvs[id].td_ids &&
                            result[id].fd_ids == os_drvs[id].fd_ids && result[id].do_ids == os_drvs[id].do_ids)) &&
                    (id !in drv_ids_to_modify ==> result[id] == os_drvs[id])
        // Property: In <result>, all PIDs of <drv_ids_to_modify> are modified
{
    map id | id in os_drvs 
            :: if id !in drv_ids_to_modify then os_drvs[id] else OS_Drv(new_pid, os_drvs[id].td_ids, os_drvs[id].fd_ids, os_drvs[id].do_ids)
}

function method WSM_OSSetDevsPIDs(
    os_devs:map<Dev_ID, OS_Dev>, dev_ids_to_modify:set<Dev_ID>, new_pid:WS_PartitionID
) : (result:map<Dev_ID, OS_Dev>)
    requires forall id:: id in dev_ids_to_modify ==> id in os_devs

    ensures forall id :: id in os_devs <==> id in result
    ensures MapGetKeys(result) == MapGetKeys(os_devs)
    ensures forall id :: id in os_devs
                ==> (id in dev_ids_to_modify ==> (result[id].pid == new_pid && 
                            result[id].hcoded_td_id == os_devs[id].hcoded_td_id && result[id].td_ids == os_devs[id].td_ids &&
                            result[id].fd_ids == os_devs[id].fd_ids && result[id].do_ids == os_devs[id].do_ids)) &&
                    (id !in dev_ids_to_modify ==> result[id] == os_devs[id])
        // Property: In <result>, all PIDs of <dev_ids_to_modify> are modified
{
    map id | id in os_devs 
            :: if id !in dev_ids_to_modify then os_devs[id] else OS_Dev(new_pid, os_devs[id].hcoded_td_id, os_devs[id].td_ids, os_devs[id].fd_ids, os_devs[id].do_ids)
}




/*********************** Private Lemmas ********************/
lemma Lemma_WSM_TDsOwnedByOSDevs_Prove(s:state, dev_ids:set<Dev_ID>, result:set<TD_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs
    requires result == (set dev_id, td_id | dev_id in dev_ids &&
                        td_id in s.subjects.os_devs[dev_id].td_ids 
                    :: td_id)

    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].td_ids <= result
{
    forall dev_id | dev_id in dev_ids 
        ensures s.subjects.os_devs[dev_id].td_ids <= result
    {
        assert forall td_id :: td_id in s.subjects.os_devs[dev_id].td_ids 
                ==> td_id in result;
    }
}

lemma Lemma_WSM_FDsOwnedByOSDevs_Prove(s:state, dev_ids:set<Dev_ID>, result:set<FD_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs
    requires result == (set dev_id, fd_id | dev_id in dev_ids &&
                        fd_id in s.subjects.os_devs[dev_id].fd_ids 
                    :: fd_id)

    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].fd_ids <= result
{
    forall dev_id | dev_id in dev_ids 
        ensures s.subjects.os_devs[dev_id].fd_ids <= result
    {
        assert forall fd_id :: fd_id in s.subjects.os_devs[dev_id].fd_ids 
                ==> fd_id in result;
    }
}

lemma Lemma_WSM_DOsOwnedByOSDevs_Prove(s:state, dev_ids:set<Dev_ID>, result:set<DO_ID>)
    requires forall id :: id in dev_ids ==> id in s.subjects.os_devs
    requires result == (set dev_id, do_id | dev_id in dev_ids &&
                        do_id in s.subjects.os_devs[dev_id].do_ids 
                    :: do_id)

    ensures forall dev_id :: dev_id in dev_ids 
                ==> s.subjects.os_devs[dev_id].do_ids <= result
{
    forall dev_id | dev_id in dev_ids 
        ensures s.subjects.os_devs[dev_id].do_ids <= result
    {
        assert forall do_id :: do_id in s.subjects.os_devs[dev_id].do_ids 
                ==> do_id in result;
    }
}