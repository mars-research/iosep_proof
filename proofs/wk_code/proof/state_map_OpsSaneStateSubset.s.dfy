include "state_map_any_state.s.dfy"
include "../state_properties_OpsSaneStateSubset.s.dfy"
include "../dev/usb2/state_mapping/eehci_map.s.dfy"
include "../dev/usb2/state_mapping/usbtd_map.s.dfy"
include "../utils/model/utils_objs_valid_state.s.dfy"
include "../../DetailedModel/utils/Collections.dfy"

function WSM_MapState(s:state) : (dm:DM_State)
    requires OpsSaneStateSubset(s)
{
    var tds_to_all_states := F_WSM_MapState_AlwaysExistTDsToAllStates(s);
    DM_State(
        WSM_MapState_Subjs(s), WSM_MapState_Objs(s), WSM_MapState_PIDs(s),
        WSM_MapState_OSPID(s),
        s.activate_conds.ehci_activate_cond,
        tds_to_all_states
    )
}




/*********************** State Mappings  ********************/
// [State/Ops Mapping] Axiom (well known): There always exists a <tds_to_all_states> to satisfy 
// <K_IsValidState_TDsToAllStates>, and hence satisfy <IsValidState_TDsToAllStates(k)>
function {:axiom} F_WSM_MapState_AlwaysExistTDsToAllStates(s:state) : (tds_to_all_states:map<set<TD_ID>, set<map<TD_ID, TD_Val>>>)
    requires OpsSaneStateSubset(s)
    ensures var k_objs := WSM_MapState_Objs(s);
            K_IsValidState_TDsToAllStates(k_objs, tds_to_all_states)


// [State/Ops Mapping] Axiom (well known): If only temp global variables, counters, registers, and stack are changed, this 
// function returns the same result
lemma {:axiom} Lemma_F_WSM_MapState_AlwaysExistTDsToAllStates_Property(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)
    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)
    ensures F_WSM_MapState_AlwaysExistTDsToAllStates(s1) == F_WSM_MapState_AlwaysExistTDsToAllStates(s2)


predicate K_IsValidState_TDsToAllStates(k_objs:Objects, tds_to_all_states:map<set<TD_ID>, set<map<TD_ID, TD_Val>>>)
{
    // Condition: Exists a map (<tds_to_all_states>) mapping arbitary set of  
    // TDs to all their possbile values
    (forall td_ids :: td_ids in tds_to_all_states <==> td_ids <= AllTDIDs(k_objs)) &&
        // Any subset of TDs in model state are in the tds_to_all_states map
    (forall td_ids, tds_state :: td_ids in tds_to_all_states &&
            tds_state in tds_to_all_states[td_ids]
        ==> TDsStateGetTDIDs(tds_state) == td_ids) &&
    (forall td_ids, tds_state :: td_ids in tds_to_all_states &&
            TDsStateGetTDIDs(tds_state) == td_ids
        ==> tds_state in tds_to_all_states[td_ids])
        // The mapped set comprises all combinations of values of these TDs
}

function WSM_MapState_Subjs(s:state) : (result:Subjects)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
{
    Subjects(
        WSM_MapState_Drvs_ToSubjs(s),
        WSM_MapState_Devs_ToSubjs(s)
    )
}

function WSM_MapState_Objs(s:state) : (result:Objects)
    requires OpsSaneStateSubset(s)
{
    Objects(
        WSM_MapState_TDsToAbstractTDs_PickActiveNonHCodedTDs(s),
        WSM_MapState_FDsToAbstractFDs_PickActiveFDs(s),
        WSM_MapState_DOsToAbstractDOs_PickActiveDOs(s),

        MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickInactiveNonHCodedTDs(s)),
        MapGetKeys(WSM_MapState_FDsToAbstractFDs_PickInactiveFDs(s)),
        MapGetKeys(WSM_MapState_DOsToAbstractDOs_PickInactiveDOs(s)),

        WSM_MapState_TDsToAbstractTDs_PickHCodedTDs(s)
    )
}

function WSM_MapState_PIDs(s:state) : (result:set<Partition_ID>)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s.wk_mstate))
{
    var globals := wkm_get_globals(s.wk_mstate);
    var ws_pids:set<WS_PartitionID> := WK_GetAllPIDs(globals);

    set ws_pid | ws_pid in ws_pids :: WSM_MapWSParititonID_ToAbstractPartitionID(ws_pid)
}

function WSM_MapState_OSPID(s:state) : (result:Partition_ID)
{
    WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(PID_RESERVED_OS_PARTITION))
}




/*********************** State Mappings for Partition ID ********************/
function WSM_MapWSParititonID_ToAbstractPartitionID(pid:WS_PartitionID) : (result:Partition_ID)
    ensures result == NULL || isUInt32(result.pid)
{
    if(pid == WS_PartitionID(PID_INVALID)) then
        NULL
    else
        Partition_ID(pid.v)
}

function WSM_CalcWSParititonID_FromAbstractPartitionID(pid:Partition_ID) : (result:WS_PartitionID)
    requires pid == NULL || isUInt32(pid.pid)
{
    if(pid == NULL) then
        WS_PartitionID(PID_INVALID)
    else
        WS_PartitionID(pid.pid)
}




/*********************** Private Functions and Lemmas - Subjects ********************/
function WSM_MapState_Drvs_ToSubjs(s:state) : (result:map<Drv_ID, Drv_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == WSM_AllDrvIDs(s.subjects)
    ensures forall id :: id in result
                ==> var pid := WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid));
                    (id in s.subjects.wimp_drvs ==>
                        result[id] == Drv_State(pid, {}, {}, {s.subjects.wimp_drvs[id].do_id})) &&
                    (id in s.subjects.os_drvs ==>
                        result[id] == Drv_State(pid, s.subjects.os_drvs[id].td_ids, s.subjects.os_drvs[id].fd_ids, s.subjects.os_drvs[id].do_ids))
{
    var m1 := WSM_MapWimpDrvs_ToAbstractSubjs(s);
    var m2 := WSM_MapOSDrvs_ToAbstractSubjs(s);
    
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    MapConcat(m1, m2)
}

function WSM_MapState_Devs_ToSubjs(s:state) : (result:map<Dev_ID, Dev_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == WSM_AllDevIDs(s.subjects)
    ensures forall id :: id in result
                ==> var pid := WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid));
                    (id in s.subjects.eehcis ==>
                        result[id] == Dev_State(pid, s.subjects.eehcis[id].hcoded_td_id, 
                        s.subjects.eehcis[id].td_ids, s.subjects.eehcis[id].fd_ids, s.subjects.eehcis[id].do_ids)) &&
                    (id in s.subjects.usbpdevs ==>
                        result[id] == Dev_State(pid, s.subjects.usbpdevs[id].hcoded_td_id,
                        {s.subjects.usbpdevs[id].hcoded_td_id}, s.subjects.usbpdevs[id].fd_ids, s.subjects.usbpdevs[id].do_ids)) &&
                    (id in s.subjects.os_devs ==>
                        result[id] == Dev_State(pid, s.subjects.os_devs[id].hcoded_td_id,
                        s.subjects.os_devs[id].td_ids, s.subjects.os_devs[id].fd_ids, s.subjects.os_devs[id].do_ids))
{
    var m1 := WSM_MapEEHCIs_ToAbstractSubjs(s);
    var m2 := WSM_MapUSBPDevices_ToAbstractSubjs(s);
    var m3 := WSM_MapOSDevs_ToAbstractSubjs(s);
    
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    MapConcat(MapConcat(m1, m2), m3)
}

function WSM_MapWimpDrvs_ToAbstractSubjs(s:state) : (result:map<Drv_ID, Drv_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == MapGetKeys(s.subjects.wimp_drvs)
    ensures forall id :: id in s.subjects.wimp_drvs
                ==> result[id] == Drv_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                        {}, {}, {s.subjects.wimp_drvs[id].do_id})
{
    var wimp_drvs := s.subjects.wimp_drvs;
    map id | id in wimp_drvs
            :: Drv_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                {}, {}, {wimp_drvs[id].do_id}
            )
}

function WSM_MapOSDrvs_ToAbstractSubjs(s:state) : (result:map<Drv_ID, Drv_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == MapGetKeys(s.subjects.os_drvs)
    ensures forall id :: id in s.subjects.os_drvs
                ==> result[id] == Drv_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                        s.subjects.os_drvs[id].td_ids, s.subjects.os_drvs[id].fd_ids, s.subjects.os_drvs[id].do_ids)
{
    var os_drvs := s.subjects.os_drvs;
    map id | id in os_drvs
            :: Drv_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                os_drvs[id].td_ids, os_drvs[id].fd_ids, os_drvs[id].do_ids
            )
}

function WSM_MapEEHCIs_ToAbstractSubjs(s:state) : (result:map<Dev_ID, Dev_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == MapGetKeys(s.subjects.eehcis)
    ensures forall id :: id in s.subjects.eehcis
                ==> result[id] == Dev_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                        s.subjects.eehcis[id].hcoded_td_id,
                        s.subjects.eehcis[id].td_ids, s.subjects.eehcis[id].fd_ids, s.subjects.eehcis[id].do_ids)
{
    var eehcis := s.subjects.eehcis;
    map id | id in eehcis
            :: Dev_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                eehcis[id].hcoded_td_id,
                eehcis[id].td_ids, eehcis[id].fd_ids, eehcis[id].do_ids
            )
}

function WSM_MapUSBPDevices_ToAbstractSubjs(s:state) : (result:map<Dev_ID, Dev_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == MapGetKeys(s.subjects.usbpdevs)
    ensures forall id :: id in s.subjects.usbpdevs
                ==> result[id] == Dev_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                        s.subjects.usbpdevs[id].hcoded_td_id,
                        {s.subjects.usbpdevs[id].hcoded_td_id}, s.subjects.usbpdevs[id].fd_ids, s.subjects.usbpdevs[id].do_ids)
{
    var usbpdevs := s.subjects.usbpdevs;
    map id | id in usbpdevs
            :: Dev_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                usbpdevs[id].hcoded_td_id,
                {s.subjects.usbpdevs[id].hcoded_td_id}, usbpdevs[id].fd_ids, usbpdevs[id].do_ids
            )
}

function WSM_MapOSDevs_ToAbstractSubjs(s:state) : (result:map<Dev_ID, Dev_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures MapGetKeys(result) == MapGetKeys(s.subjects.os_devs)
    ensures forall id :: id in s.subjects.os_devs
                ==> result[id] == Dev_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                        s.subjects.os_devs[id].hcoded_td_id,
                        s.subjects.os_devs[id].td_ids, s.subjects.os_devs[id].fd_ids, s.subjects.os_devs[id].do_ids)
{
    var os_devs := s.subjects.os_devs;
    map id | id in os_devs
            :: Dev_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.sid)),
                os_devs[id].hcoded_td_id,
                s.subjects.os_devs[id].td_ids, os_devs[id].fd_ids, os_devs[id].do_ids
            )
}




/*********************** Private Functions and Lemmas - TDs ********************/
function WSM_MapState_TDsToAbstractTDs_PickActiveNonHCodedTDs(s:state) : (result:map<TD_ID, TD_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in result
                ==> id in WSM_AllTDIDs(s.objects) && id !in WSM_AllHCodedTDIDs(s.subjects)
        // Property: Returned TDs cannot be hardcoded TDs (HTDs)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result
                ==> WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        // Property: Returned TDs must be active
    ensures var all_tds := WSM_MapState_GatherAllAbstractTDs(s);
            forall id :: id in result
                ==> result[id] == all_tds[id]
{
    Lemma_WSM_AllHCodedTDIDs_Properties(s);
    var globals := wkm_get_globals(s.wk_mstate);
    var hcoded_td_ids := WSM_AllHCodedTDIDs(s.subjects);
    var all_tds := WSM_MapState_GatherAllAbstractTDs(s);

    map e | e in all_tds && e !in hcoded_td_ids && 
            WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, e.oid)
        :: all_tds[e]
}

function WSM_MapState_TDsToAbstractTDs_PickInactiveNonHCodedTDs(s:state) : (result:map<TD_ID, TD_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in result
                ==> id in WSM_AllTDIDs(s.objects) && id !in WSM_AllHCodedTDIDs(s.subjects)
        // Property: Returned TDs cannot be hardcoded TDs (HTDs)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result
                ==> !WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        // Property: Returned TDs must be inactive
    ensures var all_tds := WSM_MapState_GatherAllAbstractTDs(s);
            forall id :: id in result
                ==> result[id] == all_tds[id]
{
    Lemma_WSM_AllHCodedTDIDs_Properties(s);
    var globals := wkm_get_globals(s.wk_mstate);
    var hcoded_td_ids := WSM_AllHCodedTDIDs(s.subjects);
    var all_tds := WSM_MapState_GatherAllAbstractTDs(s);

    map e | e in all_tds && e !in hcoded_td_ids && 
            !WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, e.oid)
        :: all_tds[e]
}

function WSM_MapState_TDsToAbstractTDs_PickHCodedTDs(s:state) : (hcoded_tds:map<TD_ID, TD_State>)
    requires OpsSaneStateSubset(s)

    ensures WSM_AllHCodedTDIDs(s.subjects) <= WSM_AllTDIDs(s.objects)
    ensures MapGetKeys(hcoded_tds) == WSM_AllHCodedTDIDs(s.subjects)
    ensures var all_tds := WSM_MapState_GatherAllAbstractTDs(s);
            forall id :: id in hcoded_tds
                ==> hcoded_tds[id] == all_tds[id]
{
    Lemma_WSM_AllHCodedTDIDs_Properties(s);
    var hcoded_td_ids := WSM_AllHCodedTDIDs(s.subjects);
    var all_tds := WSM_MapState_GatherAllAbstractTDs(s);

    map e | e in hcoded_td_ids :: all_tds[e]
}

// Function: Merge all TD mappings into a single map
function WSM_MapState_GatherAllAbstractTDs(s:state) : (result:map<TD_ID, TD_State>)
    requires OpsSaneStateSubset(s)

    ensures MapGetKeys(result) == WSM_AllTDIDs(s.objects)
    ensures forall id :: id in result
                ==> var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                    (id in s.objects.os_tds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_MapOSTDVal_ToTDVal(s.objects, s.objects.os_tds[id].val)) &&
                    (id in s.objects.eehci_hcoded_tds ==>
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.eehci_hcoded_tds[id]) &&
                    (id in s.objects.eehci_other_tds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_eEHCI_USBTDRegVal_ToTDVal(s, WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s, id).2)) &&
                    (id in s.objects.usbpdev_tds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.usbpdev_tds[id]) &&
                    (id in s.objects.usbtd_tds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_USBTD_CalcTDVal(s, id))
{
    var result1 := WSM_MapStateToAbstractTDs_ForOSTDs(s);
    var result2 := WSM_MapStateToAbstractTDs_ForEEHCIHCodedTDs(s);
    var result3 := WSM_MapStateToAbstractTDs_ForEEHCIOtherTDs(s);

    var result4 := WSM_MapStateToAbstractTDs_ForUSBPDev(s);
    var result5 := WSM_MapStateToAbstractTDs_ForUSBTDs(s);

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    var m1 := MapConcat(MapConcat(result1, result2), MapConcat(result3, result4));
    
    MapConcat(m1, result5)
}

function WSM_MapStateToAbstractTDs_ForOSTDs(s:state) : (k_objects_tds:(map<TD_ID, TD_State>))
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures forall id :: id in s.objects.os_tds <==> id in k_objects_tds
    ensures forall id :: id in s.objects.os_tds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_tds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
    ensures forall id :: id in s.objects.os_tds
                ==> k_objects_tds[id].val == WSM_MapOSTDVal_ToTDVal(s.objects, s.objects.os_tds[id].val)
{
    var os_tds := s.objects.os_tds;

    map id | id in os_tds
            :: 
            TD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_MapOSTDVal_ToTDVal(s.objects, s.objects.os_tds[id].val)
            )
}

function WSM_MapStateToAbstractTDs_ForUSBTDs(s:state) : (k_objects_tds:map<TD_ID, TD_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in s.objects.usbtd_tds <==> id in k_objects_tds
    ensures forall id :: id in s.objects.usbtd_tds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_tds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
        // Property: PIDs are mapped correctly
    ensures forall id :: id in s.objects.usbtd_tds
                ==> k_objects_tds[id].val == WSM_USBTD_CalcTDVal(s, id)
        // Property: TD values are mapped correctly
{
    var usbtd_tds:set<TD_ID> := s.objects.usbtd_tds;

    map id | id in usbtd_tds
            :: 
            TD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_USBTD_CalcTDVal(s, id)
            )
}

function WSM_MapStateToAbstractTDs_ForEEHCIHCodedTDs(s:state) : (k_objects_tds:map<TD_ID, TD_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures forall id :: id in s.objects.eehci_hcoded_tds <==> id in k_objects_tds
    ensures forall id :: id in s.objects.eehci_hcoded_tds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_tds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
    ensures forall id :: id in s.objects.eehci_hcoded_tds
                ==> s.objects.eehci_hcoded_tds[id] == k_objects_tds[id].val
{
    var eehci_hcoded_tds := s.objects.eehci_hcoded_tds;

    map id | id in eehci_hcoded_tds
            :: 
            TD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                eehci_hcoded_tds[id]
            )
}

function WSM_MapStateToAbstractTDs_ForEEHCIOtherTDs(s:state) : (k_objects_tds:map<TD_ID, TD_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_SecureMState(s.wk_mstate)

    ensures forall id :: id in s.objects.eehci_other_tds <==> id in k_objects_tds
    ensures forall id :: id in s.objects.eehci_other_tds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_tds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
        // Property: PIDs are mapped correctly
    ensures forall id :: id in s.objects.eehci_other_tds
                ==> k_objects_tds[id].val == WSM_eEHCI_USBTDRegVal_ToTDVal(s, WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s, id).2)
        // Property: TD values are mapped correctly
{
    var eehci_other_tds:set<TD_ID> := s.objects.eehci_other_tds;

    map id | id in eehci_other_tds
            :: 
            TD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_eEHCI_USBTDRegVal_ToTDVal(
                    s, WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s, id).2
                )
            )
}

function WSM_MapStateToAbstractTDs_ForUSBPDev(s:state) : (k_objects_tds:map<TD_ID, TD_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures forall id :: id in s.objects.usbpdev_tds <==> id in k_objects_tds
    ensures forall id :: id in s.objects.usbpdev_tds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_tds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
    ensures forall id :: id in s.objects.usbpdev_tds
                ==> s.objects.usbpdev_tds[id] == k_objects_tds[id].val
{
    var usbpdev_tds := s.objects.usbpdev_tds;

    map id | id in usbpdev_tds
            :: 
            TD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                usbpdev_tds[id]
            )
}

// Function: Given the value <usbtd_reg_val> stored in a usbtd_reg of an eEHCI, Returns the corresponding TD_Val
function WSM_eEHCI_USBTDRegVal_ToTDVal(s:state, usbtd_reg_val:word) : TD_Val
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires usbtd_reg_val == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(usbtd_reg_val)
        // Requirement: Due to <WK_EEHCI_Mem_SecureGlobalVarValues>, the <usbtd_reg_val> must be an allowed USBTD slot ID
    requires usbtd_map_valid_slot_id(usbtd_reg_val)
                ==> usbtd_map_get_idword(wkm_get_globals(s.wk_mstate), usbtd_reg_val) != USBTD_ID_INVALID
        // Requirement: Due to <WK_EEHCI_Mem_SecureGlobalVarValues>, the <usbtd_reg_val> must not point to a USB TD with
        // idword equals to USBTD_ID_INVALID
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();

    var globals := wkm_get_globals(s.wk_mstate);

    if(usbtd_reg_val == USBTD_SlotID_INVALID) then
        TD_Val(map[], map[], map[])
    else
        assert usbtd_map_valid_slot_id(usbtd_reg_val);
        var usbtd_idword := usbtd_map_get_idword(globals, usbtd_reg_val);
        assert usbtd_idword != USBTD_ID_INVALID;

        var usbtd_mapped_tdid:TD_ID := s.id_mappings.usbtd_to_td[usbtd_idword];
        var result_trans_params_tds:map<TD_ID, TD_Trans_Param> := map[usbtd_mapped_tdid := TD_Trans_Param({R}, {})];
        TD_Val(result_trans_params_tds, map[], map[])
}

// Function: Given a TD_ID in <s.objects.eehci_other_tds>, return the value stored in the corresponding usbtd_reg
// Return: (eehci_idword:word, usbtd_reg_id:uint32, usbtd_reg_val:word)
function WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s:state, eehci_other_td_id:TD_ID) : (result:(word, uint32, word))
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_SecureMState(s.wk_mstate)

    requires eehci_other_td_id in s.objects.eehci_other_tds

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword:word := result.0;
            var usbtd_reg_id:uint32 := result.1;
            var usbtd_reg_val:word := result.2;
            eehci_idword_in_record(globals, eehci_idword)
                ==> (eehci_idword != eEHCI_ID_INVALID && 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
                     usbtd_reg_val == eehci_mem_get_usbtd_reg(globals, eehci_get_slot_by_idword(globals, eehci_idword), usbtd_reg_id)
                )
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var eehci_idword:word := result.0;
            var usbtd_reg_id:uint32 := result.1;
            var usbtd_reg_val:word := result.2;
            !eehci_idword_in_record(globals, eehci_idword)
                ==> usbtd_reg_val == USBTD_SlotID_INVALID
        // Property : If the eEHCI is in <g_eehci_mem_info>, then use the <usbtd_reg> there. Otherwise, the result must  
        // be USBTD_SlotID_INVALID, because the eEHCI has never been used by any wimp drivers yet
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_reg_val:word := result.2;
            usbtd_map_valid_slot_id(usbtd_reg_val)
                ==> usbtd_map_get_idword(wkm_get_globals(s.wk_mstate), usbtd_reg_val) != USBTD_ID_INVALID
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();

    var globals := wkm_get_globals(s.wk_mstate);

    // Find the <eehci_dev_id> that owns the <eehci_other_td_id>
    var eehci_dev_id:Dev_ID :| eehci_dev_id in s.subjects.eehcis &&
                        eehci_other_td_id in OwnedTDs_eEHCI_ExcludeHCodedTD(s.subjects, eehci_dev_id);
    assert eehci_other_td_id in s.subjects.eehcis[eehci_dev_id].td_ids;
    assert eehci_other_td_id != s.subjects.eehcis[eehci_dev_id].hcoded_td_id;

    // Find the <usbtd_reg> that maps to the <eehci_other_td_id>
    assert exists k :: k in s.subjects.eehcis[eehci_dev_id].map_td_ids &&
                        s.subjects.eehcis[eehci_dev_id].map_td_ids[k] == eehci_other_td_id;
    var usbtd_reg_offset:uint32 :| usbtd_reg_offset in s.subjects.eehcis[eehci_dev_id].map_td_ids &&
                                   s.subjects.eehcis[eehci_dev_id].map_td_ids[usbtd_reg_offset] == eehci_other_td_id;
    Lemma_WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs_ProveUSBTDRegOffsetInRange(s, eehci_dev_id, usbtd_reg_offset);
    assert usbtd_reg_offset in eehci_usbtd_regs_offsets();
    var usbtd_reg_id:uint32 := eehci_usbtd_reg_offset_to_id(usbtd_reg_offset);

    // Find ID word of the eEHCI
    var eehci_idword:word := EEHCI_DevID_ToIDWord(s.subjects, s.objects, s.id_mappings, eehci_dev_id);

    // If the eEHCI is in <g_eehci_mem_info>, then use the <usbtd_reg> there. Otherwise, the result must be 
    // USBTD_SlotID_INVALID, because the eEHCI has never been used by any wimp drivers yet
    if(eehci_idword_in_record(globals, eehci_idword)) then
        var eehci_slot := eehci_get_slot_by_idword(globals, eehci_idword);
        var usbtd_reg_val:word := eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id);

        (eehci_idword, usbtd_reg_id, usbtd_reg_val)
    else
        (eehci_idword, usbtd_reg_id, USBTD_SlotID_INVALID)
}

// Function: Return the <usbtd_reg_id> corresponding to the memory offset of the <usbtd_reg>
function eehci_usbtd_reg_offset_to_id(offset:uint32) : (usbtd_reg_id:uint32)
    requires offset in eehci_usbtd_regs_offsets()

    ensures G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * ARCH_WORD_BYTES == offset
    ensures 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
{
    (offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset)/ARCH_WORD_BYTES
}

lemma Lemma_WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs_ProveUSBTDRegOffsetInRange(
    s:state, eehci_dev_id:Dev_ID, usbtd_reg_offset:uint32
)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)

    requires eehci_dev_id in s.subjects.eehcis
    requires usbtd_reg_offset in s.subjects.eehcis[eehci_dev_id].map_td_ids

    ensures usbtd_reg_offset in eehci_usbtd_regs_offsets()
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();

    var temp := eehci_usbtd_regs_offsets();
    var map_td_ids := s.subjects.eehcis[eehci_dev_id].map_td_ids;
    assert MapGetKeys(map_td_ids) == temp;
    Lemma_KeyInMapIffKeyInMapGetKeys(map_td_ids);
    assert usbtd_reg_offset in MapGetKeys(map_td_ids);
    assert usbtd_reg_offset in temp; 
}




/*********************** Private Functions and Lemmas - FDs ********************/
function WSM_MapState_FDsToAbstractFDs_PickActiveFDs(s:state) : (result:map<FD_ID, FD_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in result
                ==> id in WSM_AllFDIDs(s.objects)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result
                ==> WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        // Property: Returned FDs must be active
    ensures var all_fds := WSM_MapState_GatherAllAbstractFDs(s);
            forall id :: id in result
                ==> result[id] == all_fds[id]
{
    var globals := wkm_get_globals(s.wk_mstate);
    var all_fds := WSM_MapState_GatherAllAbstractFDs(s);

    map e | e in all_fds && 
            WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, e.oid)
        :: all_fds[e]
}

function WSM_MapState_FDsToAbstractFDs_PickInactiveFDs(s:state) : (result:map<FD_ID, FD_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in result
                ==> id in WSM_AllFDIDs(s.objects)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result
                ==> !WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        // Property: Returned FDs must be inactive
    ensures var all_fds := WSM_MapState_GatherAllAbstractFDs(s);
            forall id :: id in result
                ==> result[id] == all_fds[id]
{
    var globals := wkm_get_globals(s.wk_mstate);
    var all_fds := WSM_MapState_GatherAllAbstractFDs(s);

    map e | e in all_fds &&
            !WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, e.oid)
        :: all_fds[e]
}

// Function: Merge all FD mappings into a single map
function WSM_MapState_GatherAllAbstractFDs(s:state) : (result:map<FD_ID, FD_State>)
    requires OpsSaneStateSubset(s)

    ensures MapGetKeys(result) == WSM_AllFDIDs(s.objects)
    ensures forall id :: id in result
                ==> var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                    (id in s.objects.os_fds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.os_fds[id].val) &&
                    (id in s.objects.eehci_fds ==>
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_MapStateToAbstractFDs_ForEEHCIFDs(s)[id].val) &&
                    (id in s.objects.usbpdev_fds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.usbpdev_fds[id]) &&
                    (id in s.objects.usbtd_fds ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_MapStateToAbstractFDs_ForFDsInUSBTD(s)[id].val)
{
    var result1 := WSM_MapStateToAbstractFDs_ForEEHCIFDs(s);
    var result2 := WSM_MapStateToAbstractFDs_ForFDsInUSBTD(s);

    var result3 := map id | id in s.objects.os_fds
                    :: FD_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                        ),
                        s.objects.os_fds[id].val
                    );

    var result4 := map id | id in s.objects.usbpdev_fds
                    :: FD_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                        ),
                        s.objects.usbpdev_fds[id]
                    );


    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    
    MapConcat(MapConcat(result1, result2), MapConcat(result3, result4))
}

function WSM_MapStateToAbstractFDs_ForEEHCIFDs(s:state) : (k_objects_fds:map<FD_ID, FD_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_SecureMState(s.wk_mstate)

    ensures forall id :: id in s.objects.eehci_fds <==> id in k_objects_fds
    ensures forall id :: id in s.objects.eehci_fds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_fds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
        // Property: PIDs are mapped correctly
    ensures forall id :: id in s.objects.eehci_fds
                ==> k_objects_fds[id].val == WSM_eEHCI_GetAbstractFDVal(s, id)
        // Property: FD values are mapped correctly
{
    var eehci_fds:set<FD_ID> := s.objects.eehci_fds;

    map id | id in eehci_fds
            :: 
            FD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_eEHCI_GetAbstractFDVal(s, id)
            )
}

function WSM_MapStateToAbstractFDs_ForFDsInUSBTD(s:state) : (k_objects_fds:map<FD_ID, FD_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_SecureMState(s.wk_mstate)

    ensures forall id :: id in s.objects.usbtd_fds <==> id in k_objects_fds
    ensures forall id :: id in s.objects.usbtd_fds
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_fds[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
        // Property: PIDs are mapped correctly
    ensures forall id :: id in s.objects.usbtd_fds
                ==> k_objects_fds[id].val == WSM_USBTD_GetAbstractFDVal(s, id)
        // Property: FD values are mapped correctly
{
    var usbtd_fds:set<FD_ID> := s.objects.usbtd_fds;

    map id | id in usbtd_fds
            :: 
            FD_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_USBTD_GetAbstractFDVal(s, id)
            )
}




/*********************** Private Functions and Lemmas - DOs ********************/
function WSM_MapState_DOsToAbstractDOs_PickActiveDOs(s:state) : (result:map<DO_ID, DO_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in result
                ==> id in WSM_AllDOIDs(s.objects)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result
                ==> WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        // Property: Returned DOs must be active
    ensures var all_dos := WSM_MapState_GatherAllAbstractDOs(s);
            forall id :: id in result
                ==> result[id] == all_dos[id]
{
    var globals := wkm_get_globals(s.wk_mstate);
    var all_dos := WSM_MapState_GatherAllAbstractDOs(s);

    map e | e in all_dos && 
            WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, e.oid)
        :: all_dos[e]
}

function WSM_MapState_DOsToAbstractDOs_PickInactiveDOs(s:state) : (result:map<DO_ID, DO_State>)
    requires OpsSaneStateSubset(s)

    ensures forall id :: id in result
                ==> id in WSM_AllDOIDs(s.objects)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall id :: id in result
                ==> !WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, id.oid)
        // Property: Returned DOs must be inactive
    ensures var all_dos := WSM_MapState_GatherAllAbstractDOs(s);
            forall id :: id in result
                ==> result[id] == all_dos[id]
{
    var globals := wkm_get_globals(s.wk_mstate);
    var all_dos := WSM_MapState_GatherAllAbstractDOs(s);

    map e | e in all_dos &&
            !WSM_IsActiveObj(s.subjects, s.objects, s.id_mappings, globals, e.oid)
        :: all_dos[e]
}

// Function: Merge all DO mappings into a single map
function WSM_MapState_GatherAllAbstractDOs(s:state) : (result:map<DO_ID, DO_State>)
    requires OpsSaneStateSubset(s)

    ensures MapGetKeys(result) == WSM_AllDOIDs(s.objects)
    ensures forall id :: id in result
                ==> var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                    (id in s.objects.os_dos ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.os_dos[id].val) &&
                    (id in s.objects.eehci_dos ==>
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_MapStateToAbstractDOs_ForEEHCIDOs(s)[id].val) &&
                    (id in s.objects.usbpdev_dos ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.usbpdev_dos[id]) &&
                    (id in s.objects.wimpdrv_dos ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == s.objects.wimpdrv_dos[id]) &&
                    (id in s.objects.usbtd_dos ==> 
                        result[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid) &&
                        result[id].val == WSM_MapStateToAbstractDOs_ForDOsInUSBTD(s)[id].val)
{
    var result1 := WSM_MapStateToAbstractDOs_ForEEHCIDOs(s);
    var result2 := WSM_MapStateToAbstractDOs_ForDOsInUSBTD(s);

    var result3 := map id | id in s.objects.os_dos
                    :: DO_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                        ),
                        s.objects.os_dos[id].val
                    );
    assert MapGetKeys(result3) == MapGetKeys(s.objects.os_dos);

    var result4 := map id | id in s.objects.usbpdev_dos
                    :: DO_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                        ),
                        s.objects.usbpdev_dos[id]
                    );
    assert MapGetKeys(result4) == MapGetKeys(s.objects.usbpdev_dos);

    var result5 := map id | id in s.objects.wimpdrv_dos
                    :: DO_State(
                        WSM_MapWSParititonID_ToAbstractPartitionID(
                            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                        ),
                        s.objects.wimpdrv_dos[id]
                    );
    assert MapGetKeys(result5) == MapGetKeys(s.objects.wimpdrv_dos);

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    var m1 := MapConcat(MapConcat(result1, result2), MapConcat(result3, result4));
    MapConcat(m1, result5)
}

function WSM_MapStateToAbstractDOs_ForEEHCIDOs(s:state) : (k_objects_dos:map<DO_ID, DO_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_SecureMState(s.wk_mstate)

    ensures forall id :: id in s.objects.eehci_dos <==> id in k_objects_dos
    ensures forall id :: id in s.objects.eehci_dos
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_dos[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
        // Property: PIDs are mapped correctly
    ensures forall id :: id in s.objects.eehci_dos
                ==> k_objects_dos[id].val == WSM_eEHCI_GetAbstractDOVal(s, id)
        // Property: DO values are mapped correctly
{
    var eehci_dos:set<DO_ID> := s.objects.eehci_dos;

    map id | id in eehci_dos
            :: 
            DO_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_eEHCI_GetAbstractDOVal(s, id)
            )
}

function WSM_MapStateToAbstractDOs_ForDOsInUSBTD(s:state) : (k_objects_dos:map<DO_ID, DO_State>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_SecureMState(s.wk_mstate)

    ensures forall id :: id in s.objects.usbtd_dos <==> id in k_objects_dos
    ensures forall id :: id in s.objects.usbtd_dos
                ==> (var pid:WS_PartitionID := WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid);
                        k_objects_dos[id].pid == WSM_MapWSParititonID_ToAbstractPartitionID(pid)
                    )
        // Property: PIDs are mapped correctly
    ensures forall id :: id in s.objects.usbtd_dos
                ==> k_objects_dos[id].val == WSM_USBTD_GetAbstractDOVal(s, id)
        // Property: DO values are mapped correctly
{
    var usbtd_dos:set<DO_ID> := s.objects.usbtd_dos;

    map id | id in usbtd_dos
            :: 
            DO_State(
                WSM_MapWSParititonID_ToAbstractPartitionID(
                    WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id.oid)
                ), 
                WSM_USBTD_GetAbstractDOVal(s, id)
            )
}