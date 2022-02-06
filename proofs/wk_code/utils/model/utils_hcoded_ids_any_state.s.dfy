include "../../state.dfy"
include "utils_objs_any_state.s.dfy"

function WSM_AllHCodedTDIDs(subjs:WSM_Subjects) : set<TD_ID>
{
    WSM_AllHCodedTDIDs_OSDevs(subjs) + WSM_AllHCodedTDIDs_USBPDevs(subjs) + WSM_AllHCodedTDIDs_EEHCIs(subjs)
}




/*********************** Util Functions and Predicates ********************/
function WSM_AllHCodedTDIDs_OSDevs(subjs:WSM_Subjects) : set<TD_ID>
    ensures forall td_id :: td_id in WSM_AllHCodedTDIDs_OSDevs(subjs)
                <==> (exists dev_id :: dev_id in subjs.os_devs &&
                      td_id == subjs.os_devs[dev_id].hcoded_td_id)
{
    set dev_id | dev_id in subjs.os_devs
               :: subjs.os_devs[dev_id].hcoded_td_id
}

function WSM_AllHCodedTDIDs_USBPDevs(subjs:WSM_Subjects) : set<TD_ID>
    ensures forall td_id :: td_id in WSM_AllHCodedTDIDs_USBPDevs(subjs)
                <==> (exists dev_id :: dev_id in subjs.usbpdevs &&
                      td_id == subjs.usbpdevs[dev_id].hcoded_td_id)
{
    set dev_id | dev_id in subjs.usbpdevs
               :: subjs.usbpdevs[dev_id].hcoded_td_id
}

function WSM_AllHCodedTDIDs_EEHCIs(subjs:WSM_Subjects) : set<TD_ID>
    ensures forall td_id :: td_id in WSM_AllHCodedTDIDs_EEHCIs(subjs)
                <==> (exists dev_id :: dev_id in subjs.eehcis &&
                      td_id == subjs.eehcis[dev_id].hcoded_td_id)
{
    set dev_id | dev_id in subjs.eehcis
               :: subjs.eehcis[dev_id].hcoded_td_id
}

function WSM_BuildMap_DevsToHCodedTDVals_OSDevs(subjs:WSM_Subjects, objs:WSM_Objects) : map<Dev_ID, TD_Val>
    requires forall dev_id :: dev_id in subjs.os_devs
                ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in subjs.os_devs && td_id in subjs.os_devs[dev_id].td_ids
                ==> td_id in objs.os_tds

    ensures MapGetKeys(WSM_BuildMap_DevsToHCodedTDVals_OSDevs(subjs, objs)) == MapGetKeys(subjs.os_devs)
    ensures forall dev_id :: dev_id in subjs.os_devs
                ==> WSM_BuildMap_DevsToHCodedTDVals_OSDevs(subjs, objs)[dev_id] == 
                    WSM_MapOSTDVal_ToTDVal(objs, objs.os_tds[subjs.os_devs[dev_id].hcoded_td_id].val)
{
    map dev_id | dev_id in subjs.os_devs
               :: WSM_MapOSTDVal_ToTDVal(objs, objs.os_tds[subjs.os_devs[dev_id].hcoded_td_id].val)
}

function WSM_BuildMap_DevsToHCodedTDVals_USBPDevs(subjs:WSM_Subjects, objs:WSM_Objects) : map<Dev_ID, TD_Val>
    requires forall dev_id :: dev_id in subjs.usbpdevs
                ==> subjs.usbpdevs[dev_id].hcoded_td_id in objs.usbpdev_tds

    ensures MapGetKeys(WSM_BuildMap_DevsToHCodedTDVals_USBPDevs(subjs, objs)) == MapGetKeys(subjs.usbpdevs)
    ensures forall dev_id :: dev_id in subjs.usbpdevs
                ==> WSM_BuildMap_DevsToHCodedTDVals_USBPDevs(subjs, objs)[dev_id] == 
                    objs.usbpdev_tds[subjs.usbpdevs[dev_id].hcoded_td_id]
{
    map dev_id | dev_id in subjs.usbpdevs
               :: objs.usbpdev_tds[subjs.usbpdevs[dev_id].hcoded_td_id]
}

function WSM_BuildMap_DevsToHCodedTDVals_EEHCIs(subjs:WSM_Subjects, objs:WSM_Objects) : map<Dev_ID, TD_Val>
    requires forall dev_id :: dev_id in subjs.eehcis
                ==> subjs.eehcis[dev_id].hcoded_td_id in objs.eehci_hcoded_tds

    ensures MapGetKeys(WSM_BuildMap_DevsToHCodedTDVals_EEHCIs(subjs, objs)) == MapGetKeys(subjs.eehcis)
    ensures forall dev_id :: dev_id in subjs.eehcis
                ==> WSM_BuildMap_DevsToHCodedTDVals_EEHCIs(subjs, objs)[dev_id] == 
                    objs.eehci_hcoded_tds[subjs.eehcis[dev_id].hcoded_td_id]
{
    map dev_id | dev_id in subjs.eehcis
               :: objs.eehci_hcoded_tds[subjs.eehcis[dev_id].hcoded_td_id]
}
