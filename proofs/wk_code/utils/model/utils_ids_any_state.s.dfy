include "../../state.dfy"

function method WSM_IsSubjID(subjs:WSM_Subjects, s_id:Subject_ID) : bool
{
    Drv_ID(s_id) in subjs.wimp_drvs || Drv_ID(s_id) in subjs.os_drvs ||
    Dev_ID(s_id) in subjs.eehcis || Dev_ID(s_id) in subjs.usbpdevs || Dev_ID(s_id) in subjs.os_devs
}

function method WSM_IsOSSubjID(subjs:WSM_Subjects, s_id:Subject_ID) : bool
{
    Drv_ID(s_id) in subjs.os_drvs || Dev_ID(s_id) in subjs.os_devs
}

// Return the IDs of all subjects
function method WSM_AllSubjsIDs(subjs:WSM_Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in WSM_AllSubjsIDs(subjs)
                <==> (Drv_ID(s_id) in subjs.wimp_drvs || Drv_ID(s_id) in subjs.os_drvs || 
                      Dev_ID(s_id) in subjs.eehcis || Dev_ID(s_id) in subjs.usbpdevs || Dev_ID(s_id) in subjs.os_devs)
    ensures forall s_id :: s_id in WSM_AllSubjsIDs(subjs)
                <==> WSM_IsSubjID(subjs, s_id)
{
    WSM_AllSubjsIDsInDrvs(subjs) + WSM_AllSubjsIDsInDevs(subjs)
}

function method WSM_AllDrvIDs(subjs:WSM_Subjects) : (result:set<Drv_ID>)
    ensures forall id :: id in result
                <==> id in subjs.wimp_drvs || id in subjs.os_drvs
{
    MapGetKeys(subjs.wimp_drvs) + MapGetKeys(subjs.os_drvs)
}

// Return the set<Dev_ID> of all devices
function method WSM_AllDevIDs(subjs:WSM_Subjects) : set<Dev_ID>
    ensures forall id :: id in WSM_AllDevIDs(subjs)
                <==> id in subjs.os_devs || id in subjs.usbpdevs || id in subjs.eehcis
{
    Lemma_SameIDsIffSameInternalIDs();
    MapGetKeys(subjs.os_devs) + MapGetKeys(subjs.usbpdevs) + MapGetKeys(subjs.eehcis)
}




/*********************** Util Functions and Predicates ********************/
// Return the subject IDs of all drivers
function method WSM_AllSubjsIDsInDrvs(subjs:WSM_Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in WSM_AllSubjsIDsInDrvs(subjs)
                <==> (Drv_ID(s_id) in subjs.wimp_drvs || Drv_ID(s_id) in subjs.os_drvs)
{
    Lemma_SameIDsIffSameInternalIDs();
    var combined_set := MapGetKeys(subjs.wimp_drvs) + MapGetKeys(subjs.os_drvs);

    (set drv_id, s_id | drv_id in combined_set && s_id == drv_id.sid
              :: s_id)
}

// Return the subject IDs of all devices
function method WSM_AllSubjsIDsInDevs(subjs:WSM_Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in WSM_AllSubjsIDsInDevs(subjs)
                <==> (Dev_ID(s_id) in subjs.eehcis || Dev_ID(s_id) in subjs.usbpdevs || Dev_ID(s_id) in subjs.os_devs)
{
    Lemma_SameIDsIffSameInternalIDs();
    var combined_set := MapGetKeys(subjs.eehcis) + MapGetKeys(subjs.usbpdevs) + MapGetKeys(subjs.os_devs);

    (set dev_id, s_id | dev_id in combined_set && s_id == dev_id.sid
              :: s_id)
}

