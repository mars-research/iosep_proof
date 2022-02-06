include "Syntax.dfy"
include "Properties.dfy"
include "Properties_Corollaries.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"
include "SecurityProperties_Ops.dfy"

lemma Lemma_DrvRead_SrcObjsOfCopyMustBeActive(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the read access
    read_objs:set<Object_ID>,

    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k) && IsSecureState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires SubjPID(k, drv_sid) != NULL
        // Requirement: The driver is in the state and is active
    requires read_objs <= AllObjsIDs(k.objects)

    requires DrvRead_ReadSrcObjsToDestObjs_PreConditions(k, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    requires forall id :: id in tds_dst_src 
                ==> ObjPID_KObjects(k.objects, tds_dst_src[id].oid) != NULL
    requires forall id :: id in fds_dst_src 
                ==> ObjPID_KObjects(k.objects, fds_dst_src[id].oid) != NULL
    requires forall id :: id in dos_dst_src 
                ==> ObjPID_KObjects(k.objects, dos_dst_src[id].oid) != NULL

    ensures (forall td_id :: td_id in tds_dst_src ==> tds_dst_src[td_id] in k.objects.active_non_hcoded_tds) &&
            (forall fd_id :: fd_id in fds_dst_src ==> fds_dst_src[fd_id] in k.objects.active_fds) &&
            (forall do_id :: do_id in dos_dst_src ==> dos_dst_src[do_id] in k.objects.active_dos)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
}

lemma Lemma_DevRead_ProvePreConditionsForWrite(
    k:State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active
    requires forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)
        // Requirement: The read transfers must be defined in TDs that can be
        // read by the device

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures forall td_id :: td_id in tds_dst_src
                ==> td_id in k.objects.active_non_hcoded_tds && tds_dst_src[td_id] in k.objects.active_non_hcoded_tds
    ensures forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in k.objects.active_fds && fds_dst_src[fd_id] in k.objects.active_fds
    ensures forall do_id :: do_id in dos_dst_src
                ==> do_id in k.objects.active_dos && dos_dst_src[do_id] in k.objects.active_dos
{
    Lemma_DevRead_ProvePreConditionsForWrite_TD(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    Lemma_DevRead_ProvePreConditionsForWrite_FD(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
    Lemma_DevRead_ProvePreConditionsForWrite_DO(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src);
}

// [NOTE] Needs 600s to verify
lemma Lemma_DevRead_ProvePreConditionsForWrite_TD(
    k:State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active
    requires forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)
        // Requirement: The read transfers must be defined in TDs that can be
        // read by the device

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures forall td_id :: td_id in tds_dst_src
                ==> td_id in k.objects.active_non_hcoded_tds && tds_dst_src[td_id] in k.objects.active_non_hcoded_tds
{
    forall td_id | td_id in tds_dst_src
        ensures td_id in k.objects.active_non_hcoded_tds && tds_dst_src[td_id] in k.objects.active_non_hcoded_tds
    {
        assert DevWrite_WriteTDWithValMustBeInATransfer(k, dev_sid, td_id, DevRead_GetReadObjVal_AnyTD(k.objects, tds_dst_src[td_id]));
    }
}

// [NOTE] Needs 600s to verify
lemma Lemma_DevRead_ProvePreConditionsForWrite_FD(
    k:State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active
    requires forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)
        // Requirement: The read transfers must be defined in TDs that can be
        // read by the device

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures forall fd_id :: fd_id in fds_dst_src
                ==> fd_id in k.objects.active_fds && fds_dst_src[fd_id] in k.objects.active_fds
{
    forall fd_id | fd_id in fds_dst_src
        ensures fd_id in k.objects.active_fds && fds_dst_src[fd_id] in k.objects.active_fds
    {
        assert DevWrite_WriteFDWithValMustBeInATransfer(k, dev_sid, fd_id, DevRead_GetReadObjVal_AnyFD(k.objects, fds_dst_src[fd_id]));
        //assert SubjPID(k, dev_sid) == ObjPID(k, fd_id.oid);

        //Lemma_ActiveObjsMustInActiveSet_FD(k, fd_id);
    }
}

// [NOTE] Needs 600s to verify
lemma Lemma_DevRead_ProvePreConditionsForWrite_DO(
    k:State, 
    dev_sid:Subject_ID, // ID of the device issues the read access
    read_objs:set<Object_ID>, // IDs of all objects to be read. The read 
                              // objects not copied to any other objects 
                              // are also included in <read_objs>
    tds_dst_src:map<TD_ID, TD_ID>, // Map from destination TD to source TD
    fds_dst_src:map<FD_ID, FD_ID>, // Map from destination FD to source FD
    dos_dst_src:map<DO_ID, DO_ID>  // Map from destination DO to source DO
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The device is in the state and is active
    requires forall o_id :: o_id in read_objs
            ==> R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)
        // Requirement: The read transfers must be defined in TDs that can be
        // read by the device

    requires DrvDevRead_ReadSrcObjsToDestObjs_SrcObjsOfCopyMustInReadObjs(read_objs, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_SrcAndDstObjsOfCopyMustBeInWSState(k, tds_dst_src, fds_dst_src, dos_dst_src)
    requires DevRead_ReadSrcObjsToDestObjs_WriteInCopyMustFromCorrespondingTransfers(k, dev_sid, read_objs, tds_dst_src, fds_dst_src, dos_dst_src)

    ensures forall do_id :: do_id in dos_dst_src
                ==> do_id in k.objects.active_dos && dos_dst_src[do_id] in k.objects.active_dos
{
    forall do_id | do_id in dos_dst_src
        ensures do_id in k.objects.active_dos && dos_dst_src[do_id] in k.objects.active_dos
    {
        assert DevWrite_WriteDOWithValMustBeInATransfer(k, dev_sid, do_id, DevRead_GetReadObjVal_AnyDO(k.objects, dos_dst_src[do_id]));
    }
}