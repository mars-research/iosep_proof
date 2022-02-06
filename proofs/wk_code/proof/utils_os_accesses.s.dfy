include "DM_AdditionalPredicates.s.dfy"
include "DM_Operations_Stubs.s.dfy"
include "state_map_OpsSaneState.i.dfy"
include "../state_properties_OpsSaneStateSubset.s.dfy"
include "../../WK_Design/Model.dfy"

/*********************** Axioms - DrvRead/DevRead ********************/
// [State/Ops Mapping] Axiom (well known): Given a memory read transfer by OS drivers, the function can convert target memory  
// address to object IDs. Only the objects to be read are returned
function {:axiom} OSDrvRead_ByPAddr_GetReadObjs(
    s:state, paddr:PAddrRegion
) : (result:(set<TD_ID>, set<FD_ID>, set<DO_ID>))
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
        // Requirement: The OS partition and the wimp partitions must be separate in memory

    requires paddr.paddr_start <= paddr.paddr_end

    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.tds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be TDs to be read
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.fds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: FDs in the result must be FDs to be read
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.dos_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: DOs in the result must be DOs to be read
    ensures var read_tds := result.0; // IDs of TDs overlapping with the memory region <paddr>
            var read_fds := result.1; // IDs of FDs overlapping with the memory region <paddr>
            var read_dos := result.2; // IDs of DOs overlapping with the memory region <paddr>
            P_OSDrvAccess_AccessActiveObjsOnly(s, read_tds, read_fds, read_dos)
        // Property: Because of MMU and nested page table, OS drivers can only access active objects in the OS partition

// [State/Ops Mapping] Axiom (well known): Given a PIO read transfer by OS drivers, the function can convert target PIO 
// address to object IDs. Only the objects to be read are returned
function {:axiom} OSDrvRead_ByPIO_GetReadObjs(
    s:state, pio_addr:ioaddr
) : (result:(set<TD_ID>, set<FD_ID>, set<DO_ID>))
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
        // Requirement: The wimp objects do not have PIO addr

    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pio :: pio in s.objs_addrs.tds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: TDs in the result must be TDs to be read
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pio :: pio in s.objs_addrs.fds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: FDs in the result must be FDs to be read
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pio :: pio in s.objs_addrs.dos_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: DOs in the result must be DOs to be read
    ensures var read_tds := result.0; // IDs of TDs located at the PIO addr <pio_addr>
            var read_fds := result.1; // IDs of FDs located at the PIO addr <pio_addr>
            var read_dos := result.2; // IDs of DOs located at the PIO addr <pio_addr>
            P_OSDrvAccess_AccessActiveObjsOnly(s, read_tds, read_fds, read_dos)
        // Property: PIO address space only contains active objects in the OS partition

// [State/Ops Mapping] Axiom (well known): Given a memory read transfer by OS devices, the function can convert target memory 
// address to object IDs. Only the objects to be read are returned
function {:axiom} OSDevRead_ByPAddr_GetReadObjs(
    s:state, paddr:PAddrRegion
) : (result:(set<TD_ID>, set<FD_ID>, set<DO_ID>))
    requires paddr.paddr_start <= paddr.paddr_end
    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.tds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be TDs to be read
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.fds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: FDs in the result must be FDs to be read
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.dos_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: DOs in the result must be DOs to be read

// [State/Ops Mapping] Axiom (well known): Given a PIO read transfer by OS devices, the function can convert target PIO 
// address to object IDs. Only the objects to be read are returned
function {:axiom} OSDevRead_ByPIO_GetReadObjs(
    s:state, pio_addr:ioaddr
) : (result:(set<TD_ID>, set<FD_ID>, set<DO_ID>))
    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pio :: pio in s.objs_addrs.tds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: TDs in the result must be TDs to be read
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pio :: pio in s.objs_addrs.fds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: FDs in the result must be FDs to be read
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pio :: pio in s.objs_addrs.dos_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: DOs in the result must be DOs to be read




/*********************** Axioms - DrvWrite/DevWrite ********************/
// [State/Ops Mapping] Axiom (well known): Given a memory write transfer, the function can convert target memory address and 
// new string values to object IDs and object values. Only the objects to be modified are returned
function {:axiom} OSDrvWrite_ByPAddr_GetWriteObjsValsPairs(
    s:state, paddr:PAddrRegion, new_v:string
) : (result:(map<TD_ID, OS_TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
        // Requirement: The OS partition and the wimp partitions must be separate in memory

    requires paddr.paddr_start <= paddr.paddr_end

    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.tds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be TDs to be modified
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.fds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be FDs to be modified
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.dos_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be DOs to be modified
    ensures var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := result.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := result.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := result.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: Because of MMU and nested page table, OS drivers can only access active objects in the OS partition

// [State/Ops Mapping] Axiom (well known): Given a PIO write transfer, the function can convert target PIO address and new 
// string values to object IDs and object values. Only the objects to be modified are returned
function {:axiom} OSDrvWrite_ByPIO_GetWriteObjsValsPairs(
    s:state, pio_addr:ioaddr, new_v:string
) : (result:(map<TD_ID, OS_TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
        // Requirement: The OS partition and the wimp partitions must be separate in memory

    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pio :: pio in s.objs_addrs.tds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: TDs in the result must be TDs to be modified
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pio :: pio in s.objs_addrs.fds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: TDs in the result must be FDs to be modified
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pio :: pio in s.objs_addrs.dos_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: TDs in the result must be DOs to be modified
    ensures var wsm_td_id_val_map:map<TD_ID, OS_TD_Val> := result.0; // IDs of TDs overlapping with the memory region <paddr>, and values to be written
            var wsm_fd_id_val_map:map<FD_ID, FD_Val> := result.1; // IDs of FDs overlapping with the memory region <paddr>, and values to be written
            var wsm_do_id_val_map:map<DO_ID, DO_Val> := result.2; // IDs of DOs overlapping with the memory region <paddr>, and values to be written
            P_OSDrvAccess_AccessActiveObjsOnly(s, MapGetKeys(wsm_td_id_val_map), MapGetKeys(wsm_fd_id_val_map), MapGetKeys(wsm_do_id_val_map))
        // Property: PIO address space only contains active objects in the OS partition

// [State/Ops Mapping] Axiom (well known): Given a memory write transfer, the function can convert target memory address and  
// new string values to object IDs and object values. Only the objects to be modified are returned
function {:axiom} OSDevWrite_ByPAddr_GetWriteObjsValsPairs(
    s:state, paddr:PAddrRegion, new_v:string
) : (result:(map<TD_ID, OS_TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires paddr.paddr_start <= paddr.paddr_end
    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.tds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be TDs to be modified
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.fds_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be FDs to be modified
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pmem :: pmem in s.objs_addrs.dos_addrs[id].paddrs &&
                                    pmem.paddr_start <= pmem.paddr_end &&
                                    is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr.paddr_start, paddr.paddr_end)
                    )
        // Property: TDs in the result must be DOs to be modified

// [State/Ops Mapping] Axiom (well known): Given a PIO write transfer, the function can convert target PIO address and new 
// string values to object IDs and object values. Only the objects to be modified are returned
function {:axiom} OSDevWrite_ByPIO_GetWriteObjsValsPairs(
    s:state, pio_addr:ioaddr, new_v:string
) : (result:(map<TD_ID, OS_TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    ensures forall id :: id in result.0
                ==> id in s.objs_addrs.tds_addrs &&
                    (exists pio :: pio in s.objs_addrs.tds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: TDs in the result must be TDs to be modified
    ensures forall id :: id in result.1
                ==> id in s.objs_addrs.fds_addrs &&
                    (exists pio :: pio in s.objs_addrs.fds_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: FDs in the result must be FDs to be modified
    ensures forall id :: id in result.2
                ==> id in s.objs_addrs.dos_addrs &&
                    (exists pio :: pio in s.objs_addrs.dos_addrs[id].pio_addrs &&
                                    pio == pio_addr
                    )
        // Property: DOs in the result must be DOs to be modified
        
// [State/Ops Mapping] Axiom (well known): "Writing to TDs (by IDs) with new OS_TD_Vals in WK implemnetation model" always 
// map to "writing to the same set of TDs with new TD_Vals in WK design model"
function {:axiom} OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>
) : (result:map<TD_ID, TD_Val>)
    ensures MapGetKeys(result) == MapGetKeys(wsm_td_id_val_map)

// [HW] Axiom: Properties of early mediation performed by IOMMU. That is, if OS devices do not reference wimp objects  
// and pEHCIs by PIO addresses and IDs, then the OS devices cannot issue cross-partition transfers to them directly and 
// indirectly.
// [NOTE] Red OS/Apps can never access USBPDevs, even after red OS/Apps grabs these devices from wimp drivers. This is
// because red OS/Apps need to grab the *physical* USB HC as well, which can only be done outside a trace of this model 
// ends. (Recall that I/O separation model and its interpretations cannot see the *physical* USB HC).
// [NOTE] We regard IOMMU perform early memory access mediation, even though it performs late mediation in fact.
// [TODO] This axiom can be loosen and allow pEHCIs to have PIO addresses if they are active in the OS partition.
function {:axiom} IOMMU_DevHWProt(in_s:state) : (out_s:state)
    requires OpsSaneStateSubset(in_s)

    requires OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(in_s)
    requires P_WimpObjs_HaveNoPIOAddr(in_s)
        // Requirement: In in_s.objects.os_tds, only <trans_params_*_atpaddr> can reference wimp objects active in wimp 
        // partitions or inactive
    requires OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(in_s)
    requires P_PEHCIsObjs_HaveNoPIOAddr(in_s)
        // Requirement: In in_s.objects.os_tds, only <trans_params_*_atpaddr> can reference pEHCIs' objects

    ensures out_s.wk_mstate == in_s.wk_mstate &&
            out_s.subjects == in_s.subjects &&
            out_s.objs_addrs == in_s.objs_addrs &&
            out_s.id_mappings == in_s.id_mappings &&
            out_s.activate_conds == in_s.activate_conds &&
            out_s.ok == in_s.ok &&
            out_s.os_mem_active_map == in_s.os_mem_active_map
    ensures out_s.objects.os_fds == in_s.objects.os_fds &&
            out_s.objects.os_dos == in_s.objects.os_dos &&
            out_s.objects.eehci_hcoded_tds == in_s.objects.eehci_hcoded_tds &&
            out_s.objects.eehci_other_tds == in_s.objects.eehci_other_tds &&
            out_s.objects.eehci_fds == in_s.objects.eehci_fds &&
            out_s.objects.eehci_dos == in_s.objects.eehci_dos &&
            out_s.objects.usbpdev_tds == in_s.objects.usbpdev_tds &&
            out_s.objects.usbpdev_fds == in_s.objects.usbpdev_fds &&
            out_s.objects.usbpdev_dos == in_s.objects.usbpdev_dos &&
            out_s.objects.wimpdrv_dos == in_s.objects.wimpdrv_dos &&
            out_s.objects.usbtd_tds == in_s.objects.usbtd_tds &&
            out_s.objects.usbtd_fds == in_s.objects.usbtd_fds &&
            out_s.objects.usbtd_dos == in_s.objects.usbtd_dos
        // Property: Only in_s.objects.os_tds is modified
    ensures OpsSaneState(out_s)
        // Property: <out_s> must be a valid and secure state. 
        // We can assume OpsSaneStateSubset(out_s). This is easy to prove when only in_s.objects.os_tds is modified

// [State/Ops Mapping] Axiom (well known): In OSDrvWrite_* operation, if only s.objects.os_tds/fds/dos are modified, then 
// there exists td/fd/do_id_val_map in the WK design spec, such that the OSDrvWrite operation in the WK implementation 
// spec maps to the WS_RedDrvWrite operation with these parameters in the WK design spec
// [NOTE] Needs 50s to verify
function {:axiom} OSDrvWrite_ProveCommutativeDiagram_GetOpParamsForDesignModel(
    s:state, s':state, drv_sid:Subject_ID
) : (result:(map<TD_ID, TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires OpsSaneState(s)
    requires OpsSaneState(s')
    requires forall ws:DM_State, op:DM_Op :: P_DM_OpsProperties(ws, op)
    
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), drv_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: The driver is in the red partition

    requires s'.wk_mstate == s.wk_mstate &&
            s'.subjects == s.subjects &&
            s'.objs_addrs == s.objs_addrs &&
            s'.id_mappings == s.id_mappings &&
            s'.activate_conds == s.activate_conds &&
            s'.ok == s.ok &&
            s'.os_mem_active_map == s.os_mem_active_map
    requires s'.objects.eehci_hcoded_tds == s.objects.eehci_hcoded_tds &&
            s'.objects.eehci_other_tds == s.objects.eehci_other_tds &&
            s'.objects.eehci_fds == s.objects.eehci_fds &&
            s'.objects.eehci_dos == s.objects.eehci_dos &&
            s'.objects.usbpdev_tds == s.objects.usbpdev_tds &&
            s'.objects.usbpdev_fds == s.objects.usbpdev_fds &&
            s'.objects.usbpdev_dos == s.objects.usbpdev_dos &&
            s'.objects.wimpdrv_dos == s.objects.wimpdrv_dos &&
            s'.objects.usbtd_tds == s.objects.usbtd_tds &&
            s'.objects.usbtd_fds == s.objects.usbtd_fds &&
            s'.objects.usbtd_dos == s.objects.usbtd_dos
        // Requirement: Only s.objects.os_tds/fds/dos are modified

    requires var dm := WSM_MapState(s);
            DM_IsValidState(dm) && DM_IsSecureState(dm)
        // Requirement: s maps to a good state in the WK design spec
        
    ensures var dm := WSM_MapState(s);
            var td_id_val_map := result.0;
            var fd_id_val_map := result.1;
            var do_id_val_map := result.2;
            (forall td_id :: td_id in td_id_val_map ==> td_id in DM_AllTDIDs(dm.objects)) &&
            (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in DM_AllFDIDs(dm.objects)) &&
            (forall do_id :: do_id in do_id_val_map ==> do_id in DM_AllDOIDs(dm.objects))
    ensures var dm := WSM_MapState(s);
            var td_id_val_map := result.0;
            var fd_id_val_map := result.1;
            var do_id_val_map := result.2;
            forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
    ensures var dm := WSM_MapState(s);
            var dm' := WSM_MapState(s');
            var td_id_val_map := result.0;
            var fd_id_val_map := result.1;
            var do_id_val_map := result.2;
            dm' == WSD_OSDrvWrite_Stub(dm, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map).0
        // Property: Exists td/fd/do_id_val_map in the WK design spec, such that the OSDrvWrite operation in the WK 
        // implementation spec maps to the WS_RedDrvWrite operation with these parameters in the WK design spec

// Axiom: <IOMMU_DevHWProt> refines <DevHWProt>
lemma {:axiom} Lemma_IOMMU_DevHWProt_Refines_DevHWProt(orig_s:state, in_s:state)
    requires OpsSaneStateSubset(orig_s)
    requires OpsSaneStateSubset(in_s)
    requires OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(in_s)
    requires P_WimpObjs_HaveNoPIOAddr(in_s)
        // Requirement: In in_s.objects.os_tds, only <trans_params_*_atpaddr> can reference wimp objects active in wimp 
        // partitions or inactive
    requires OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(in_s)
    requires P_PEHCIsObjs_HaveNoPIOAddr(in_s)
        // Requirement: In in_s.objects.os_tds, only <trans_params_*_atpaddr> can reference pEHCIs' objects

    requires var dm := WSM_MapState(in_s);
             P_DMObjectsHasUniqueIDs(dm.objects)
    requires var dm := WSM_MapState(in_s);
             DM_IsValidState_SubjsObjsPIDs(dm)
    requires var dm := WSM_MapState(in_s);
             IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(dm.objects)
    requires var dm := WSM_MapState(in_s);
             DM_IsValidState_DevsActivateCond(dm)
        // Requirement: 

    ensures var out_s := IOMMU_DevHWProt(in_s);
            var orig_dm := WSM_MapState(orig_s);
            var dm := WSM_MapState(in_s);
            var dm' := WSM_MapState(out_s);
            dm' == DevHWProt(orig_dm, dm)




/*********************** Utility Functions and Predicates ********************/
predicate P_WimpObjs_HaveNoPIOAddr(s:state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
{
    (forall id:TD_ID, pio:ioaddr :: WSM_IsWimpTDID(s.objects, id)
        ==> pio !in s.objs_addrs.tds_addrs[id].pio_addrs
    ) &&
    (forall id:FD_ID, pio:ioaddr :: WSM_IsWimpFDID(s.objects, id)
        ==> pio !in s.objs_addrs.fds_addrs[id].pio_addrs
    ) &&
    (forall id:DO_ID, pio:ioaddr :: WSM_IsWimpDOID(s.objects, id)
        ==> pio !in s.objs_addrs.dos_addrs[id].pio_addrs
    )
}

predicate P_PEHCIsObjs_HaveNoPIOAddr(s:state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjsAddrs();

    var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);

    (forall id:TD_ID, pio:ioaddr :: id in pehci_td_ids
        ==> pio !in s.objs_addrs.tds_addrs[id].pio_addrs
    ) &&
    (forall id:FD_ID, pio:ioaddr :: id in pehci_fd_ids
        ==> pio !in s.objs_addrs.fds_addrs[id].pio_addrs
    ) &&
    (forall id:DO_ID, pio:ioaddr :: id in pehci_do_ids
        ==> pio !in s.objs_addrs.dos_addrs[id].pio_addrs
    )
}

// Predicate: If the OS device writes to a set of TDs/FDs/DOs with some values, then the device must be able to write 
// the corresponding objects with the corresponding values in the WK design model
predicate WSM_OSDevWrite_TransfersMustBeDefinedInWSDesignModel(
    s:state, dev_sid:Subject_ID, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires WSM_IsOSDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                == WS_PartitionID(PID_RESERVED_OS_PARTITION)
        // Requirement: the device is in the red partition
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    var td_id_val_map:map<TD_ID, TD_Val> := OSDrvDevWrite_TDObjWritingInWKImpl_MapsToTDObjWritingInWKDesign(wsm_td_id_val_map);
    var fd_id_val_map:map<FD_ID, FD_Val> := wsm_fd_id_val_map;
    var do_id_val_map:map<DO_ID, DO_Val> := wsm_do_id_val_map;

    (forall td_id2 :: td_id2 in td_id_val_map
                ==> DM_DevWrite_WriteTDWithValMustBeInATransfer(dm, dev_sid, td_id2, td_id_val_map[td_id2])) &&
    (forall fd_id2 :: fd_id2 in fd_id_val_map
                ==> DM_DevWrite_WriteFDWithValMustBeInATransfer(dm, dev_sid, fd_id2, fd_id_val_map[fd_id2])) &&
    (forall do_id2 :: do_id2 in do_id_val_map
                ==> DM_DevWrite_WriteDOWithValMustBeInATransfer(dm, dev_sid, do_id2, do_id_val_map[do_id2]))
}

function {:opaque} WS_OSDrvAccess_ChkDrvAndObjsAreInSamePartition(
    s:state, 
    drv_sid:Subject_ID, // ID of the device issues the write access
    td_ids:set<TD_ID>,
    fd_ids:set<FD_ID>, 
    do_ids:set<DO_ID>
) : bool
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    
    requires WSM_IsOSDrvID(s.subjects, Drv_ID(drv_sid))
    
    requires (forall td_id :: td_id in td_ids ==> td_id in WSM_AllTDIDs(s.objects)) &&
            (forall fd_id :: fd_id in fd_ids ==> fd_id in WSM_AllFDIDs(s.objects)) &&
            (forall do_id :: do_id in do_ids ==> do_id in WSM_AllDOIDs(s.objects))
        // Requirement: Driver only write existing objects
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall id :: id in td_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid) ==
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in fd_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid) ==
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid)) &&
    (forall id :: id in do_ids
        ==> WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, drv_sid) ==
            WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid))
}

predicate OSDrvWrite_OSTDsHasNoRefToWimpObjsByIDs_AfterModification1(s:state)
{
    (forall td_id, td_id2 :: td_id in s.objects.os_tds &&
            td_id2 in s.objects.os_tds[td_id].val.trans_params_tds_atoid
        ==> !WSM_IsWimpTDID(s.objects, td_id2)
    ) &&
    (forall td_id, fd_id2 :: td_id in s.objects.os_tds &&
            fd_id2 in s.objects.os_tds[td_id].val.trans_params_fds_atoid
        ==> !WSM_IsWimpFDID(s.objects, fd_id2)
    ) &&
    (forall td_id, do_id2 :: td_id in s.objects.os_tds &&
            do_id2 in s.objects.os_tds[td_id].val.trans_params_dos_atoid
        ==> !WSM_IsWimpDOID(s.objects, do_id2)
    ) &&

    (true)
}

predicate OSDrvWrite_OSTDsOutsidePEHCIsHasNoRefToPEHCIObjsByIDs_AfterModification1(s:state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidState_DevsActivateCond(s.subjects, s.objects, s.id_mappings, s.activate_conds, wkm_get_globals(s.wk_mstate))
{
    reveal WK_ValidState_DevsActivateCond();

    var pehci_ids := WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s, pehci_ids);

    (forall td_id, td_id2 :: td_id in s.objects.os_tds && 
            td_id !in pehci_td_ids &&
            td_id2 in s.objects.os_tds[td_id].val.trans_params_tds_atoid
        ==> td_id2 !in pehci_td_ids
        // For all OS TDs in <s.objects.os_tds>, if they are not owned by a PEHCI, then it doesn't reference PEHCIs' 
        // objects by IDs
    ) &&
    (forall td_id, fd_id2 :: td_id in s.objects.os_tds &&
            td_id !in pehci_td_ids &&
            fd_id2 in s.objects.os_tds[td_id].val.trans_params_fds_atoid
        ==> fd_id2 !in pehci_fd_ids
    ) &&
    (forall td_id, do_id2 :: td_id in s.objects.os_tds &&
            td_id !in pehci_td_ids &&
            do_id2 in s.objects.os_tds[td_id].val.trans_params_dos_atoid
        ==> do_id2 !in pehci_do_ids
    ) &&

    (true)
}

// Predicate: If a device reads a set of TDs/FDs/DOs , then the device must be able to read the corresponding 
// objects in the WK design model
predicate WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(
    s:state, dev_sid:Subject_ID, 
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    DM_DevRead_TransfersMustBeDefinedInWSDesignModel(dm, dev_sid, read_tds, read_fds, read_dos)
}

predicate P_OSDrvAccess_AccessActiveObjsOnly(s:state, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall td_id :: td_id in td_ids ==> td_id in WSM_AllTDIDs(s.objects)) &&
    (forall fd_id :: fd_id in fd_ids ==> fd_id in WSM_AllFDIDs(s.objects)) &&
    (forall do_id :: do_id in do_ids ==> do_id in WSM_AllDOIDs(s.objects)) &&

    (forall id :: id in td_ids
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in fd_ids
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in do_ids
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION))
        // Property: Because of MMU and nested page table, OS drivers can only access active objects in the OS partition
}

predicate P_OSDevWrite_AccessOSObjsOnly(s:state, 
    wsm_td_id_val_map:map<TD_ID, OS_TD_Val>, wsm_fd_id_val_map:map<FD_ID, FD_Val>, wsm_do_id_val_map:map<DO_ID, DO_Val>
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall id :: id in wsm_td_id_val_map 
                ==> id in s.objects.os_tds) &&
    (forall id :: id in wsm_fd_id_val_map 
                ==> id in s.objects.os_fds) &&
    (forall id :: id in wsm_do_id_val_map 
                ==> id in s.objects.os_dos) &&

    (forall id :: id in wsm_td_id_val_map
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in wsm_fd_id_val_map
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&
    (forall id :: id in wsm_do_id_val_map
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == WS_PartitionID(PID_RESERVED_OS_PARTITION)) &&

    (true)
}

predicate P_EEHCIWriteUSBPDevObjs(s:state, eehci_id:Dev_ID,
    fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WSM_IsEEHCIDevID(s.subjects, eehci_id)
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall id :: id in fd_id_val_map 
                ==> id in s.objects.usbpdev_fds) &&
    (forall id :: id in do_id_val_map 
                ==> id in s.objects.usbpdev_dos) &&

    (forall id :: id in fd_id_val_map
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
            WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)
    ) &&
    (forall id :: id in do_id_val_map
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
            WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)
    ) &&

    (true)
}

predicate P_EEHCIWriteWimpDrvDO(s:state, eehci_id:Dev_ID,
     do_id_val_map:map<DO_ID, DO_Val>
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires WSM_IsEEHCIDevID(s.subjects, eehci_id)
{
    var globals := wkm_get_globals(s.wk_mstate);

    (forall id :: id in do_id_val_map 
                ==> id in s.objects.wimpdrv_dos) &&

    (forall id :: id in do_id_val_map
        ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, id.oid) == 
            WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, eehci_id.sid)
    ) &&

    (true)
}