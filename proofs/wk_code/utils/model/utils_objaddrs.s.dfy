include "../../state_properties_validity_subjs_objs_mstate.s.dfy"

// Function: Get all objects that overlap with the given physical memory region [paddr_start, paddr_end)
function ObjAddrs_GetAllObjectsOverlappedWithPMemRegion(
    objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, paddr_start:paddr, paddr_end:uint
) : (result:set<Object_ID>)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjs_ObjIDs(objs)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires paddr_start <= paddr_end

    ensures forall id :: id in result && WSM_IsTDID(objs, TD_ID(id))
                ==> TD_ID(id) in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForTDs(objs, objs_addrs, globals, paddr_start, paddr_end)
    ensures forall id :: id in result && WSM_IsFDID(objs, FD_ID(id))
                ==> FD_ID(id) in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForFDs(objs, objs_addrs, globals, paddr_start, paddr_end)
    ensures forall id :: id in result && WSM_IsDOID(objs, DO_ID(id))
                ==> DO_ID(id) in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForDOs(objs, objs_addrs, globals, paddr_start, paddr_end)
{
    reveal WK_ValidObjs_ObjIDs();

    (set id | id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForTDs(objs, objs_addrs, globals, paddr_start, paddr_end) :: id.oid) + 
    (set id | id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForFDs(objs, objs_addrs, globals, paddr_start, paddr_end) :: id.oid) + 
    (set id | id in ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForDOs(objs, objs_addrs, globals, paddr_start, paddr_end) :: id.oid)
}




/*********************** Private Functions ********************/
// Predicate: If the given TD overlaps with the given physical memory region [paddr_start, paddr_end)
predicate ObjAddrs_GivenTDOverlapWithPMemRegion(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, td_id:TD_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires td_id in objs_addrs.tds_addrs
    requires paddr_start <= paddr_end
{
    reveal WK_ValidObjsAddrs();
    exists pmem :: pmem in objs_addrs.tds_addrs[td_id].paddrs &&
                   is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
}

// Predicate: If the given FD overlaps with the given physical memory region [paddr_start, paddr_end)
predicate ObjAddrs_GivenFDOverlapWithPMemRegion(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, fd_id:FD_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires fd_id in objs_addrs.fds_addrs
    requires paddr_start <= paddr_end
{
    reveal WK_ValidObjsAddrs();
    exists pmem :: pmem in objs_addrs.fds_addrs[fd_id].paddrs &&
                   is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
}

// Predicate: If the given DO overlaps with the given physical memory region [paddr_start, paddr_end)
predicate ObjAddrs_GivenDOOverlapWithPMemRegion(objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, do_id:DO_ID, paddr_start:paddr, paddr_end:uint)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires do_id in objs_addrs.dos_addrs
    requires paddr_start <= paddr_end
{
    reveal WK_ValidObjsAddrs();
    exists pmem :: pmem in objs_addrs.dos_addrs[do_id].paddrs &&
                   is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, paddr_start, paddr_end)
}

// Function: Get all TDs that overlap with the given physical memory region [paddr_start, paddr_end)
function ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForTDs(
    objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, paddr_start:paddr, paddr_end:uint
) : set<TD_ID>
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires paddr_start <= paddr_end
{
    set td_id:TD_ID | td_id in objs_addrs.tds_addrs &&
                     ObjAddrs_GivenTDOverlapWithPMemRegion(objs, objs_addrs, globals, td_id, paddr_start, paddr_end)
}

// Function: Get all FDs that overlap with the given physical memory region [paddr_start, paddr_end)
function ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForFDs(
    objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, paddr_start:paddr, paddr_end:uint
) : set<FD_ID>
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires paddr_start <= paddr_end
{
    set fd_id:FD_ID | fd_id in objs_addrs.fds_addrs &&
                     ObjAddrs_GivenFDOverlapWithPMemRegion(objs, objs_addrs, globals, fd_id, paddr_start, paddr_end)
}

// Function: Get all DOs that overlap with the given physical memory region [paddr_start, paddr_end)
function ObjAddrs_GetAllObjectsOverlappedWithPMemRegion_ForDOs(
    objs:WSM_Objects, objs_addrs:WSM_Objects_Addrs, globals:globalsmap, paddr_start:paddr, paddr_end:uint
) : set<DO_ID>
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidObjsAddrs(objs, objs_addrs, globals)

    requires paddr_start <= paddr_end
{
    set do_id:DO_ID | do_id in objs_addrs.dos_addrs &&
                     ObjAddrs_GivenDOOverlapWithPMemRegion(objs, objs_addrs, globals, do_id, paddr_start, paddr_end)
}