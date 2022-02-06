include "../../utils/common/headers.dfy"
include "../common/arch_mem.dfy"
include "x86_types.dfy"
include "x86_mstate.dfy"

/*********************** WK Kernel Memory Layout - Definitions ********************/
const ADDR_SPACE_LOWER:vaddr := 0;
const ADDR_SPACE_UPPER:uint32 := 0xFFFF_FFFF;
const WK_KERN_BASE:vaddr := 0xC000_0000; // start of WK virtual address




/*********************** Architecture Specific State Invariants and Related Predicates ********************/
predicate {:opaque} x86wk_valid_memstate(mem:wk_memmap)
{
    (forall addr:vaddr :: is_vaddr_in_stack(addr) <==> addr in mem) &&

    (true)
}

// Interface realization: <WK_ValidMemForRead>
// If <addr> points to a readable memory of WK; i.e., s.wk_mstate.m
// [NOTE] s.wk_mstate.m contains the WK stack only. s.wk_mstate.m does not contain memory for global variables, because 
// their state is s.wk_mstate.globals
predicate WK_ValidMemForRead(addr:addr)
    requires WK_Mem_Separate_Segs()
    // Requirement: The validity of <addr> requires WK memory segments are separate. Otherwise, the spec of memory insts. 
    // need to modify multiple WK segments (e.g., two or more of ROMem, Stack, DATA segments), not only the Stack 
{
    is_vaddr_in_stack(addr)
}

// Interface realization: <WK_ValidMemForWrite>
// If <addr> points to a writable memory of WK; i.e., s.wk_mstate.m
// [NOTE] Memory write instructions target s.wk_mstate.m must be a stack addr.
predicate WK_ValidMemForWrite(addr:addr)
    requires WK_Mem_Separate_Segs()
    // Requirement: The validity of <addr> requires WK memory segments are separate. Otherwise, the spec of memory insts. 
    // need to modify multiple WK segments (e.g., two or more of ROMem, Stack, DATA segments), not only the Stack 
{
    is_vaddr_in_stack(addr)
}

// Interface realization: <WK_ValidMemVAddr>
// If <addr> refs a valid WK's memory address within wkm.m
predicate WK_ValidMemVAddr(addr:vaddr)
    requires WK_Mem_Separate_Segs()
    // Requirement: The validity of <addr> requires WK memory segments are separate. Otherwise, the spec of memory insts. 
    // need to modify multiple WK segments (e.g., two or more of ROMem, Stack, DATA segments), not only the Stack 
{
    WK_ValidMemForRead(addr) && WK_ValidMemForWrite(addr)
}

// Interface realization: <WK_Mem_Separate_Segs>
// WK's ROMem, Stack, DATA are separate in both vaddr space and paddr space
predicate {:opaque} WK_Mem_Separate_Segs()
{
    // WK's ROMem, Stack, DATA are separate in the vaddr space
    !(
        is_mem_region_overlap(WK_ROMem_Base(), WK_ROMem_End(), WK_StackSeg_Limit(), WK_StackSeg_Base()) ||
        is_mem_region_overlap(WK_ROMem_Base(), WK_ROMem_End(), WK_DataSeg_Base(), WK_DataSeg_End()) ||
        is_mem_region_overlap(WK_StackSeg_Limit(), WK_StackSeg_Base(), WK_DataSeg_Base(), WK_DataSeg_End())
    ) &&

    // WK's ROMem, Stack, DATA are separate in the paddr space
    !(
        is_mem_region_overlap(WK_ROMem_BasePAddr(), WK_ROMem_EndPAddr(), WK_StackSeg_LimitPAddr(), WK_StackSeg_BasePAddr()) ||
        is_mem_region_overlap(WK_ROMem_BasePAddr(), WK_ROMem_EndPAddr(), WK_DATASeg_BasePAddr(), WK_DATASeg_EndPAddr()) ||
        is_mem_region_overlap(WK_StackSeg_LimitPAddr(), WK_StackSeg_BasePAddr(), WK_DATASeg_BasePAddr(), WK_DATASeg_EndPAddr())
    )
}

// Predicate: The given paddr region [paddr_base, paddr_end) must not overlap with WK (I/O separation part)'s 
// paddr region
predicate WK_Mem_NotOverlapWithWKMem(paddr_base:paddr, paddr_end:uint)
    requires paddr_base <= paddr_end
{
    !(
        is_mem_region_overlap(WK_ROMem_BasePAddr(), WK_ROMem_EndPAddr(), paddr_base, paddr_end) ||
        is_mem_region_overlap(WK_StackSeg_LimitPAddr(), WK_StackSeg_BasePAddr(), paddr_base, paddr_end) ||
        is_mem_region_overlap(WK_DATASeg_BasePAddr(), WK_DATASeg_EndPAddr(), paddr_base, paddr_end)
    )
}




/*********************** WK Kernel Memory Layout - Segments for x86 platform ********************/
//////////////////////// WK's Read-Only Memory (Code and ROData Seg)  ////////////////////////
// [Assumption] WK loader must fit WK's Read-only memory in WK's vaddr space 
const WK_ROMem_NPAGES:int := 1024;
const WK_ROMem_SZ:int := WK_ROMem_NPAGES * PAGE_4K_SZ;

// [Loader] Axiom (well known): we don't know where the WK's CODE segment is exactly, but the stack must fit in WK's address space
function {:axiom} WK_ROMem_Base() : (addr:vaddr)
    ensures PageAligned(addr)
    ensures WK_KERN_BASE <= addr <= ADDR_SPACE_UPPER - WK_ROMem_SZ
        // Property: this region must be in WK's vaddr space

function WK_ROMem_End() : (addr:vaddr)
    ensures PageAligned(addr)
    ensures WK_KERN_BASE <= addr <= ADDR_SPACE_UPPER
        // Property: this region must be in WK's vaddr space 
{
    Lemma_NTimesPage4KSZIsPageAligned(WK_ROMem_NPAGES);
    var addr1 := PageAlignedAdd(WK_ROMem_Base(), WK_ROMem_SZ);
    
    lemma_PageAlignedImpliesUInt32Aligned(addr1);
    assert is_valid_vaddr(addr1);
    addr1
}

predicate IsAddrInROMem(addr:vaddr)
{
    WK_ROMem_Base() <= addr < WK_ROMem_End()
}

// [Loader] Axiom (well known): WK loader provides a 1:1 mapping for WK's Read-only memory
function {:axiom} WK_ROMem_VtoPoffset() : (offset:int)
    ensures ADDR_SPACE_LOWER - WK_ROMem_Base() <= offset < ADDR_SPACE_UPPER - WK_ROMem_End()

function WK_ROMem_VAddrToPAddr(addr:vaddr) : (paddr:paddr)
    requires WK_ROMem_Base() <= addr < WK_ROMem_End()
    ensures ADDR_SPACE_LOWER <= paddr < ADDR_SPACE_UPPER
{
    addr + WK_ROMem_VtoPoffset()
}

// The paddr of the start and end (exclusive) of the ROMem
function WK_ROMem_BasePAddr() : (addr:paddr)
    ensures ADDR_SPACE_LOWER <= addr < ADDR_SPACE_UPPER 
{
    WK_ROMem_VAddrToPAddr(WK_ROMem_Base())
}

function WK_ROMem_EndPAddr() : (addr:paddr)
    ensures addr == WK_ROMem_BasePAddr() + WK_ROMem_SZ
    ensures ADDR_SPACE_LOWER <= addr < ADDR_SPACE_UPPER 
{
    reveal WordAligned();

    assert WK_ROMem_End() == WK_ROMem_Base() + WK_ROMem_SZ;
    WK_ROMem_VAddrToPAddr(WordAlignedSub(WK_ROMem_End(), ARCH_WORD_BYTES)) + ARCH_WORD_BYTES
}



//////////////////////// Stack ////////////////////////
const WK_STACK_NPAGES:int := 4;
const WK_STACK_SZ:int := WK_STACK_NPAGES * PAGE_4K_SZ;
const WK_STACK_FOR_EXTERNEL_FUNCS_SZ:int := 256 * ARCH_WORD_BYTES;

// [Loader] Axiom (well known): we don't know where the stack is exactly, but the stack must fit in WK's address space
function {:axiom} WK_StackSeg_Limit() : (addr:vaddr)
    ensures PageAligned(addr)
    ensures WK_KERN_BASE <= addr <= ADDR_SPACE_UPPER - WK_STACK_SZ
        // Property: this region must be in WK's vaddr space

function WK_StackSeg_Base() : (addr:vaddr)
    ensures PageAligned(addr)
    ensures WK_KERN_BASE <= addr <= ADDR_SPACE_UPPER
        // Property: this region must be in WK's vaddr space 
{
    Lemma_NTimesPage4KSZIsPageAligned(WK_STACK_NPAGES);
    var addr1 := PageAlignedAdd(WK_StackSeg_Limit(), WK_STACK_SZ);

    lemma_PageAlignedImpliesUInt32Aligned(addr1);
    assert is_valid_vaddr(addr1);
    addr1
}

// Interface Realization: <is_vaddr_in_stack>
predicate is_vaddr_in_stack(addr:addr)
{
    WK_StackSeg_Limit() <= addr < WK_StackSeg_Base()
}

// [Loader] Axiom (well known): WK loader provides a 1:1 mapping for WK's stack
function {:axiom} WK_StackReg_VtoPoffset() : (offset:int)
    ensures ADDR_SPACE_LOWER - WK_StackSeg_Limit() <= offset < ADDR_SPACE_UPPER - WK_StackSeg_Base()

function WK_StackSeg_VAddrToPAddr(addr:vaddr) : (paddr:paddr)
    requires is_vaddr_in_stack(addr)
    ensures ADDR_SPACE_LOWER <= paddr < ADDR_SPACE_UPPER
{
    addr + WK_StackReg_VtoPoffset()
}

// The paddr of the start and end (exclusive) of the Stack
function WK_StackSeg_LimitPAddr() : (addr:paddr)
    ensures ADDR_SPACE_LOWER <= addr < ADDR_SPACE_UPPER 
{
    WK_StackSeg_VAddrToPAddr(WK_StackSeg_Limit())
}

function WK_StackSeg_BasePAddr() : (addr:paddr)
    ensures addr == WK_StackSeg_LimitPAddr() + WK_STACK_SZ
    ensures ADDR_SPACE_LOWER <= addr < ADDR_SPACE_UPPER 
{
    WK_StackSeg_VAddrToPAddr(WK_StackSeg_Base() - ARCH_WORD_BYTES) + ARCH_WORD_BYTES
}




//////////////////////// Global Variables ////////////////////////
// [Assumption] WK loader must fit WK's DATA segment in WK's vaddr space 
const WK_DATA_NPAGES:int := 2000;
const WK_DATASeg_SZ:int := WK_DATA_NPAGES * PAGE_4K_SZ;

// [Loader] Axiom (well known): we don't know where the WK's data segment is exactly, but the data must fit in WK's address space
function {:axiom} WK_DataSeg_Base() : (addr:vaddr)
    ensures PageAligned(addr)
    ensures WK_KERN_BASE <= addr <= ADDR_SPACE_UPPER - WK_DATASeg_SZ

function WK_DataSeg_End() : (addr:vaddr)
    ensures PageAligned(addr)
    ensures WK_KERN_BASE <= addr <= ADDR_SPACE_UPPER 
        // Property: this region must be in WK's vaddr space 
{
    Lemma_NTimesPage4KSZIsPageAligned(WK_DATA_NPAGES);
    var addr1 := PageAlignedAdd(WK_DataSeg_Base(), WK_DATASeg_SZ);

    lemma_PageAlignedImpliesUInt32Aligned(addr1);
    assert is_valid_vaddr(addr1);
    addr1
}

predicate IsAddrInDataSeg(addr:vaddr)
{
    WK_DataSeg_Base() <= addr < WK_DataSeg_End()
}

// [Loader] Axiom (well known): WK loader provides a 1:1 mapping for WK's DATA segment
function {:axiom} WK_DATASeg_VtoPoffset() : (offset:int)
    ensures ADDR_SPACE_LOWER - WK_DataSeg_Base() <= offset < ADDR_SPACE_UPPER - WK_DataSeg_End()

function WK_DATASeg_VAddrToPAddr(addr:vaddr) : (paddr:paddr)
    requires WK_DataSeg_Base() <= addr < WK_DataSeg_End()
    ensures ADDR_SPACE_LOWER <= paddr < ADDR_SPACE_UPPER
{
    addr + WK_DATASeg_VtoPoffset()
}

// The paddr of the start and end (exclusive) of the DATA segment
function WK_DATASeg_BasePAddr() : (addr:paddr)
    ensures ADDR_SPACE_LOWER <= addr < ADDR_SPACE_UPPER 
{
    WK_DATASeg_VAddrToPAddr(WK_DataSeg_Base())
}

function WK_DATASeg_EndPAddr() : (addr:paddr)
    ensures addr == WK_DATASeg_BasePAddr() + WK_DATASeg_SZ
    ensures ADDR_SPACE_LOWER <= addr < ADDR_SPACE_UPPER 
{
    assert WK_DataSeg_End() == WK_DataSeg_Base() + WK_DATASeg_SZ;
    WK_DATASeg_VAddrToPAddr(WK_DataSeg_End() - ARCH_WORD_BYTES) + ARCH_WORD_BYTES
}




/*********************** Interface Realization ********************/
// Interface realization: <stack_under_sp_is_unchanged>
// Do the two WK's machine states have same stack content below the current sp 
predicate stack_under_sp_is_unchanged(mem1:wk_memmap, mem2:wk_memmap, sp:vaddr)
    requires x86wk_valid_memstate(mem1)
    requires x86wk_valid_memstate(mem2)
    requires is_vaddr_in_stack(sp)
{
    reveal x86wk_valid_memstate();
    assert MapGetKeys(mem1) == MapGetKeys(mem2);

    (forall addr:vaddr :: is_vaddr_in_stack(addr) && addr >= sp
        ==> mem1[addr] == mem2[addr])
}

predicate stack_is_unchanged(mem1:wk_memmap, mem2:wk_memmap)
    requires x86wk_valid_memstate(mem1)
    requires x86wk_valid_memstate(mem2)

    ensures stack_is_unchanged(mem1, mem2) 
                ==> (forall sp:vaddr :: is_vaddr_in_stack(sp) ==> stack_under_sp_is_unchanged(mem1, mem2, sp))
{
    mem1 == mem2
}

// Interface realization: <stack_get_val>
// Read stack value at a word-aligned vaddr
function stack_get_val(m:wk_memmap, a:vaddr) : word
    requires x86wk_valid_memstate(m)

    requires WK_Mem_Separate_Segs()
    requires WK_ValidMemForRead(a)
{
    reveal x86wk_valid_memstate();
    m[a]
}

// Interface realization: <stack_get_val_vaddr32>
// Read stack value at a 32bit-aligned vaddr
function stack_get_val_vaddr32(m:wk_memmap, a:addr) : word
    requires x86wk_valid_memstate(m)

    requires WK_Mem_Separate_Segs()
    requires WK_ValidMemForRead(a)

    requires UInt32Aligned(a)
{
    stack_get_val(m, a)
}

// Interface realization: <stack_get_val_uint64>
// Read stack value at a word-aligned vaddr
function stack_get_val_uint64(m:wk_memmap, a:addr) : uint64
    requires x86wk_valid_memstate(m)

    requires WK_Mem_Separate_Segs()
    requires WK_ValidMemForRead(a)
    requires WK_ValidMemForRead(a + UINT32_BYTES)

    requires UInt32Aligned(a)
{
    var low := stack_get_val_vaddr32(m, a);
    var high := stack_get_val_vaddr32(m, a + UINT32_BYTES);
    UInt64_FromTwoUInt32s(high, low)
}

// Interface realization: <stack_set_val>
function stack_set_val(m:wk_memmap, a:vaddr, v:word) : wk_memmap
    requires x86wk_valid_memstate(m)

    requires WK_Mem_Separate_Segs()
    requires WK_ValidMemForWrite(a)

    ensures x86wk_valid_memstate(stack_set_val(m, a, v))
{
    reveal x86wk_valid_memstate();
    
    m[a := v]
}

// Interface realization: <wkm_stack_get_val>
function wkm_stack_get_val(s:WK_MState, m:vaddr): word
    requires x86wk_valid_memstate(s.m)

    requires WK_Mem_Separate_Segs()
    requires WK_ValidMemForRead(m)
{
    reveal x86wk_valid_memstate();
    //reveal WK_ValidMemForRead();
    
    stack_get_val(s.m, m)
}

// Interface realization: <wkm_stack_get_all>
// Return the entire stack in <s>
function wkm_stack_get_all(s:WK_MState) : wk_memmap
{
    s.m
}