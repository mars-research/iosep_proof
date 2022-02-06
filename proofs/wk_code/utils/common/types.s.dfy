//-----------------------------------------------------------------------------
// Core types
//-----------------------------------------------------------------------------
const TRUE:int := 1;
const FALSE:int := 0;

const UINT16_LIM:int := 0x1_0000;
const UINT32_BYTES:int := 4;
const UINT32_BITS:int := 32;
const UINT32_LIM:int := 0x1_0000_0000;
const UINT64_LIM:int := 0x1_0000_0000_0000_0000;

const PAGE_4K_SZ:int := 0x1000;

type uint7 = x | 0 <= x < 128
type uint11 = x | 0 <= x < 2048

type uint16 = x | isUInt16(x)
type uint32 = x:int | isUInt32(x)
type uint64 = x | isUInt64(x)
type size = x | isUInt32(x)
type uint = x | x >= 0






/*********************** Utility Functions ********************/
predicate isUInt16(i:int) { 0 <= i < UINT16_LIM }
predicate isUInt32(i:int) { 0 <= i < UINT32_LIM }
predicate isUInt64(i:int) { 0 <= i < UINT64_LIM }

function {:opaque} TruncateUInt32(x:int): uint32
{ x % UINT32_LIM }

function {:opaque} TruncateUInt64(x:int): uint64
{ x % UINT64_LIM }

// [Hack] Use div instead of shift, because Dafny does not support shift for int
function method UInt64High(i:uint64) : uint32
{
    i / UINT32_LIM
}

function method UInt64Low(i:uint64) : uint32
{
    i % UINT32_LIM
}

function method UInt64_FromTwoUInt32s(high:uint32, low:uint32) : (v:uint64)
    ensures UInt64Low(v) == low
    ensures UInt64High(v) == high
{
    high * 0x1_0000_0000 + low
}

predicate {:opaque} UInt32Aligned(i:int) { i % UINT32_BYTES == 0 }
function method UInt32sToBytes(w:int): int
    ensures UInt32Aligned(UInt32sToBytes(w))
{ reveal UInt32Aligned(); UINT32_BYTES * w }

function method BytesToUInt32s(b:int): int
    requires UInt32Aligned(b)
{ reveal UInt32Aligned(); b / UINT32_BYTES }


const PAGESIZE:int := 0x1000;
const PAGEBITS:int := 12;

predicate {:opaque} PageAligned(addr:int)
    requires addr >= 0
    ensures PageAligned(addr) ==> UInt32Aligned(addr)
{
    if addr % PAGESIZE == 0
    then lemma_PageAlignedImpliesUInt32Aligned(addr); true
    else false
}



lemma lemma_PageAlignedImplies1KAligned(addr:int)
    requires addr >= 0 && addr % 0x1000 == 0
    ensures addr % 0x400 == 0
{ assert 0x1000 % 0x400 == 0; }

lemma lemma_1KAlignedImpliesUInt32Aligned(addr:int)
    requires addr >= 0 && addr % 0x400 == 0
    ensures UInt32Aligned(addr)
{
    calc {
        true;
        addr % 0x400 == 0;
        addr % 0x200 == 0;
        addr % 0x100 == 0;
        addr % 0x80 == 0;
        addr % 0x40 == 0;
        addr % 0x20 == 0;
        addr % 0x10 == 0;
        addr % 8 == 0;
        addr % 4 == 0;
        { reveal UInt32Aligned(); }
        UInt32Aligned(addr);
    }
}

lemma lemma_PageAlignedImpliesUInt32Aligned(addr:int)
    requires addr >= 0 && addr % 0x1000 == 0
    ensures UInt32Aligned(addr)
{
    lemma_PageAlignedImplies1KAligned(addr);
    lemma_1KAlignedImpliesUInt32Aligned(addr);
}



function PageAlignedAdd(x1:int, x2:int): int
    requires x1 > 0 && x2 > 0
    requires PageAligned(x1)
    requires PageAligned(x2)
    ensures PageAlignedAdd(x1, x2) > 0
    ensures  PageAligned(PageAlignedAdd(x1, x2))
{
    reveal PageAligned();
    x1 + x2
}

function PageAlignedSub(x1:int, x2:int): int
    requires x1 > x2 > 0
    requires PageAligned(x1) && PageAligned(x2)
    ensures PageAlignedSub(x1, x2) > 0
    ensures  PageAligned(PageAlignedSub(x1, x2))
{
    reveal PageAligned();
    x1 - x2
}


