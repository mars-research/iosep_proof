include "../../utils/common/headers.dfy"

/*********************** Interface Realizations ********************/
// Interface realization: <ARCH_WORD_BYTES>
const ARCH_WORD_BYTES:int := 4; // [NOTE] We redefine WORD on x86 platforms. WORD is always 32-bit, instead of 16-bit

// Interface realization: <ARCH_ADDR_BYTES>
const ARCH_ADDR_BYTES:int := 4; // Each address takes four bytes

// Interface realization: <ARCH_WORD_LIMIT>
const ARCH_WORD_LIMIT:int := UINT32_LIM;

// Interface realization: <ARCH_WORD_BYTES_MULTIPLY_SHIFT_BITS>
// Whenever a value needs to multiply by ARCH_WORD_BYTES, it can shift by ARCH_WORD_BYTES_MULTIPLY_SHIFT_BITS instead
const ARCH_WORD_BYTES_MULTIPLY_SHIFT_BITS := 2; 

// Interface realization: <addr>
type addr = x:int | is_valid_addr(x)

// Interface realization: <vaddr>
// vaddr is used by WK only, so WK requires vaddr to be word aligned (e.g., for better performance on x86)
//type vaddr = x:int | (reveal WordAligned(); isUInt32(x) && WordAligned(x)) ghost witness addr_witness()
type vaddr = x:addr | (WordAligned_Revealed(x))

// Interface realization: <paddr>
// paddr is used by WK, OS, and SecApps, so WK does not require paddr to be word aligned
type paddr = addr

// Interface realization: <vaddr32>
type vaddr32 = x:addr | (UInt32Aligned_Revealed(x))

// Interface realization: <word>
type word = uint32 // [NOTE] We redefine the term Word. Now a word is always 32-bit, instead of 16-bit

// Interface realization: <isWord>
predicate isWord(a:int)
{
    isUInt32(a)
}

// Interface realization: <TruncateWord>
function TruncateWord(x:int): word
{ TruncateUInt32(x) }

// Interface realization: <is_valid_addr>
predicate is_valid_addr(a:int)
{
    isUInt32(a)
}


// Interface realization: <is_valid_vaddr>
predicate is_valid_vaddr(a:addr)
{
    reveal WordAligned();
    WordAligned(a)
}




/*********************** Other Definitions ********************/
const X86_WORD_MAX:int := 0x1_0000_0000;
const IO_LIM:int := 65536;



type ioaddr = x | (isIOPort(x))




predicate isIOPort(i:int) { 0 <= i < IO_LIM }


function WordToAddr(i:word):addr
{
    i as addr
}

predicate {:opaque} WordAligned(i:int) 
{
    UInt32Aligned(i)
}
function method WordsToBytes(w:int): int
    ensures WordAligned(WordsToBytes(w))
{ 
    reveal WordAligned();
    UInt32sToBytes(w)
}

function method BytesToWords(b:int): int
    requires WordAligned(b)
{ 
    reveal WordAligned();
    BytesToUInt32s(b)
}

// Interface realization: <WordAlignedAdd>
function WordAlignedAdd(x1:int, x2:int): int
    requires WordAligned(x1)
    requires WordAligned(x2)
    ensures  WordAligned(WordAlignedAdd(x1, x2))
{
    reveal WordAligned();
    UInt32AlignedAdd(x1, x2)
}

// Interface realization: <WordAlignedSub>
function WordAlignedSub(x1:int, x2:int): int
    requires WordAligned(x1)
    requires WordAligned(x2)
    ensures  WordAligned(WordAlignedSub(x1, x2))
{
    reveal WordAligned();
    UInt32AlignedSub(x1, x2)
}

// Interface realization: <WordAlignedMul>
function WordAlignedMul(x1:word, N:int): word
    requires WordAligned(x1)
    requires N >= 0
    requires isUInt32(x1 * N)

    ensures WordAligned(WordAlignedMul(x1, N))
    ensures WordAlignedMul(x1, N) == x1 * N
{
    reveal WordAligned();
    UInt32AlignedMul(x1, N)
}




/*********************** Private functions ********************/
predicate WordAligned_Revealed(x:int)
{
    reveal UInt32Aligned();
    UInt32Aligned(x)
}

predicate UInt32Aligned_Revealed(x:int)
{
    reveal UInt32Aligned();
    UInt32Aligned(x)
}