// REQUIRES-ANY: TEST, UTIL
// RUN: %DAFNY /compile:0 %s %DARGS

include "bitvectors.s.dfy"  // For the definition of uint32
type byte = i | 0 <= i < 256

// Map an arbitrary number of bytes to an integer
function BEByteSeqToInt(bytes:seq<byte>) : int
    decreases |bytes|;
{
    if bytes == [] then 0
    else BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + (bytes[|bytes|-1] as int)
}

// Map a big-endian integer to a sequence of bytes
function BEUintToSeqByte(v:int, width:int) : seq<byte>
    ensures width >= 0 && v >= 0 ==> |BEUintToSeqByte(v, width)| == width;
{
    if width > 0 && v >= 0 then
        BEUintToSeqByte(v/0x100, width - 1) + [ (v % 0x100) as byte ]
    else
        []
}

function {:opaque} BytesToUInt32(b0:byte, b1:byte, b2:byte, b3:byte) : uint32
{
    assert{:fuel BEByteSeqToInt, 4} 0 <= BEByteSeqToInt([b0, b1, b2, b3]) < 0x1_0000_0000;
    BEByteSeqToInt([b0, b1, b2, b3])
}

function{:opaque} UInt32ToBytes(w:uint32) : seq<byte>
    ensures |UInt32ToBytes(w)| == 4;
{
    BEUintToSeqByte(w as int, 4)
//    [ byte( w/ 0x1000000),
//      byte((w/   0x10000) % 256),
//      byte((w/     0x100) % 256),
//      byte(w              % 256) ]
}

function {:opaque} Uint64ToBytes(u:uint64) : seq<byte>
    ensures |Uint64ToBytes(u)| == 8;
{
    BEUintToSeqByte(u as int, 8)
//    [ ( u/ 0x100000000000000) as byte,
//      ((u/   0x1000000000000) % 0x100) as byte,
//      ((u/     0x10000000000) % 0x100) as byte,
//      ((u/       0x100000000) % 0x100) as byte,
//      ((u/         0x1000000) % 0x100) as byte,
//      ((u/           0x10000) % 0x100) as byte,
//      ((u/             0x100) % 0x100) as byte,
//      ((u                   ) % 0x100) as byte]
}

function UInt32SeqToBytes(ws:seq<uint32>) : seq<byte>
    ensures |UInt32SeqToBytes(ws)| == |ws| * 4;
    //ensures var bytes := UInt32SeqToBytes(ws); forall i :: 0 <= i < |ws| ==> bytes[i*4..(i+1)*4] == UInt32ToBytes(ws[i]);
{
    if |ws| == 0 then [] else UInt32ToBytes(ws[0]) + UInt32SeqToBytes(ws[1..])
}

function RepeatByte(b:byte, count:int) : seq<byte>
    requires count >= 0;
    ensures  |RepeatByte(b, count)| == count;
    ensures  forall x :: x in RepeatByte(b, count) ==> x == b;
{
    if count == 0 then [] else RepeatByte(b, count-1) + [b]
}

function RepeatValue<T>(n:T, count:int) : seq<T>
    requires count >= 0;
    ensures  |RepeatValue(n, count)| == count;
    ensures  forall x :: x in RepeatValue(n, count) ==> x == n;
{
    if count == 0 then [] else RepeatValue(n, count-1) + [n]
}

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
{
    if |ss| == 0 then [] else ss[0] + ConcatenateSeqs(ss[1..])
}

function bswap32(x:uint32) : uint32
{
    var bytes := UInt32ToBytes(x);
    BytesToUInt32(bytes[3], bytes[2], bytes[1], bytes[0])
}

