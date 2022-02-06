include "types.s.dfy"
include "bitvectors.s.dfy"

type shift_amount = s | 0 <= s < 32 // Some shifts allow s=32, but we'll be conservative for simplicity

//-----------------------------------------------------------------------------
// Functions for bitwise operations
//-----------------------------------------------------------------------------

function BitwiseXor(x:uint32, y:uint32): uint32
    { BitsAsUInt32(BitXor(UInt32AsBits(x), UInt32AsBits(y))) }

function BitwiseAnd(x:uint32, y:uint32): uint32
    { BitsAsUInt32(BitAnd(UInt32AsBits(x), UInt32AsBits(y))) }

function BitwiseOr(x:uint32, y:uint32): uint32
    { BitsAsUInt32(BitOr(UInt32AsBits(x), UInt32AsBits(y))) }

function BitwiseNot(x:uint32): uint32
    { BitsAsUInt32(BitNot(UInt32AsBits(x))) }

function LeftShift(x:uint32, amount:uint32): uint32
    requires 0 <= amount < 32;
    { BitsAsUInt32(BitShiftLeft(UInt32AsBits(x), amount)) }

function RightShift(x:uint32, amount:uint32): uint32
    requires 0 <= amount < 32;
    { BitsAsUInt32(BitShiftRight(UInt32AsBits(x), amount)) }

function RotateRight(x:uint32, amount:shift_amount): uint32
    requires 0 <= amount < 32;
    { BitsAsUInt32(BitRotateRight(UInt32AsBits(x), amount)) }

function {:opaque} UpdateTopBits(origval:uint32, newval:uint32): uint32
{
    BitwiseOr(LeftShift(newval, 16), BitwiseMaskLow(origval, 16))
}




/*********************** Flags Operations ********************/
// Predicate: Return if the value <v> has the bit at <bit_pos> set
predicate TestBit(v:uint32, bit_pos:uint32)
    requires 0 <= bit_pos < 32
{
    var flag_v := LeftShift(1, bit_pos);
    var result := BitwiseAnd(v, flag_v);

    if(result != 0) then
        true
    else
        false
}

// Set a bit to value <v>
function SetBit(v:uint32, bit_pos:uint32) : uint32
    requires 0 <= bit_pos < 32
{
    var flag_v := LeftShift(1, bit_pos);

    BitwiseOr(v, flag_v)
}

// Clear a bit to value <v>
function ClearBit(v:uint32, bit_pos:uint32) : uint32
    requires 0 <= bit_pos < 32
{
    var flag_v := LeftShift(1, bit_pos);
    var flag_v2 := BitwiseNot(flag_v);
    
    BitwiseAnd(v, flag_v2)      // v == v & flag_v2 == v & ~(1 << bit_pos)
}