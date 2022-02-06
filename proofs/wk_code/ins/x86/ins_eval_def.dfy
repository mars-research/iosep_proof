include "../../utils/common/headers.dfy"
include "../../arch/headers.dfy"

datatype Shift = LSLShift(amount_lsl:shift_amount)
               | LSRShift(amount_lsr:shift_amount)
               | RORShift(amount_ror:shift_amount)

datatype maddr = MConst(n:word) | 
                 MReg(reg:x86Reg, offset:word)

datatype operand = OConst(n:word) 
                 | OReg(r:x86Reg) 
                 | OSReg(sr:SReg) // special regs
                 | OMAddr(addr:maddr)
                 | OErr