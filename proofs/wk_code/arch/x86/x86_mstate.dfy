include "../../utils/common/headers.dfy"
include "x86_types.dfy"

/*********************** Interface Realizations ********************/
// Interface realization: <AddrRef_Objs>
// All I/O objects that can be referenced by addresses defined by CPU architectures (i.e., memory addresses, PIO addresses) 
datatype AddrRef_Objs = AddrRef_Objs(
                        m:memmap,     // Physical memory address space of ALL I/O objects; i.e., accessed by PAddr
                        pio:iomap     // Port I/O (PIO) address space of ALL I/O objects; i.e., accessed by PIO addr
                    )


// Interface realization: <WK_MState>
datatype WK_MState = WK_MState(
                        // Registers used by WK
                        // [Assumption] OS and wimp apps cannot break the integrity of these registers, during WK's 
                        // execution. Secrecy of these registers are not needed, because these registers are not 
                        // I/O objects. In a common case, WK's registers should be isolated from OS and wimp apps
                        //
                        // [NOTE-Interesting observations][Section T.1] In fact, WK and wimp apps share these registers,   
                        // and wimp apps can arbitarily write to general registers before calling WK for I/O service. 
                        // When called by wimp apps, WK does not need to do context switch for I/O separation (if 
                        // general registers are not I/O objects). This is because WK is event-triggered; i.e., invoked  
                        // via WK APIs. Context switches are for correct execution of wimp apps. 
                        regs:map<x86Reg, word>,
                        sregs:map<SReg, word>,

                        // Physical memory address space of WK (I/O separation part) code, stack, global variables
                        // [Property] WK's code is unchanged all the time (in all transitions)
                        m:wk_memmap,
                        globals:globalsmap // Global variables of WK
                    )




/*********************** Specific x86 Machine State - Registers ********************/
datatype x86Reg = EAX|EBX|ECX|EDX|ESI|EDI|ESP|EBP

// Special register instruction operands
datatype SReg = EFLAGS




/*********************** Specific x86 Machine State - Memory ********************/
type wk_memmap = map<vaddr, word> // For performance consideration of WK

// Define the type for global variables
type symbol = string
type globalsmap = map<symbol, seq<word>>

// The state of memory at given address
// [NOTE] On x86 platforms, addresses in memory accesses can be unaligned 
type memmap = map<paddr, byte> // To be compatible with OS
type iomap = map<ioaddr, word>