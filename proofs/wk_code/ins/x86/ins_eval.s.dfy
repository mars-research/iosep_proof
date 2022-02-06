include "../../mm/headers.dfy"
include "../../state.dfy"
include "../../state_properties_validity.s.dfy"
include "ins_eval_def.dfy"
include "../../state_utils.s.dfy"

include "../../partition_id.i.dfy"
include "../util/ffi.i.dfy"
include "../../dev/usb2/ffi/usb_tds.ffi.i.dfy"
include "../../dev/usb2/ffi/ehci.ffi.i.dfy"
include "../../dev/usb2/ffi/usbpdev.ffi.i.dfy"
include "../../drv/drv.ffi.i.dfy"
include "../../mhv/mhv.ffi.i.dfy"

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
datatype ins = 
 MOV(dst:operand, src:operand)
| ADD(dst:operand, src:operand)
| SUB(dst:operand, src:operand)
| MUL(src:operand)
| AND(dst:operand, src:operand)
| OR(dst:operand, src:operand)
| XOR(dst:operand, src:operand)
| NOT(dst:operand)
| MOV_reloc(dst:operand, global:symbol) //from Komodo
| LDR_global(dst:operand, global:symbol,  //from Komodo
                base:operand, ofs:operand)
| STR_global(src:operand, global:symbol,
                base:operand, ofs:operand)
| PUSH(src:operand)
| POP(dst:operand)
| SHL(dst:operand, src:operand)
| SHR(dst:operand, src:operand)
/*| CALL(src:operand) 
| JMP_Ret3 (src:operand)    // Jump to external functions, which return three words on stack */
| CALL_EEHCI_Activate()     // Input parameters are on stack, if any
| CALL_EEHCI_Deactivate()     // Input parameters are on stack, if any
| CALL_EEHCI_FIND_RefToUSBTD()
| CALL_USBTD_QTD32_ParseTDPointers() // Call to usbtd_qtd32_parseQTDpointer_stub
| CALL_USBTD_QTD32_ParseBufPointers() // Call to usbtd_qtd32_parseBufpointer_stub
| CALL_USBTD_QH32_ParseTDPointers() // Call to usbtd_qh32_parseQTDpointer_stub
| CALL_USBTD_QH32_ParseBufPointers() // Call to usbtd_qh32_parseBufpointer_stub
| CALL_USBTD_QH32_ParseTargetUSBDevID() // Call to usbtd_qh32_parseTargetUSBDevID_stub
| CALL_USBTD_Copy_From_User()
| CALL_USBTD_CheckNotModifyUSBPDevAddrs()
| CALL_USBTD_Backup()
| CALL_USBTD_Restore()
| CALL_USBTD_IsRefTargetUSBTD()
| CALL_USBTD_Clear_Content()
| CALL_WimpDrv_DO_Clear()
| CALL_WimpDrv_CheckDOPAddrRange()
| CALL_PMem_AssignToWimps()
| CALL_PMem_ReleaseFromWimps()
| CALL_PMem_ActivateInOS()
| CALL_PMem_DeactivateFromOS()
| CALL_USBPDev_Clear()
| CALL_PEHCI_ActivateInOS()
| AXIOM_Assign_USBPDevs_To_OS_Partition()
// For debug purpose
//| CALL_DEBUG()

/*| IN(dst:operand, src:operand)
| OUT(dst:operand, src:operand)
| VMCALL(leaf:operand, arg0:operand, arg1:operand, 
         arg2:operand, arg3:operand, bdf:operand)*/

//-----------------------------------------------------------------------------
// Code Representation
//-----------------------------------------------------------------------------
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt //CCH: should we also use OTstEq | OTstNe as in Komodo?
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)




/*********************** Evaluation ********************/
predicate WK_evalGlobalUpdate(s:state, g:symbol, offset:word, v:word, r:WK_MState)
    requires ValidState(s)
    requires ValidGlobalOffset(g, offset)
    requires ins_valid_strglobal_word(s.subjects, s.objects, s.id_mappings, s.objs_addrs, s.activate_conds, 
                wkm_get_globals(s.wk_mstate), g, AddressOfGlobal(g) + offset, v)
    ensures WK_evalGlobalUpdate(s, g, offset, v, r) ==> 
                (WK_ValidMState(r) && 
                (gvar_read_word_byoffset(r, g, offset) == v))
{
    reveal WK_ValidGlobalVars_Decls();

    var oldval := s.wk_mstate.globals[g];
    var newval := oldval[BytesToWords(offset) := v];
    assert |newval| == |oldval|;
    var new_s:WK_MState := s.wk_mstate.(globals := s.wk_mstate.globals[g := newval]);

    (r == new_s)
}

predicate WK_evalMemUpdate(s:WK_MState, m:vaddr, v:word, r:WK_MState)
    requires WK_ValidMState(s)
    requires WK_ValidMemVAddr(m)
    ensures WK_evalMemUpdate(s, m, v, r) ==> WK_ValidMState(r)
{
    reveal x86wk_valid_memstate();

    // store updates memory
    var d := (r == s.(m := s.m[m := v]));

    if(d) then
        Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        d
    else
        d
}

function evalCmp(c:ocmp, i1:word, i2:word):bool
{   
  match c
    case OEq => i1 == i2
    case ONe => i1 != i2
    case OLe => i1 <= i2
    case OGe => i1 >= i2
    case OLt => i1 <  i2
    case OGt => i1 >  i2
//    case OTstEq => BitwiseAnd(i1, i2) == 0
//    case OTstNe => BitwiseAnd(i1, i2) != 0
}

function evalOBool(wkm:WK_MState, o:obool):bool
    requires WK_ValidMState(wkm)
    requires ins_valid_opr_bool(wkm, o.o1)
    requires ins_valid_opr_bool(wkm, o.o2) 
{
    evalCmp(o.cmp, OperandContents(wkm, o.o1), OperandContents(wkm, o.o2))
}

predicate evalGuard(s:state, r:state) // [TODO] Need revise
    requires ValidState(s)
    requires Valid_WKMachineState_Arch(s.wk_mstate) && !interrupts_enabled(x86_get_eflags(s.wk_mstate))
{
    // this is where we would havoc flags for comparisons, if we modelled them
    //maybeHandleInterrupt(s, r)
    s == r
}

function EvalShift(w:word, shift:Shift) : word
{
    match shift
        case LSLShift(amount) => LeftShift(w, amount)
        case LSRShift(amount) => RightShift(w, amount)
        case RORShift(amount) => RotateRight(w, amount)
}

function OperandContents(wkm:WK_MState, o:operand): word
    requires WK_ValidMState(wkm)
    requires ins_valid_opr(wkm, o)
{
    match o
        case OConst(n) => n
        case OReg(r) => wkm.regs[r] 
        case OSReg(sr) => wkm.sregs[sr]
        case OMAddr(addr) => eval_val_at_maddr(wkm, addr) 
}

// Get the value in <addr>
// [NOTE] This function returns type addr but not vaddr, because vaddr must be aligned address
function eval_maddr(wkm:WK_MState, addr:maddr) : addr
    requires Valid_WKMachineState_Arch(wkm)

    ensures addr.MReg? && ( 0 <= (x86_get_reg(wkm, addr.reg) + addr.offset) < UINT32_LIM)
                ==> eval_maddr(wkm, addr) == (x86_get_reg(wkm, addr.reg) + addr.offset)
        // Property: If the reg-based address with offset is less than UINT32_LIM, then the result is just their sums
{
    reveal TruncateUInt32(); // Need to reveal it, so the verifier know that 
    match addr
        case MConst(n) => n
        case MReg(r, offset) => WordToAddr(TruncateWord(x86_get_reg(wkm, r) + offset))
}

// Get the memory content refed by <addr>
function eval_val_at_maddr(wkm:WK_MState, addr:maddr) : word
    requires WK_ValidMState(wkm)
    requires ins_valid_maddr(wkm, addr)
{
    var resolved_addr := eval_maddr(wkm, addr);
    wkm_stack_get_val(wkm, resolved_addr)
}




/*********************** Validity of Operands ********************/
// If the encapsulated <addr> refs WK's memory of wkm.m
predicate ins_valid_maddr(wkm:WK_MState, addr:maddr)
    requires WK_ValidMState(wkm)
{
    var resolved_addr := eval_maddr(wkm, addr);
    is_valid_vaddr(resolved_addr) && WK_ValidMemVAddr(resolved_addr)
}

// If the encapsulated <addr> refs a readable WK's memory of wkm.m
predicate ins_valid_maddr_memread(wkm:WK_MState, addr:maddr)
    requires WK_ValidMState(wkm)
{
    var resolved_addr := eval_maddr(wkm, addr);
    is_valid_vaddr(resolved_addr) && WK_ValidMemForRead(resolved_addr)  
}

// Is the instruction operand <o> valid?
predicate ins_valid_opr(wkm:WK_MState, o:operand)
    requires WK_ValidMState(wkm)
{
    match o
        case OConst(n) => true
        case OReg(r) => is_exist_x86_reg(wkm.regs, r)
        case OSReg(sr) => is_exist_x86_sreg(wkm.sregs, sr)
        case OMAddr(addr) => ins_valid_maddr(wkm, addr)
        case OErr => false
}

// Is the instruction operand <o> a valid source operand?
predicate ins_valid_src_opr(wkm:WK_MState, o:operand)
    requires WK_ValidMState(wkm)
{
    ins_valid_opr(wkm, o)
}

// Is the instruction operand <o> a valid destination operand?
predicate ins_valid_dst_opr(wkm:WK_MState, o:operand)
    requires WK_ValidMState(wkm)
{
    ins_valid_opr(wkm, o) &&
    (
        match o
            case OConst(n) => false
            case OReg(r) => is_exist_x86_reg(wkm.regs, r)
            case OSReg(sr) => is_exist_x86_sreg(wkm.sregs, sr)
            case OMAddr(addr) => ins_valid_maddr(wkm, addr)
    )
}

// Is the instruction operand <o> a register operand?
predicate ins_is_reg_opr(o:operand)
{ 
    o.OReg? 
}

// Is the instruction operand <o> a SReg operand?
predicate ins_is_sreg_opr(o:operand)
{ 
    o.OSReg?
}

// Is the instruction operand <o> a const operand?
predicate ins_is_const_opr(o:operand)
{ 
    o.OConst? 
}

// Is the instruction operand <o> a memory operand?
predicate ins_is_mem_opr(o:operand)
{ 
    o.OMAddr?
}

predicate ins_valid_opr_bool(wkm:WK_MState, o:operand)
    requires WK_ValidMState(wkm)
{
    ins_valid_opr(wkm, o) && !ins_is_sreg_opr(o)
}

predicate ins_valid_opr_shift(wkm:WK_MState, o:operand)
    requires WK_ValidMState(wkm)
{
    ins_valid_opr(wkm, o) && 
    (o.OConst? || o == OReg(ECX)) &&
    (OperandContents(wkm, o) < ARCH_Ins_SHIFT_MAX) // ARCH_Ins_SHIFT_MAX = 32
}

// Is the new value of the register/memory valid
predicate ins_valid_new_dst_opr_value(s:WK_MState, o:operand, v:word)
    requires WK_ValidMState(s)
    requires ins_valid_dst_opr(s, o)
{
    match o
       // case OConst(n) => false
        case OReg(reg) => 
            var r := s.(regs := s.regs[o.r := v]);
            (
                if (reg == ESP) then 
                    var addr := x86_get_reg(r, ESP);
                    IsAddrInStack(addr)  // The new ESP value must point to WK's stack
                else true
            )
                        
        case OSReg(sr) => true        
        case OMAddr(addr) => true
}

// Is the new value of the global variable satisfies <WK_ValidGlobalVars_Vals>
predicate ins_valid_strglobal_word(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, 
    objs_addrs:WSM_Objects_Addrs, activate_conds:WSM_Dev_Activate_Conditions,
    gm: globalsmap, g:symbol, addr:vaddr, v:word
)
    requires WK_ValidGlobalVars_Decls(gm)
    requires WK_WimpDrvs_ValidGlobalVarValues_PIDs(gm)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjsAddrs(objs, objs_addrs, gm)

    requires is_gvar_valid_vaddr(g, addr)
{
    reveal WK_ValidGlobalVars_Decls();
    reveal WK_ValidObjsAddrs();

    var new_globals := global_write_word(gm, g, addr, v);

    // 1. The value of <g_eehci_mem_pbase> is never changed
    g != G_EEHCI_MEM_PBASE() &&
    // 2. New values of global variables must satisfy the SIs defined in WK_ValidGlobalVars_Vals
    WK_ValidGlobalVars_Vals(new_globals) &&
    // 3. New values of global variables must match additional SIs related between global variables and <objs_addrs>
    WK_ValidObjAddrs_WimpDrv_DOPAddrs(subjs, objs, id_mappings, objs_addrs, new_globals) &&
    // 4. New values of global variables must satisfy WK_ValidGlobalVarValues_USBPDevs
    WK_ValidGlobalVarValues_USBPDevs(subjs, new_globals) &&
    // 5. The value of <g_wimpdevs_devlist> is never changed
    g != G_WimpUSBPDev_DevList() &&
    // 6. Physical EHCIs for wimp devices must always be inactive
    WSM_physical_EHCIs_must_be_inactive(subjs, activate_conds) &&

    (true)
}

// Predicate: Physical EHCIs for wimp devices must always be inactive
// [NOTE] They don't need to be all physical EHCIs in the system, but only those will map to ephemeral EHCIs
predicate {:opaque} WSM_physical_EHCIs_must_be_inactive(
    subjs:WSM_Subjects, activate_conds:WSM_Dev_Activate_Conditions
)
{
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond
        ==> dev_id in subjs.os_devs) &&
    (forall dev_id :: dev_id in activate_conds.ehci_activate_cond
        ==> SubjPID_OSDev(subjs, dev_id) == WS_PartitionID(PID_INVALID))
}

// Is the instruction operand <o> for call instructions a valid source operand?
predicate ins_valid_jmp_call_src_opr(wkm:WK_MState, o:operand)
    requires WK_ValidMState(wkm)
{
    match o
        case OConst(n) => true
        case OReg(r) => false
        case OSReg(sr) => false
        case OMAddr(addr) => false
        case OErr => false
}




/*********************** Validity of Instructions ********************/
// According to Intel® 64 and IA-32 Architectures Software Developer’s Manual
// [NOTE] The machine model specifies all transitions for every valid instructions defined here. The COTS assembler (
// e.g., gcc) may regard a subset of these instructions w/ the prescribed operands are actually valid; e.g., MOV cannot
// target to Eflags. The fact that only a subset of these instructions works does not hurt any security properties that
// that hold for the bigger set of instructions w/ operands described here

// Predicate: Validity of each instruction. The checks include operand types, operands' values (e.g., allowed values to
// be written in global variables), and related registers' values (e.g., stack pointers)
predicate ValidInstruction(s:state, ins:ins)
{
    var s_wkm := s.wk_mstate;

    ValidState(s) && match ins
        case MOV(dst, src) => ins_valid_dst_opr(s_wkm, dst) && 
            ins_valid_src_opr(s_wkm, src) &&
            (
                var v := OperandContents(s_wkm, src);
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
                  
        case ADD(dst, src) => ins_valid_dst_opr(s_wkm, dst) && 
            ins_valid_src_opr(s_wkm, src) && ins_valid_src_opr(s_wkm, dst) &&
            (
                var v := TruncateWord(OperandContents(s_wkm, dst) + OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case SUB(dst, src) => ins_valid_dst_opr(s_wkm, dst) && 
            ins_valid_src_opr(s_wkm, src) && ins_valid_src_opr(s_wkm, dst) &&
            (
                var v := TruncateWord(OperandContents(s_wkm, dst) - OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case MUL(src) => ins_valid_src_opr(s_wkm, src) && ins_valid_src_opr(s_wkm, OReg(EAX)) && 
                  ins_valid_src_opr(s_wkm, OReg(EDX)) && ins_valid_dst_opr(s_wkm, OReg(EAX))
        case AND(dst, src) => ins_valid_dst_opr(s_wkm, dst) && 
            ins_valid_src_opr(s_wkm, src) && ins_valid_src_opr(s_wkm, dst) &&
            (
                var v := BitwiseAnd(OperandContents(s_wkm, dst), OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case OR(dst, src) => ins_valid_dst_opr(s_wkm, dst) && 
            ins_valid_src_opr(s_wkm, src) && ins_valid_src_opr(s_wkm, dst) &&
            (
                var v := BitwiseOr(OperandContents(s_wkm, dst), OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case XOR(dst, src) => ins_valid_dst_opr(s_wkm, dst) && 
            ins_valid_src_opr(s_wkm, src) && ins_valid_src_opr(s_wkm, dst) &&
            (
                var v := BitwiseXor(OperandContents(s_wkm, dst), OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case NOT(dst) => ins_valid_dst_opr(s_wkm, dst) && ins_valid_src_opr(s_wkm, dst) &&
            (
                var v := BitwiseNot(OperandContents(s_wkm, dst));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case MOV_reloc(dst, name) => ins_valid_dst_opr(s_wkm, dst) && 
            is_gvar_exist(name) &&
            (
                var v := AddressOfGlobal(name);
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case LDR_global(dst, global, base, ofs) =>
            ins_valid_dst_opr(s_wkm, dst) &&
            ins_is_reg_opr(base) && ins_valid_src_opr(s_wkm, ofs) &&        
                                // not using ins_is_const_opr(ofs) because WK needs to traversal global arrays
            (
                var addr:int := OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs);
                is_valid_addr(addr) && is_valid_vaddr(addr) && is_gvar_valid_vaddr(global, addr)
            ) &&
            (
                var v := gvar_read_word_byoffset(s_wkm, global,
                    WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs), AddressOfGlobal(global)));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case STR_global(src, global, base, ofs) =>
            ins_valid_src_opr(s_wkm, src) &&
            ins_is_reg_opr(base) && ins_valid_src_opr(s_wkm, ofs) &&
                                // not using ins_is_const_opr(ofs) because WK needs to traversal global arrays
            (
                var addr:int := OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs);
                var v:word := OperandContents(s_wkm, src);
                is_valid_addr(addr) && is_valid_vaddr(addr) && is_gvar_valid_vaddr(global, addr) &&
                ins_valid_strglobal_word(s.subjects, s.objects, s.id_mappings, s.objs_addrs, s.activate_conds, 
                    wkm_get_globals(s_wkm), global, addr, v)
            )
        case PUSH(src) =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - UINT32_BYTES;
            ins_valid_src_opr(s_wkm, src) && ins_valid_opr(s_wkm, OReg(ESP)) &&
            is_valid_vaddr(esp_value) && is_vaddr_in_stack(esp_value) && // The current ESP points to WK's_wkm stack
            is_vaddr_in_stack(stack_new_top)    // The new ESP value points to WK's_wkm stack
        case POP(dst) =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value + UINT32_BYTES;
            ins_valid_dst_opr(s_wkm, dst) && ins_valid_opr(s_wkm, OReg(ESP)) &&
            is_valid_vaddr(esp_value) && is_vaddr_in_stack(esp_value) &&  // The current ESP points to WK's_wkm stack
            is_vaddr_in_stack(stack_new_top) &&    // The new ESP value points to WK's_wkm stack
            ins_is_reg_opr(dst) &&      
            dst != OReg(ESP)            // WK code limits pop to registers (excluding ESP)
        case SHL(dst, src) => //CCH: dst should not allow SReg
            ins_valid_dst_opr(s_wkm, dst) && ins_valid_opr_shift(s_wkm, src) &&
            (
                var v := LeftShift(OperandContents(s_wkm, dst), OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        case SHR(dst, src) => //CCH: dst should not allow SReg
            ins_valid_dst_opr(s_wkm, dst) && ins_valid_opr_shift(s_wkm, src) &&
            (
                var v := RightShift(OperandContents(s_wkm, dst), OperandContents(s_wkm, src));
                ins_valid_new_dst_opr_value(s_wkm, dst, v)
            )
        /*case CALL(src) =>
            ins_valid_jmp_call_src_opr(s_wkm, src) 
        case JMP_Ret3(src) =>
            ins_valid_jmp_call_src_opr(s_wkm, src) */
        case CALL_EEHCI_Activate() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_retval_space := FFI_EEHCI_Activate_ReturnWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_retval_space)
        case CALL_EEHCI_Deactivate() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_eehci_deactivate(s_wkm, esp_value)
        case CALL_EEHCI_FIND_RefToUSBTD() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := 1 * ARCH_WORD_BYTES;
             var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_QTD32_ParseTDPointers() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_retval_space := 4 * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_retval_space) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_QTD32_ParseBufPointers() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_retval_space := 5 * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_retval_space) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_QH32_ParseTDPointers() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_retval_space := FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_retval_space) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_QH32_ParseBufPointers() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_retval_space := FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_retval_space) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_QH32_ParseTargetUSBDevID() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_retval_space := FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_retval_space) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_Copy_From_User() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES)
        case CALL_USBTD_CheckNotModifyUSBPDevAddrs() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES)
        case CALL_USBTD_Backup() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBTD_Backup_StackParamsWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_Restore() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_usbtd_restore(wkm_stack_get_all(s_wkm), wkm_get_globals(s_wkm), esp_value)
        case CALL_USBTD_IsRefTargetUSBTD() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            usbtd_map_valid_slot_id(td_slot)
        case CALL_USBTD_Clear_Content() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_usbtd_clear_content(wkm_stack_get_all(s_wkm), wkm_get_globals(s_wkm), esp_value)
        case CALL_WimpDrv_DO_Clear() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_WimpDrv_DO_Clear_StackParamsWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_wimpdrv_DO_clear(s, esp_value)
        case CALL_WimpDrv_CheckDOPAddrRange() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords * ARCH_WORD_BYTES;
            var td_slot := stack_get_val(old_stack, esp_value); 
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES)
        case CALL_PMem_AssignToWimps() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_PMem_AssignToWimps_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_pmem_assign_main_mem_to_wimps(s, esp_value)
        case CALL_PMem_ReleaseFromWimps() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_pmem_release_main_mem_from_wimps(s, esp_value)
        case CALL_PMem_ActivateInOS() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_pmem_activate_main_mem_in_os(s, esp_value)
        case CALL_PMem_DeactivateFromOS() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_pmem_deactivate_main_mem_from_os(s, esp_value)
        case CALL_USBPDev_Clear() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_USBPDev_Clear_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_usbpdev_clear(s, esp_value)
        case AXIOM_Assign_USBPDevs_To_OS_Partition() =>
            WK_ValidGlobalVarValues_USBPDevList(s.subjects, s.id_mappings, wkm_get_globals(s.wk_mstate)) &&
            (forall i :: usbpdev_valid_slot_id(i)
                ==> usbpdev_get_pid(wkm_get_globals(s.wk_mstate), i) == WS_PartitionID(PID_INVALID))
                // All USBPDevs are inactive
        case CALL_PEHCI_ActivateInOS() =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var old_stack := wkm_stack_get_all(s_wkm);
            var stack_new_top := esp_value - WK_STACK_FOR_EXTERNEL_FUNCS_SZ;
            var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
            is_vaddr_in_stack(stack_new_top) &&
            is_vaddr_in_stack(esp_value + stack_params_space - ARCH_WORD_BYTES) &&
            ins_valid_pEHCI_ActivateInOS(s, esp_value)
        /*
        case VMCALL(leaf, arg0, arg1, arg2, arg3, bdf) =>
             leaf == OReg(EAX) && arg0 == OReg(ECX) && arg1 == OReg(EDX) &&
             arg2 == OReg(ESI) && arg3 == OReg(EDI) && bdf == OReg(EBX)*/
}

predicate evalUpdate(s:WK_MState, o:operand, v:word, r:WK_MState)
    requires WK_ValidMState(s)
    requires ins_valid_dst_opr(s, o)
    requires ins_valid_new_dst_opr_value(s, o, v)

    ensures evalUpdate(s, o, v, r) ==> WK_ValidMState(r)
{
    var d := (match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])              
        case OSReg(sr) => r == s.(sregs := s.sregs[sr := v])         
        case OMAddr(addr) => var resolved_addr := eval_maddr(s, addr);
                             WK_evalMemUpdate(s, resolved_addr, v, r));

    if(d) then
        Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        d
    else
        d       
}

// Eval update of two registers at the same time
predicate evalUpdate_tworegs(s:WK_MState, o1:operand, v1:word, o2:operand, v2:word, r:WK_MState)
    requires WK_ValidMState(s)
    requires ins_valid_dst_opr(s, o1)
    requires ins_valid_dst_opr(s, o2)
        // Requirement: the two operands are dest. operands
    requires ins_is_reg_opr(o1)
    requires ins_is_reg_opr(o2)
    requires o1 != o2
        // Requirement: the two operands are distinct registers
    requires o2 != OReg(ESP)
        // Requirement: the 2nd operand must not be ESP

    requires ins_valid_new_dst_opr_value(s, o1, v1)

    ensures evalUpdate_tworegs(s, o1, v1, o2, v2, r) ==> WK_ValidMState(r)
{
    var s1 := s.(regs := s.regs[o1.r := v1]);
    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(s), wkm_get_globals(s1));

    var d := (r == s1.(regs := s1.regs[o2.r := v2]));

    if(d) then
        Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(s1), wkm_get_globals(r));
        d
    else
        d
}

// Eval update of one register and one memory at the same time
predicate evalUpdate_regandmem(s:WK_MState, o1:operand, v1:word, m:vaddr, v2:word, r:WK_MState)
    requires WK_ValidMState(s)
    requires ins_valid_dst_opr(s, o1)   
    requires ins_is_reg_opr(o1)
        // Requirement: the first operand must be a register operand
    requires WK_ValidMemVAddr(m)
        // Requirement: the second operand must be a valid vaddr

    requires ins_valid_new_dst_opr_value(s, o1, v1)

    ensures evalUpdate_regandmem(s, o1, v1, m, v2, r) ==> WK_ValidMState(r)
{
    reveal x86wk_valid_memstate();
    var s1 := s.(regs := s.regs[o1.r := v1]);
    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(s), wkm_get_globals(s1));

    var d := (r == s1.(m := s1.m[m := v2])); 

    if(d) then
        Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(s1), wkm_get_globals(r));
        d
    else
        d
}

// Predicate: Correctness of each instruction in transiting machine states
// [NOTE] This predicate is assumed to be true in Vale procedures' pre-conditions
predicate evalIns'_wkmstate(ins:ins, s:state, r:state)
    requires ValidInstruction(s, ins)

    ensures evalIns'_wkmstate(ins, s, r) ==> WK_ValidMState(r.wk_mstate)
    ensures evalIns'_wkmstate(ins, s, r) ==> ValidState(r)
{
    var s_wkm := s.wk_mstate;
    var r_wkm := r.wk_mstate;

    match ins
        case MOV(dst, src) => 
            var d := evalUpdate(s_wkm, dst, OperandContents(s_wkm, src), r_wkm) && 
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case ADD(dst, src) => 
            var d := evalUpdate(s_wkm, dst, 
                        TruncateWord(OperandContents(s_wkm, dst) + OperandContents(s_wkm, src)), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case SUB(dst, src) => 
            var d :=evalUpdate(s_wkm, dst,
                        TruncateWord(OperandContents(s_wkm, dst) - OperandContents(s_wkm, src)), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case MUL(src) => 
            //unsigned mul
            Lemma_UInt32Mul_Range(); 
            var val:uint64 := (OperandContents(s_wkm, OReg(EAX)) * OperandContents(s_wkm, src));
            var eax := UInt64Low(val);
            var edx := UInt64High(val);
            var d := evalUpdate_tworegs(s_wkm, OReg(EAX), eax, OReg(EDX), edx, r_wkm) && 
                        state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case AND(dst, src) => 
            var d := evalUpdate(s_wkm, dst,
                        BitwiseAnd(OperandContents(s_wkm, dst), OperandContents(s_wkm, src)), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case OR(dst, src) => 
            var d := evalUpdate(s_wkm, dst,
                        BitwiseOr(OperandContents(s_wkm, dst), OperandContents(s_wkm, src)), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case XOR(dst, src) => 
            var d := evalUpdate(s_wkm, dst,
                        BitwiseXor(OperandContents(s_wkm, dst), OperandContents(s_wkm, src)), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case NOT(dst) => 
            var d := evalUpdate(s_wkm, dst,
                        BitwiseNot(OperandContents(s_wkm, dst)), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case MOV_reloc(dst, name) => 
            var d := evalUpdate(s_wkm, dst, AddressOfGlobal(name), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case LDR_global(dst, global, base, ofs) =>
            var d := evalUpdate(s_wkm, dst, gvar_read_word_byoffset(s_wkm, global,
                        WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs), 
                                    AddressOfGlobal(global))), r_wkm) && 
                    state_equal_except_mstate(s, r);
            
            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case STR_global(src, global, base, ofs) =>
            var d := WK_evalGlobalUpdate(s, global,
                        WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs),
                                    AddressOfGlobal(global)), OperandContents(s_wkm, src), r_wkm) && 
                    state_equal_except_mstate(s, r);

            if(d) then
                Lemma_STR_global_ResultStateIsValidState(s, r, src, global, base, ofs);
                d
            else
                d
        case PUSH(src) =>
            var src_value := OperandContents(s_wkm, src);
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var new_esp_value := esp_value - UINT32_BYTES;
            var stack_new_top := new_esp_value;
            var d := evalUpdate_regandmem(s_wkm, OReg(ESP), new_esp_value, stack_new_top, src_value, r_wkm) && 
                        state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case POP(dst) =>
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var pop_value := wkm_stack_get_val(s_wkm, esp_value);
            var new_esp_value := esp_value + UINT32_BYTES;
            assert ins_is_reg_opr(dst);
            var d := evalUpdate_tworegs(s_wkm, OReg(ESP), new_esp_value, dst, pop_value, r_wkm) && 
                        state_equal_except_mstate(s, r);

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case SHL(dst, src) => 
            var d := evalUpdate(s_wkm, dst, LeftShift(OperandContents(s_wkm, dst), OperandContents(s_wkm, src)), r_wkm) && 
                        state_equal_except_mstate(s, r);
            // We do not model SHL's_wkm modification to CF, because WK code only cares about IF in EFLAGS

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        case SHR(dst, src) => 
            var d := evalUpdate(s_wkm, dst, RightShift(OperandContents(s_wkm, dst), OperandContents(s_wkm, src)), r_wkm) && 
                        state_equal_except_mstate(s, r);
            // We do not model SHR's_wkm modification to CF, because WK code only cares about IF in EFLAGS

            if(d) then
                Lemma_InstNotModifyingGlobalVars_ResultStateIsValidState(s, r);
                d
            else
                d
        /*case CALL(src) =>
            var src_value := NONDET_PC();
            var esp_value := OperandContents(s_wkm, OReg(ESP));
            var new_esp_value := esp_value - UINT32_BYTES;
            var stack_new_top := new_esp_value;
            evalUpdate_regandmem(s_wkm, OReg(ESP), new_esp_value, stack_new_top, src_value, r_wkm) 
        case JMP_Ret3(src) =>
            var fn_idx := src.n;
            var new_stack := ffi_ret_on_stack_3words(fn_idx, s_wkm);
            r_wkm == s_wkm.(m := new_stack) */
        case CALL_EEHCI_Activate() =>
            var result := ffi_eehci_activate(s);
            var new_stack := result.0;
            var new_globals := result.1;
            var new_regs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm.(globals := new_globals)) &&
                      state_equal_except_mstate(s, r);    // Update regs, stack and global variables

            if(d) then
                Lemma_ffi_eehci_activate_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack, new_globals);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_eehci_activate_ResultStateIsValidState(s, r, new_regs, new_stack, new_globals);
                d 
            else
                d
        case CALL_EEHCI_Deactivate() =>
            var result := ffi_eehci_deactivate(s_wkm);
            var new_stack := result.0;
            var new_globals := result.1;
            var new_regs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm.(globals := new_globals)) &&    // Update regs, stack and global variables
                     state_equal_except_mstate(s, r);
            if(d) then
                Lemma_ffi_eehci_deactivate_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack, new_globals);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_eehci_deactivate_ResultStateIsValidState(s, r, new_regs, new_stack, new_globals);
                d
            else
                d
        case CALL_EEHCI_FIND_RefToUSBTD() =>
            var result := ffi_eehci_find_ref_to_usbtd(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_eehci_find_ref_to_usbtd_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_eehci_find_ref_to_usbtd_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_QTD32_ParseTDPointers() =>
            var result := ffi_usbtd_qtd32_parseTDPtrs(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_usbtd_qtd32_parseQTDpointer_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_qtd32_parseQTDpointer_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_QTD32_ParseBufPointers() =>
            var result := ffi_usbtd_qtd32_parseDataBufPtrs(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_usbtd_qtd32_parseBufpointer_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_qtd32_parseBufpointer_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_QH32_ParseTDPointers() =>
            var result := ffi_usbtd_qh32_parseTDPtrs(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);
            if(d) then
                Lemma_ffi_usbtd_qh32_parseQTDpointer_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_qh32_parseQTDpointer_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_QH32_ParseBufPointers() =>
            var result := ffi_usbtd_qh32_parseDataBufPtrs(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);
            if(d) then
                Lemma_ffi_usbtd_qh32_parseBufpointer_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_qh32_parseBufpointer_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_QH32_ParseTargetUSBDevID() =>
            var result := ffi_usbtd_qh32_parseTargetUSBDevID(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);
            if(d) then
                Lemma_ffi_usbtd_qh32_parseTargetUSBDevID_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_qh32_parseTargetUSBDevID_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_Copy_From_User() =>
            var result := ffi_usbtd_copy_from_user(s_wkm);
            var new_stack := result.0;
            var new_globals := result.1;
            var new_regs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm.(globals := new_globals)) &&    // Update regs, stack and global variables
                     state_equal_except_mstate(s, r);
            if(d) then
                Lemma_ffi_usbtd_copy_from_user_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack, new_globals);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_copy_from_user_ResultStateIsValidState(s, r, new_regs, new_stack, new_globals);
                d
            else
                d
        case CALL_USBTD_CheckNotModifyUSBPDevAddrs() =>
            var result := ffi_usbtd_check_not_modify_usbpdev_addrs(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);
            if(d) then
                Lemma_ffi_usbtd_check_not_modify_usbpdev_addrs_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_check_not_modify_usbpdev_addrs_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_Backup() =>
            var result := ffi_usbtd_backup(s_wkm);
            var new_stack := result.0;
            var new_globals := result.1;
            var new_regs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm.(globals := new_globals)) &&    // Update regs, stack and global variables
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_usbtd_backup_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack, new_globals);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_backup_ResultStateIsValidState(s, r, new_regs, new_stack, new_globals);
                d
            else
                d
        case CALL_USBTD_Restore() =>
            var result := ffi_usbtd_restore(s_wkm);
            var new_stack := result.0;
            var new_globals := result.1;
            var new_regs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm.(globals := new_globals)) &&    // Update regs, stack and global variables
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_usbtd_restore_ResultStateIsValidMState(s, r, new_regs, new_stack, new_globals);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_restore_ResultStateIsValidState(s, r, new_regs, new_stack, new_globals);
                d
            else
                d
        case CALL_USBTD_IsRefTargetUSBTD() =>
            var result := ffi_usbtd_is_ref_target_usbtd(s_wkm);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_usbtd_is_ref_target_usbtd_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_is_ref_target_usbtd_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_USBTD_Clear_Content() =>
            var result := ffi_usbtd_clear_content(s_wkm);
            var new_stack := result.0;
            var new_globals := result.1;
            var new_regs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm.(globals := new_globals)) &&    // Update regs, stack and global variables
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_usbtd_clear_content_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack, new_globals);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_usbtd_clear_content_ResultStateIsValidState(s, r, new_regs, new_stack, new_globals);
                d
            else
                d
        case CALL_WimpDrv_DO_Clear() =>
            var result := ffi_wimpdrv_DO_clear(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_objs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm, objects := new_objs);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_wimpdrv_DO_clear_ResultStateIsValidState(s, r);
                assert WK_ValidMState(r_wkm);
                d
            else
                d
        case CALL_WimpDrv_CheckDOPAddrRange() =>
            var result := ffi_wimpdrv_DO_check_paddr_range(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var d := (r_wkm == s2_wkm) &&    // Update both regs and stack 
                     state_equal_except_mstate(s, r);

            if(d) then
                Lemma_ffi_wimpdrv_DO_check_paddr_range_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_wimpdrv_DO_check_paddr_range_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_PMem_AssignToWimps() =>
            var result := ffi_pmem_assign_main_mem_to_wimps(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_pmem_assign_main_mem_to_wimps_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_pmem_assign_main_mem_to_wimps_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_PMem_ReleaseFromWimps() =>
            var result := ffi_pmem_release_main_mem_from_wimps(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_pmem_release_main_mem_from_wimps_ResultStateIsValidMState(s_wkm, r_wkm, new_regs, new_stack);
                assert WK_ValidMState(r_wkm);
                Lemma_ffi_pmem_release_main_mem_from_wimps_ResultStateIsValidState(s, r, new_regs, new_stack);
                d
            else
                d
        case CALL_PMem_ActivateInOS() =>
            var result := ffi_pmem_activate_main_mem_in_os(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_subjects := result.2;
            var new_objects := result.3;
            var new_os_mem_active_map := result.4;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm, subjects := new_subjects, objects := new_objects, os_mem_active_map := new_os_mem_active_map);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_pmem_activate_main_mem_in_os_ResultStateIsValidState(s, r);
                assert WK_ValidMState(r_wkm);
                d
            else
                d
        case CALL_PMem_DeactivateFromOS() =>
            var result := ffi_pmem_deactivate_main_mem_from_os(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_subjects := result.2;
            var new_objects := result.3;
            var new_os_mem_active_map := result.4;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm, subjects := new_subjects, objects := new_objects, os_mem_active_map := new_os_mem_active_map);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_pmem_deactivate_main_mem_from_os_ResultStateIsValidState(s, r);
                assert WK_ValidMState(r_wkm);
                d
            else
                d
        case CALL_USBPDev_Clear() =>
            var result := ffi_usbpdev_clear(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_objs := result.2;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm, objects := new_objs);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_usbpdev_clear_ResultStateIsValidState(s, r);
                assert WK_ValidMState(r_wkm);
                d
            else
                d
        case AXIOM_Assign_USBPDevs_To_OS_Partition() =>
            var result_subjs := AXIOM_Assign_USBPDevs_To_OS_Partition_Property(s);
            var expect_r := s.(subjects := result_subjs);
            var d := (r == expect_r);

            if(d) then
                Lemma_AXIOM_Assign_USBPDevs_To_OS_Partition_ResultStateIsValidState(s, r);
                assert WK_ValidMState(r_wkm);
                d
            else
                d
        case CALL_PEHCI_ActivateInOS() =>
            var result := ffi_pEHCI_ActivateInOS(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_subjects := result.2;
            var new_objects := result.3;
            var s1_wkm := s_wkm.(regs := new_regs); 
            var s2_wkm := s1_wkm.(m := new_stack);
            var expect_r := s.(wk_mstate := s2_wkm, subjects := new_subjects, objects := new_objects);
            var d := (r == expect_r);

            if(d) then
                Lemma_ffi_pEHCI_ActivateInOS_ResultStateIsValidState(s, r);
                assert WK_ValidMState(r_wkm);
                d
            else
                d
                
        /*case VMCALL(leaf, arg0, arg1, arg2, arg3, bdf) =>
            evalVMCALLUpdate(s_wkm, OperandContents(s_wkm, leaf), OperandContents(s_wkm, arg0),
                                OperandContents(s_wkm, arg1), OperandContents(s_wkm, arg2), 
                                OperandContents(s_wkm, arg3), OperandContents(s_wkm, bdf), r_wkm)*/ 
}

predicate evalIns'(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then !r.ok
    else 
        evalIns'_wkmstate(ins, s, r) /*&&
        WKOps_UnchangedStateVars(s, r) */
}

predicate evalIns(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then !r.ok
    else if interrupts_enabled(x86_get_eflags(s.wk_mstate)) then !r.ok // [NOTE] In the I/O separation part of WK, all operations 
                                                    // must have interrupts disabled
    else evalIns'(ins, s, r)
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r' :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

predicate evalIfElse(cond:obool, ifT:code, ifF:code, s:state, r:state)
    decreases if ValidState(s) && ins_valid_opr_bool(s.wk_mstate, cond.o1) && ins_valid_opr_bool(s.wk_mstate, cond.o2) && evalOBool(s.wk_mstate, cond) 
              then ifT else ifF
{
    if ValidState(s) && s.ok && 
       ins_valid_opr_bool(s.wk_mstate, cond.o1) && ins_valid_opr_bool(s.wk_mstate, cond.o2) &&
       !interrupts_enabled(x86_get_eflags(s.wk_mstate)) // [NOTE] In the I/O separation part of WK, all operations must have interrupts 
                                        // disabled
    then
        (if evalOBool(s.wk_mstate, cond) then evalCode(ifT, s, r) else evalCode(ifF, s, r))
    else
        !r.ok
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state)
    decreases c, n
{
    if ValidState(s) && s.ok && 
       ins_valid_opr_bool(s.wk_mstate, b.o1) && ins_valid_opr_bool(s.wk_mstate, b.o2) &&
       !interrupts_enabled(x86_get_eflags(s.wk_mstate)) // [NOTE] In the I/O separation part of WK, all operations must have interrupts 
                                        // disabled
    then
        if n == 0 then
            !evalOBool(s.wk_mstate, b) && (s == r) // While-loop should be skipped/terminated, so s must equal to r
        else
            exists r':state :: evalOBool(s.wk_mstate, b) && evalCode(c, s, r') && evalWhile(b, c, n - 1, r', r)
                                                // Otherwise "evalCode(c, s, r')" evaluate the entire while-loop body,
                                                // and then evaluate the next-iteration of the while-loop
    else
        !r.ok
}

predicate evalCode(c:code, s:state, r:state)
    decreases c, 0
{
    match c
        case Ins(ins) => evalIns(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s, r) // given s and r, there must be n
                                                            // steps to transit s to r
}




/*********************** Private Lemma ********************/
lemma Lemma_STR_global_ResultStateIsValidState(
    s:state, r:state, src:operand, global:symbol,
    base:operand, ofs:operand
)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             ins_valid_src_opr(s_wkm, src) &&
             ins_is_reg_opr(base) && ins_valid_src_opr(s_wkm, ofs) &&
                                // not using ins_is_const_opr(ofs) because WK needs to traversal global arrays
             (
                var addr:int := OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs);
                var v:word := OperandContents(s_wkm, src);
                is_valid_addr(addr) && is_valid_vaddr(addr) && is_gvar_valid_vaddr(global, addr) &&
                ins_valid_strglobal_word(s.subjects, s.objects, s.id_mappings, s.objs_addrs, s.activate_conds, 
                    wkm_get_globals(s_wkm), global, addr, v)
             )

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             WK_evalGlobalUpdate(s, global,
                        WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs),
                                    AddressOfGlobal(global)), OperandContents(s_wkm, src), r_wkm) 
    requires state_equal_except_mstate(s, r)

    ensures ValidState(r)
{
    reveal WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition();
    reveal WK_ValidObjsAddrs();

    Lemma_STR_global_ResultStateIsValidState_Prove_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s, r, src, global, base, ofs);
    Lemma_STR_global_ResultStateIsValidState_Prove_WK_ValidState_DevsActivateCond(s, r, src, global, base, ofs);
    Lemma_STR_global_ResultStateIsValidState_Prove_WK_ValidObjsAddrs_PEHCIs(s, r, src, global, base, ofs);

    reveal WK_ValidGlobalVarValues_USBPDevs();
    reveal WK_ValidGlobalVarValues_USBPDevList();
    
    var globals := wkm_get_globals(r.wk_mstate);
}

// Lemma: STR_global ends up at a result state fulfilling WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition
lemma Lemma_STR_global_ResultStateIsValidState_Prove_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s:state, r:state, src:operand, global:symbol,
                base:operand, ofs:operand)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             ins_valid_src_opr(s_wkm, src) &&
             ins_is_reg_opr(base) && ins_valid_src_opr(s_wkm, ofs) &&
                                // not using ins_is_const_opr(ofs) because WK needs to traversal global arrays
             (
                var addr:int := OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs);
                var v:word := OperandContents(s_wkm, src);
                is_valid_addr(addr) && is_valid_vaddr(addr) && is_gvar_valid_vaddr(global, addr) &&
                ins_valid_strglobal_word(s.subjects, s.objects, s.id_mappings, s.objs_addrs, s.activate_conds, 
                    wkm_get_globals(s_wkm), global, addr, v)
             )

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             WK_evalGlobalUpdate(s, global,
                        WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs),
                                    AddressOfGlobal(global)), OperandContents(s_wkm, src), r_wkm) 
    requires state_equal_except_mstate(s, r)

    ensures WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))
{
    reveal WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);

    // Dafny-2.3 have difficulties to apply <Lemma_ObjsOwnedByOSSubjsMustBeInState_ApplyForOneSubjAndObj> and
    // <Lemma_ObjsOwnedByOSSubjsMustBeInState>, so we have to reveal these predicates
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall s_id, o_id | WSM_IsOSSubjID(subjs', s_id) && WSM_DoOwnObj(subjs', s_id, o_id)
        ensures WSM_IsOSObj(objs', o_id)
        ensures WSM_IsOSObj(objs, o_id)
    {
        Lemma_ObjsOwnedByOSSubjsMustBeInState_ApplyForOneSubjAndObj(subjs', objs', id_mappings', s_id, o_id);
    }

    // Prove WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition
    forall s_id, o_id | WSM_IsOSSubjID(subjs', s_id) && WSM_DoOwnObj(subjs', s_id, o_id)
        ensures WSM_SubjPID(subjs', objs', id_mappings', globals', s_id) == WSM_ObjPID(subjs', objs', id_mappings', globals', o_id)
    {
        assert WSM_IsOSSubjID(subjs, s_id);
        assert WSM_DoOwnObj(subjs, s_id, o_id);
    }
}

// Lemma: STR_global ends up at a result state fulfilling WK_ValidState_DevsActivateCond
lemma Lemma_STR_global_ResultStateIsValidState_Prove_WK_ValidState_DevsActivateCond(s:state, r:state, src:operand, global:symbol,
                base:operand, ofs:operand)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             ins_valid_src_opr(s_wkm, src) &&
             ins_is_reg_opr(base) && ins_valid_src_opr(s_wkm, ofs) &&
                                // not using ins_is_const_opr(ofs) because WK needs to traversal global arrays
             (
                var addr:int := OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs);
                var v:word := OperandContents(s_wkm, src);
                is_valid_addr(addr) && is_valid_vaddr(addr) && is_gvar_valid_vaddr(global, addr) &&
                ins_valid_strglobal_word(s.subjects, s.objects, s.id_mappings, s.objs_addrs, s.activate_conds, 
                    wkm_get_globals(s_wkm), global, addr, v)
             ) 

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             WK_evalGlobalUpdate(s, global,
                        WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs),
                                    AddressOfGlobal(global)), OperandContents(s_wkm, src), r_wkm) 
    requires state_equal_except_mstate(s, r)

    ensures WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidState_DevsActivateCond();
    reveal WSM_physical_EHCIs_must_be_inactive();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);
    var activate_conds := s.activate_conds;

    var subjs' := r.subjects;
    var objs' := r.objects;
    var id_mappings' := r.id_mappings;
    var objs_addrs' := r.objs_addrs;
    var globals' := wkm_get_globals(r.wk_mstate);
    var activate_conds' := r.activate_conds;

    assert forall s_id :: WSM_IsOSSubjID(subjs', s_id)
            ==> WSM_SubjPID(subjs', objs', id_mappings', globals', s_id) == WSM_SubjPID(subjs, objs, id_mappings, globals, s_id);
    
    assert forall dev_id :: WSM_IsEEHCIDevID(subjs', dev_id)
            ==> (SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', dev_id) == WS_PartitionID(PID_INVALID) || 
                 SubjPID_EEHCI_ByDevID(subjs', objs', id_mappings', globals', dev_id) in pids_parse_g_wimp_pids(globals'));

    // Prove: If a device is active in red partition, then all mapped devices are inactive
    assert WSM_physical_EHCIs_must_be_inactive(subjs, activate_conds);
    assert WSM_physical_EHCIs_must_be_inactive(subjs', activate_conds');
    forall dev_id | dev_id in activate_conds'.ehci_activate_cond &&
            WSM_SubjPID(subjs', objs', id_mappings', globals', dev_id.sid) != WS_PartitionID(PID_INVALID)
        ensures (forall dev_id2 :: dev_id2 in activate_conds'.ehci_activate_cond[dev_id]
                ==> WSM_SubjPID(subjs', objs', id_mappings', globals', dev_id2.sid) == WS_PartitionID(PID_INVALID))
    {
        assert dev_id in subjs'.os_devs;
        assert SubjPID_OSDev(subjs', dev_id) == WS_PartitionID(PID_INVALID);
        assert WSM_SubjPID(subjs', objs', id_mappings', globals', dev_id.sid) == SubjPID_OSDev(subjs', dev_id);
    }
}

// Lemma: STR_global ends up at a result state fulfilling WK_ValidObjsAddrs_PEHCIs
lemma Lemma_STR_global_ResultStateIsValidState_Prove_WK_ValidObjsAddrs_PEHCIs(s:state, r:state, src:operand, global:symbol,
                base:operand, ofs:operand)
    requires ValidState(s)

    requires WK_ValidMState(r.wk_mstate)
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidState_DevsActivateCond(r.subjects, r.objects, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             ins_valid_src_opr(s_wkm, src) &&
             ins_is_reg_opr(base) && ins_valid_src_opr(s_wkm, ofs) &&
                                // not using ins_is_const_opr(ofs) because WK needs to traversal global arrays
             (
                var addr:int := OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs);
                var v:word := OperandContents(s_wkm, src);
                is_valid_addr(addr) && is_valid_vaddr(addr) && is_gvar_valid_vaddr(global, addr) &&
                ins_valid_strglobal_word(s.subjects, s.objects, s.id_mappings, s.objs_addrs, s.activate_conds, 
                    wkm_get_globals(s_wkm), global, addr, v)
             ) 

    requires var s_wkm := s.wk_mstate;
             var r_wkm := r.wk_mstate;
             WK_evalGlobalUpdate(s, global,
                        WordAlignedSub(OperandContents(s_wkm, base) + OperandContents(s_wkm, ofs),
                                    AddressOfGlobal(global)), OperandContents(s_wkm, src), r_wkm) 
    requires state_equal_except_mstate(s, r)

    ensures WK_ValidObjsAddrs_PEHCIs(r.subjects, r.objects, r.objs_addrs, r.id_mappings, r.activate_conds, wkm_get_globals(r.wk_mstate))
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjsAddrs_PEHCIs();
    reveal WSM_physical_EHCIs_must_be_inactive();
}