//CCH: many things are from original vale's printGcc.s.dfy and Komodo's ARMprint.s.dfy
include "ins/x86/ins_eval.s.dfy"
include "ins/x86/valesupp.i.dfy"
include "wk_partition_ops.gen.dfy"
include "drv/drv_ops.gen.dfy"
include "os/os_ops.gen.dfy"
include "dev/usb2/usb_pdev_ops.gen.dfy"
include "dev/usb2/eehci_ops.gen.dfy"
include "dev/usb2/usb_tds_ops/usb_tds_ops.gen.dfy"
include "ins/util/ffi.s.dfy"

method printReg(r:x86Reg)
{
    print("%");
    match r
        case EAX => print("eax");
        case EBX => print("ebx");
        case ECX => print("ecx");
        case EDX => print("edx");
        case ESI => print("esi");
        case EDI => print("edi");
        case ESP => print("esp");
        case EBP => print("ebp");
}

method printMAddr(addr:maddr) //CCH: should be checked again
{
    match addr
        case MConst(n) => { print("("); print("$"); print(n); print(")"); } 
        case MReg(reg, offset) =>
            if 0 <= offset < 0x1_0000_0000 { print(offset); print("(");
                 printReg(reg); print(")");}
            else { print(" !NOT IMPLEMENTED11!"); }
}

method printOprnd(o:operand)
{
    match o
        case OConst(n) =>
            if 0 <= n as int < 0x1_0000_0000 { print("$"); print(n); }
            else { print(" !!!NOT IMPLEMENTED21!!!"); }
        case OReg(r) => printReg(r);
        case OSReg(r) => print(" !!!NOT IMPLEMENTED22!!!");
        case OMAddr(addr) => printMAddr(addr);
        case OErr => print("!!!ILLEGAL OPERAND!!!");
}


method printOffsetOprnd(o:operand)
{
    match o
        case OConst(offset) =>
            if 0 <= offset as int < 0x1_0000_0000 { print(offset); }
            else { print(" !!NOT IMPLEMENTED41!!!"); }
        case OReg(r) => print(" !!NOT IMPLEMENTED42!!!");
        case OSReg(r) => print(" !!NOT IMPLEMENTED43!!!");
        case OMAddr(addr) => print(" !!NOT IMPLEMENTED44!!!");
        case OErr => print("!!!ILLEGAL OPERAND!!!");
}

method print_Global_offset(base:operand, ofs:operand)
{
    if(base.OReg? && ofs.OReg?)
    {
        print("("); printOprnd(base); print(", "); printOprnd(ofs); print(")");  
    }
    else
    {
        printOffsetOprnd(ofs); print("("); printOprnd(base); print(")");
    }
}


method printIns(ins:ins)
{
    match ins
    {
        case MOV(dst, src) => print("  movl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case ADD(dst, src) => print("  addl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case SUB(dst, src) => print("  subl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case MUL(src) => print("  mull "); printOprnd(src); print("\n");
        case AND(dst, src) => print("  andl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case OR(dst, src)  => print("  orl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case XOR(dst, src) => print("  xorl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case NOT(dst) => print("  notl "); printOprnd(dst); print("\n");
        case MOV_reloc(dst, global) => print("  movl "); print("$("); print(global); print(")"); print(", "); printOprnd(dst); print("\n"); //CCH: should be checked again
        case LDR_global(dst, global, base, ofs) => print("  movl "); print_Global_offset(base, ofs); print(", "); printOprnd(dst); print("\n");
        case STR_global(src, global, base, ofs) => print("  movl "); printOprnd(src); print(", "); print_Global_offset(base, ofs); print("\n");
        case PUSH(src) => print("  pushl "); printOprnd(src); print("\n");
        case POP(dst)  => print("  popl "); printOprnd(dst); print("\n");
        case SHL(dst, src) => print("  shll "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        case SHR(dst, src) => print("  shrl "); printOprnd(src); print(", "); 
                              printOprnd(dst); print("\n");
        /*case CALL(src) => var func_name := ffi_get_targetfunc_name(src);
                        print("  call "); print(func_name); print("\n");
        case JMP_Ret3(src) => var func_name := ffi_get_targetfunc_name(src);
                        print("  jmp "); print(func_name); print("\n");*/
        case CALL_EEHCI_Activate() => print("  call eehci_activate_stub"); print("\n");
        case CALL_EEHCI_Deactivate() => print("  call eehci_deactivate_stub"); print("\n");
        case CALL_EEHCI_FIND_RefToUSBTD() => print("  call eehci_find_ref_to_usbtd"); print("\n");
        case CALL_USBTD_QTD32_ParseTDPointers() => print("  call usbtd_qtd32_parseQTDpointers"); print("\n");
        case CALL_USBTD_QTD32_ParseBufPointers() => print("  call usbtd_qtd32_parseBufpointers"); print("\n");
        case CALL_USBTD_QH32_ParseTDPointers() => print("  call usbtd_qh32_parseQTDpointers"); print("\n");
        case CALL_USBTD_QH32_ParseBufPointers() => print("  call usbtd_qh32_parseBufpointers"); print("\n");
        case CALL_USBTD_QH32_ParseTargetUSBDevID() => print("  call usbtd_qh32_parseTargetUSBDevID"); print("\n");
        case CALL_USBTD_Copy_From_User() => print("  call usbtd_copy_from_user"); print("\n");
        case CALL_USBTD_CheckNotModifyUSBPDevAddrs() => print("  call usbtd_check_not_modify_usbpdev_addrs"); print("\n");
        case CALL_USBTD_Backup() => print("  call usbtd_backup"); print("\n");
        case CALL_USBTD_Restore() => print("  call usbtd_restore"); print("\n");
        case CALL_USBTD_IsRefTargetUSBTD() => print("  call usbtd_is_ref_target_usbtd"); print("\n");
        case CALL_USBTD_Clear_Content() => print("  call usbtd_clear_content"); print("\n");
        case CALL_WimpDrv_DO_Clear() => print("  call wimpdrv_do_clear"); print("\n");
        case CALL_WimpDrv_CheckDOPAddrRange() => print("  call wimpdrv_do_check_paddr_range"); print("\n");
        case CALL_PMem_AssignToWimps() => print("  call pmem_assign_main_mem_to_wimps"); print("\n");
        case CALL_PMem_ReleaseFromWimps() => print("  call pmem_release_main_mem_from_wimps"); print("\n");
        case CALL_PMem_ActivateInOS() => print("  call pmem_activate_main_mem_in_os"); print("\n");
        case CALL_PMem_DeactivateFromOS() => print("  call pmem_deactivate_main_mem_from_os"); print("\n");
        case CALL_USBPDev_Clear() => print("  call usbpdev_clear"); print("\n");
        case CALL_PEHCI_ActivateInOS() => print("  call phy_ehci_activate_in_os"); print("\n");
        // For debug purpose
        //case CALL_DEBUG() => print("  call debug_func"); print("\n");
        /*case VMCALL(leaf, arg0, arg1, arg2, arg3, bdf) => print("  vmcall "); print("\n");*/
    }
}


method printBlock(b:codes, n:int) returns(n':int)
{
    n' := n;
    var i := b;
    while (i.va_CCons?)
        decreases i
    {
        n' := printCode(i.hd, n');
        i := i.tl;
    }
}


function method cmpNot(c:ocmp):ocmp
{
    match c
        case OEq => ONe
        case ONe => OEq
        case OLe => OGt
        case OGe => OLt
        case OLt => OGe
        case OGt => OLe
}

method printJcc(c:ocmp)
{
    match c
        case OEq => print("  je ");
        case ONe => print("  jne ");
        case OLe => print("  jbe ");
        case OGe => print("  jae ");
        case OLt => print("  jb ");
        case OGt => print("  ja ");
}


method printCode(c:code, n:int) returns(n':int)
{
    match c
        case Ins(ins) => printIns(ins); n' := n;
        case Block(block) => n' := printBlock(block, n);
        case IfElse(ifb, ift, iff) =>
        {
            var n1 := n;
            var n2 := n + 1;
            print("  cmpl "); printOprnd(ifb.o2); print(", "); printOprnd(ifb.o1); print("\n");
            printJcc(cmpNot(ifb.cmp)); print("L"); print(n1); print("\n");
            n' := printCode(ift, n + 2);
            print("  jmp L"); print(n2); print("\n");
            print("L"); print(n1); print(":\n");
            n' := printCode(iff, n');
            print("L"); print(n2); print(":\n");
        }
        case While(b, loop) =>
        {
            var n1 := n;
            var n2 := n + 1;
            print("  jmp L"); print(n2); print("\n");
            print(".align 16\nL"); print(n1); print(":\n");
            n' := printCode(loop, n + 2);
            print(".align 16\nL"); print(n2); print(":\n");
            print("  cmpl "); printOprnd(b.o2); print(", "); printOprnd(b.o1); print("\n");
            printJcc(b.cmp); print("L"); print(n1); print("\n");
        }
}


/*method printPrologue()
{
    print("  pushl %ebp"); print("\n");
    print("  movl %esp, %ebp"); print("\n");
    print("  subl $0x114, %esp"); print("\n");      //CCH: 0x114 could be changed
    print("  movl 0xc(%ebp), %ebx"); print("\n");   //psInBuf

    print("  movl 0x18(%ebx), %eax"); print("\n");   //DMAvirtual value
    print("  movl $(g_dma_virtbase), %ecx"); print("\n"); //LDRglobaladdr(ecx, DMAVirtBaseOp());
    print("  movl %eax, (%ecx)"); print("\n");       //STRglobal(eax, DMAVirtBaseOp(), ecx, 0);

    print("  movl 0x1C(%ebx), %eax"); print("\n");   //DMAphysical value
    print("  movl $(g_dma_physbase), %ecx"); print("\n"); //LDRglobaladdr(eax, DMAPhysBaseOp());
    print("  movl %eax, (%ecx)"); print("\n");       //STRglobal(eax, DMAPhysBaseOp(), ecx, 0);

    print("  movl (%ebx), %ecx"); print("\n");      //arg1
    print("  movl 0x4(%ebx), %edx"); print("\n");   //arg2
    print("  movl 0x8(%ebx), %esi"); print("\n");   //arg3
    print("  movl 0xC(%ebx), %edi"); print("\n");   //arg4
    print("  movl 0x10(%ebx), %eax"); print("\n");  //arg5
    print("  movl 0x14(%ebx), %ebx"); print("\n");  //arg6
    print("  movl %edi, 0x4(%esp)"); print("\n");
    print("  movl %eax, 0x8(%esp)"); print("\n");
    print("  movl %ebx, 0xC(%esp)"); print("\n");
    print("  movl $(g_devicedb), %eax"); print("\n"); //LDRglobaladdr(eax, DeviceDb());
    print("  movl %eax, (%esp)"); print("\n");
    print("  movl 0x8(%ebp), %eax"); print("\n");   //uiCommand
}

method printEpilogue()
{
    //CCH: should be reconsidered
    print("  movl 0x10(%ebp), %ebx"); print("\n");   //puiRv
    print("  movl %eax, (%ebx)"); print("\n");       //puiRv->status

    print("  movl $(g_dma_virtbase), %ebx"); print("\n"); //LDRglobaladdr(ebx, DMAVirtBaseOp());
    print("  movl (%ebx), %eax"); print("\n");            //LDRglobal(eax, DMAVirtBaseOp(), ebx, 0);
    print("  movl $(g_dma_physbase), %edx"); print("\n"); //LDRglobaladdr(edx, DMAVirtBaseOp());
    print("  movl (%edx), %ecx"); print("\n");            //LDRglobal(ecx, DMAPhysBaseOp(), edx, 0);
    print("  movl $0x1, (%esp)"); print("\n");            //slotnr.  1st parameter to vk_ret_os
    print("  movl %eax, 0x4(%esp)"); print("\n");         //vaddr.   2nd parameter to vk_ret_os
    print("  movl %ecx, 0x8(%esp)"); print("\n");         //paddr.   3nd parameter to vk_ret_os

    //print("  call vk_jump_to_os");
    print("  call vk_ret_os");
}*/

/*method printWKHandler(symname:string, c:code, n:int) returns(n':int)
{
    print(".global "); print(symname); nl();
    print(symname); print(":"); nl();
    printPrologue();
    n' := printCode(c, n);  //CCH: should be on
    printEpilogue();
    print("\n\n");
}*/

method printFunction(symname:string, c:code, n:int) returns(n':int)
{
    print(".global "); print(symname); nl();
    print(symname); print(":"); nl();
    n' := printCode(c, n);  
    print("\n\n");
}


method printHeader()
{
    //print(".x86"); nl(); CCH: is this necessary?
    print(".code32"); nl();
    print(".section .text"); nl();
}   


method nl()
{
    print("\n");
}

/*
method printHypercallHandlerReturn()
{
    print("leaveq");
    nl();
    print("retq");
    nl();
}


method printPgtblviolationHandlerReturn()
{
    print("leaveq");
    nl();
    print("retq");
    nl();
}
*/

method printGlobal(symname: string, bytes: int)
{
    print(".global ");
    print(symname);
    nl();

    print(".lcomm ");
    print(symname);
    print(", ");
    print(bytes);
    nl();
}

method printGlobalPalign(symname: string, bytes: int)
{
    print(".global ");
    print(symname);
    nl();
    print(".zero ");
    print(bytes);
    nl();
}


//CCH: this is from Komodo
method printBss(gdecls: globaldecls)
    requires ValidGlobalDecls(gdecls)
{
    print(".section .bss"); nl();
    print(".balign 4096"); nl(); // 4096-byte alignment // [Superymk] We prefer "balign" because it is consistent across archtectures
    var syms := (set k | k in gdecls :: k);
    while (|syms| > 0)
        invariant forall s :: s in syms ==> s in gdecls;
    {
        var s :| s in syms;
        printGlobal(s, gdecls[s]);
        syms := syms - {s};
    }
}

method printPalign(gdecls: globaldecls)
    requires ValidGlobalDecls(gdecls)
{
    print(".section .palign_data"); nl();
    var syms := (set k | k in gdecls :: k);
    while (|syms| > 0)
        invariant forall s :: s in syms ==> s in gdecls;
    {
        var s :| s in syms;
        printGlobalPalign(s, gdecls[s]);
        syms := syms - {s};
    }
}

method printFunctionReturn(symname:string)
{

    if(symname == "wk_empty_partition_create")
    {print "  jmp wk_empty_partition_create_ret"; print("\n");}
    else if(symname == "wk_empty_partition_destroy")
    {print "  jmp wk_empty_partition_destroy_ret"; print("\n");}

    else if(symname == "wimpdrv_activate")
    {print "  jmp wimpdrv_activate_ret"; print("\n");}
    else if(symname == "wimpdrv_deactivate")
    {print "  jmp wimpdrv_deactivate_ret"; print("\n");}

    else if(symname == "usbpdev_activate")
    {print "  jmp usbpdev_activate_ret"; print("\n");}
    else if(symname == "usbpdev_deactivate")
    {print "  jmp usbpdev_deactivate_ret"; print("\n");}

    else if(symname == "usbtd_slot_allocate_1slot")
    {print "  jmp usbtd_slot_allocate_1slot_ret"; print("\n");}
    else if(symname == "usbtd_slot_deallocate_1slot")
    {print "  jmp usbtd_slot_deallocate_1slot_ret"; print("\n");}

    else if(symname == "usbtd_slot_submit_and_verify_qtd32")
    {print "  jmp usbtd_slot_submit_and_verify_qtd32_ret"; print("\n");}
    else if(symname == "usbtd_slot_submit_and_verify_qh32")
    {print "  jmp usbtd_slot_submit_and_verify_qh32_ret"; print("\n");}

    else if(symname == "eehci_activate")
    {print "  jmp eehci_activate_ret"; print("\n");}
    else if(symname == "eehci_deactivate")
    {print "  jmp eehci_deactivate_ret"; print("\n");}

    else if(symname == "os_activate_all_released_pehcis_and_usbpdevs")
    {print "  jmp os_activate_all_released_pehcis_and_usbpdevs_ret"; print("\n");}
    else if(symname == "os_activate_mainmem_bypaddr")
    {print "  jmp os_activate_mainmem_bypaddr_ret"; print("\n");}
    else if(symname == "os_deactivate_mainmem_bypaddr")
    {print "  jmp os_deactivate_mainmem_bypaddr_ret"; print("\n");}

    else if(symname == "wimpdrv_write_eehci_config")
    {print "  jmp wimpdrv_write_eehci_config_ret"; print("\n");}
    else if(symname == "wimpdrv_read_eehci_config")
    {print "  jmp wimpdrv_read_eehci_config_ret"; print("\n");}

    else if(symname == "wimpdrv_write_eehci_status")
    {print "  jmp wimpdrv_write_eehci_status_ret"; print("\n");}
    else if(symname == "wimpdrv_read_eehci_status")
    {print "  jmp wimpdrv_read_eehci_status_ret"; print("\n");}

    else if(symname == "wimpdrv_write_eehci_usbtdreg")
    {print "  jmp wimpdrv_write_eehci_usbtdreg_ret"; print("\n");}
    else if(symname == "wimpdrv_read_eehci_usbtdreg")
    {print "  jmp wimpdrv_read_eehci_usbtdreg_ret"; print("\n");}





    // For test purpose
    /*else if(symname == "_wimpdrv_activate_private")
    {print "  jmp _wimpdrv_activate_private_ret"; print("\n");} 
    else if(symname == "_usbpdev_activate_private")
    {print "  jmp _usbpdev_activate_private_ret"; print("\n");}*/
}
method printAll()
{ 
    var n := 0;
    printHeader(); nl();

    //n := printWKHandler("wk_new_entry", wk_handler(), n); 
    //n := printFunction("wk_test_entry", wk_handler_obsolete(), n); 
    //nl();

    n := printFunction("wk_empty_partition_create", va_code_WK_EmptyPartitionCreate(), n); 
    printFunctionReturn("wk_empty_partition_create"); nl();
    n := printFunction("wk_empty_partition_destroy", va_code_WK_EmptyPartitionDestroy(), n); 
    printFunctionReturn("wk_empty_partition_destroy"); nl();

    n := printFunction("wimpdrv_activate", va_code_WimpDrv_Activate(), n); 
    printFunctionReturn("wimpdrv_activate"); nl();
    n := printFunction("wimpdrv_deactivate", va_code_WimpDrv_Deactivate(), n); 
    printFunctionReturn("wimpdrv_deactivate"); nl();

    n := printFunction("usbpdev_activate", va_code_USBPDev_Activate(), n); 
    printFunctionReturn("usbpdev_activate"); nl();
    n := printFunction("usbpdev_deactivate", va_code_USBPDev_Deactivate(), n); 
    printFunctionReturn("usbpdev_deactivate"); nl();

    n := printFunction("usbtd_slot_allocate_1slot", va_code_USBTD_slot_allocate_1slot(), n); 
    printFunctionReturn("usbtd_slot_allocate_1slot"); nl();
    n := printFunction("usbtd_slot_deallocate_1slot", va_code_USBTD_slot_deallocate_1slot(), n); 
    printFunctionReturn("usbtd_slot_deallocate_1slot"); nl();

    n := printFunction("usbtd_slot_submit_and_verify_qtd32", va_code_USBTD_slot_submit_and_verify_qtd32(), n); 
    printFunctionReturn("usbtd_slot_submit_and_verify_qtd32"); nl();
    n := printFunction("usbtd_slot_submit_and_verify_qh32", va_code_USBTD_slot_submit_and_verify_qh32(), n); 
    printFunctionReturn("usbtd_slot_submit_and_verify_qh32"); nl();

    n := printFunction("eehci_activate", va_code_EEHCI_Activate(), n); 
    printFunctionReturn("eehci_activate"); nl();
    n := printFunction("eehci_deactivate", va_code_EEHCI_Deactivate(), n); 
    printFunctionReturn("eehci_deactivate"); nl();

    n := printFunction("os_activate_all_released_pehcis_and_usbpdevs", va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs(), n); 
    printFunctionReturn("os_activate_all_released_pehcis_and_usbpdevs"); nl();
    n := printFunction("os_activate_mainmem_bypaddr", va_code_OS_Activate_MainMem_ByPAddr(), n); 
    printFunctionReturn("os_activate_mainmem_bypaddr"); nl();
    n := printFunction("os_deactivate_mainmem_bypaddr", va_code_OS_Deactivate_MainMem_ByPAddr(), n); 
    printFunctionReturn("os_deactivate_mainmem_bypaddr"); nl();

    n := printFunction("wimpdrv_write_eehci_config", va_code_WimpDrv_Write_eEHCI_Config(), n); 
    printFunctionReturn("wimpdrv_write_eehci_config"); nl();
    n := printFunction("wimpdrv_read_eehci_config", va_code_WimpDrv_Read_eEHCI_Config(), n); 
    printFunctionReturn("wimpdrv_read_eehci_config"); nl();

    n := printFunction("wimpdrv_write_eehci_status", va_code_WimpDrv_Write_eEHCI_Status(), n); 
    printFunctionReturn("wimpdrv_write_eehci_status"); nl();
    n := printFunction("wimpdrv_read_eehci_status", va_code_WimpDrv_Read_eEHCI_Status(), n); 
    printFunctionReturn("wimpdrv_read_eehci_status"); nl();

    n := printFunction("wimpdrv_write_eehci_usbtdreg", va_code_WimpDrv_Write_eEHCI_USBTDReg(), n); 
    printFunctionReturn("wimpdrv_write_eehci_usbtdreg"); nl();
    n := printFunction("wimpdrv_read_eehci_usbtdreg", va_code_WimpDrv_Read_eEHCI_USBTDReg(), n); 
    printFunctionReturn("wimpdrv_read_eehci_usbtdreg"); nl();



    // For test purpose
    /*n := printFunction("_wimpdrv_activate_private", va_code__wimpdrv_activate_private(), n); 
    printFunctionReturn("_wimpdrv_activate_private"); nl(); 

    n := printFunction("_usbpdev_activate_private", va_code__usbpdev_activate_private(), n); 
    printFunctionReturn("_usbpdev_activate_private"); nl();*/
    
    

    var bssglobals
        := map o | o in WK_GlobalDecls() 
                 :: WK_GlobalDecls()[o];
    //print(".globl g_devicedb, g_dma_virtbase, g_dma_physbase"); nl(); //CCH: should be reconsidered
    printBss(bssglobals);
}



