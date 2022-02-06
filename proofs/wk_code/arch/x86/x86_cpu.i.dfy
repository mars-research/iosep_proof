include "x86_cpu.dfy"

lemma Lemma_EachRegsIsSameThenRegsAreSame(regs1:map<x86Reg, word>, regs2:map<x86Reg, word>)
    requires is_valid_x86_regs(regs1)
    requires is_valid_x86_regs(regs2)
    requires regs1[EAX] == regs2[EAX]
    requires regs1[EBX] == regs2[EBX]
    requires regs1[ECX] == regs2[ECX]
    requires regs1[EDX] == regs2[EDX]
    requires regs1[ESI] == regs2[ESI]
    requires regs1[EDI] == regs2[EDI]
    requires regs1[ESP] == regs2[ESP]
    requires regs1[EBP] == regs2[EBP]

    ensures regs1 == regs2
{
    forall r:x86Reg | true
        ensures regs1[r] == regs2[r]
    {
        assert r == EAX || r == EBX || r == ECX || r == EDX || r == ESI || r == EDI || r == ESP || r == EBP;
    }
}

