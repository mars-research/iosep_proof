Run verification
==================================
Dafny 2.3 (650a6bbe): https://github.com/dafny-lang/dafny
Vale-v0.3.10: https://github.com/project-everest/vale/releases/tag/v0.3.10

Machine: i9-9900K + 128GB memory
Command: make verify -j16


Line count
==================================
Result: 28518
Command: find . -name '*.dfy' | xargs wc -l