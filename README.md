## Quick guide in adding this LLVM pass

1. Add *PreSpill.h* and *PreSpill.cpp* in the folder **&lt;your LLVM folder>/lib/CodeGen*

2. Add the pass *PreSpill.cpp* in the CMake file  *&lt;your LLVM folder>/lib/CodeGen/CmakeLists.txt*
3. Create the pass in *&lt;your LLVM folder>/include/llvm/CodeGen/Passes.h*  by adding:

```C++
FunctionPass *createPreSpillPass();
```

4. Initialize the pass in *&lt;your LLVM folder>/include/llvm/InitializePasses.h*

```C++
void initializePreSpillPass(PassRegistry&);
```

5. Add the pass to the pass queue in  *&lt;your LLVM folder>/lib/CodeGen/TargetPassConfig.cpp* in front of the register allocator and after the pre allocation passes:

```c++
addPass(createPreSpillPass());
```

6. Build LLVM

