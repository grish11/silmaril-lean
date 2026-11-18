module

public import Silmaril.Sim.X86.GM.Defs
public import Silmaril.Sim.X86.SumTo.Defs

/-!
# Example with the stack and calls: the reduction toy `f` (`examples/wasm-sim/reduce/toy`)

```
sum_to:  48 c7 c0 00 00 00 00   mov  $0, %rax          dbl:  48 89 f8   mov %rdi, %rax
         48 85 ff               test %rdi, %rdi              48 01 c0   add %rax, %rax
         74 09                  je   .Ldone                  c3         ret
.Lloop:  48 01 f8               add  %rdi, %rax
         48 83 ef 01            sub  $1, %rdi        f:  53 / 41 54        push %rbx / push %r12
         eb f2                  jmp  (test)              48 83 ec 08       sub  $8, %rsp
.Ldone:  c3                     ret                      48 89 f3          mov  %rsi, %rbx
                                                         e8 d4 ff ff ff    call sum_to
                                                         49 89 c4          mov  %rax, %r12
                                                         48 89 df          mov  %rbx, %rdi
                                                         e8 df ff ff ff    call dbl
                                                         4c 01 e0          add  %r12, %rax
                                                         48 83 c4 08       add  $8, %rsp
                                                         41 5c / 5b        pop  %r12 / pop %rbx
                                                         c3                ret
```

`toyTab b`: the three functions placed at `b` (`sum_to` at `b`, `dbl` at `b + 0x16`, `f` at
`b + 0x1d`), as decoded instructions (bytes `toyBytes`, as linked in `toy.elf`, checked in
`Thms`). `toyWin sp`: the stack window `[sp - 32, sp + 8)` of a call of `f` with `rsp = sp`
(the two saved registers, the alignment slot, the return addresses of the inner calls, and the
caller's return address).

* **The Wasm problem** `LProblemM P host (toyWin sp) (dispCode (compileTabM (toyWin sp)
  (toyTab b))) (ToyPre b sp) ToyPost`;
* **the x86 problem** `XLProblemM (toyTab b) (toyWin sp) (ToyPre b sp) ToyPost`;
* `ToyPost`: `rax = (0 + 1 + ⋯ + rdi) + 2 · rsi`, `rbx`, `r12` and every register but `rax`,
  `rdi`, `rsp` restored, `rsp` popped past the return address, RIP the return address.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Toy

open Silmaril.X86 (Reg Word)
open Silmaril.X86.Ext (Sz RM Cond)
open Silmaril.Wasm.Execution
open Silmaril.Sim.X86.Loop Silmaril.Sim.X86.GM
open Silmaril.Sim.X86.SumTo (tri)

/-- `sum_to`, `dbl` and `f` placed at `b`. -/
def toyTab (b : Word) : XTab :=
  [(b, .movI .q (.reg .rax) 0, 7), (b + 0x07, .test .q (.reg .rdi) .rdi, 3),
    (b + 0x0a, .jcc8 .e 0x09, 2), (b + 0x0c, .alu .q .add (.reg .rax) .rdi, 3),
    (b + 0x0f, .aluI8 .q .sub (.reg .rdi) 1, 4), (b + 0x13, .jmp8 0xf2, 2), (b + 0x15, .ret, 1),
    (b + 0x16, .mov .q (.reg .rax) .rdi, 3), (b + 0x19, .alu .q .add (.reg .rax) .rax, 3),
    (b + 0x1c, .ret, 1),
    (b + 0x1d, .push .rbx, 1), (b + 0x1e, .push .r12, 2), (b + 0x20, .aluI8 .q .sub (.reg .rsp) 8, 4),
    (b + 0x24, .mov .q (.reg .rbx) .rsi, 3), (b + 0x27, .call 0xffffffd4, 5),
    (b + 0x2c, .mov .q (.reg .r12) .rax, 3), (b + 0x2f, .mov .q (.reg .rdi) .rbx, 3),
    (b + 0x32, .call 0xffffffdf, 5), (b + 0x37, .alu .q .add (.reg .rax) .r12, 3),
    (b + 0x3a, .aluI8 .q .add (.reg .rsp) 8, 4), (b + 0x3e, .pop .r12, 2), (b + 0x40, .pop .rbx, 1),
    (b + 0x41, .ret, 1)]

/-- The bytes of each instruction of `toyTab`, in order. -/
def toyBytes : List (List (BitVec 8)) :=
  [[0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00], [0x48, 0x85, 0xff], [0x74, 0x09],
    [0x48, 0x01, 0xf8], [0x48, 0x83, 0xef, 0x01], [0xeb, 0xf2], [0xc3],
    [0x48, 0x89, 0xf8], [0x48, 0x01, 0xc0], [0xc3],
    [0x53], [0x41, 0x54], [0x48, 0x83, 0xec, 0x08], [0x48, 0x89, 0xf3],
    [0xe8, 0xd4, 0xff, 0xff, 0xff], [0x49, 0x89, 0xc4], [0x48, 0x89, 0xdf],
    [0xe8, 0xdf, 0xff, 0xff, 0xff], [0x4c, 0x01, 0xe0], [0x48, 0x83, 0xc4, 0x08], [0x41, 0x5c],
    [0x5b], [0xc3]]

/-- The stack window of a call of `f` with `rsp = sp`. -/
def toyWin (sp : Word) : Win := ⟨sp - 32, 40, true⟩

/-- The precondition: RIP at `f`, `rsp = sp` (the window does not wrap), and the return address
(at window offset 32) outside the code. -/
def ToyPre (b sp : Word) (R : Reg → Word) (w : Word) (B : ByteArray) : Prop :=
  w = b + 0x1d ∧ R .rsp = sp ∧ 32 ≤ sp.toNat ∧ sp.toNat + 8 ≤ 2 ^ 64 ∧
    ∃ ret, Memory.load B 32 8 = some ret ∧ 0x42 ≤ (ret - b).toNat

/-- The postcondition: `rax = sum_to(rdi) + dbl(rsi)`, the return address in RIP, `rsp`
popped, every other register but `rdi` restored. -/
def ToyPost (R : Reg → Word) (_w : Word) (B : ByteArray) (R' : Reg → Word) (w' : Word) : Prop :=
  R' .rax = BitVec.ofNat 64 (tri (R .rdi).toNat) + 2 * R .rsi ∧ R' .rsp = R .rsp + 8 ∧
    (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsp → R' r = R r) ∧ Memory.load B 32 8 = some w'

end Silmaril.Sim.X86.Toy
