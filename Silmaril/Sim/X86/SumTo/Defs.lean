module

public import Silmaril.Sim.X86.Loop.Defs

/-!
# Example with a loop: `sum_to` (`examples/wasm-sim/x86/tests/funcs.S`), posed as a Wasm problem

```
sum_to:  31 c0       xor  eax, eax
         48 85 ff    test rdi, rdi
         74 08       je   2f
1:       48 01 f8    add  rax, rdi
         48 ff cf    dec  rdi
         75 f8       jne  1b
2:       c3          ret
```

`sumTab b`: the body placed at address `b`, as a table of decoded instructions (`Thms` checks
that `sumBytes` decode to it); the `ret` at `b + 15` is not in the table, so an `XRun` ends
there. `tri n = 0 + 1 + ⋯ + n`.

* **The x86 problem** `XLProblem (sumTab b) (fun _ w => w = b) SumPost`: every run from RIP `b`
  ends with `rax = 0 + 1 + ⋯ + rdi` (modulo `2^64`).
* **The Wasm problem** `LProblem P host (dispCode (compileTab (sumTab b))) …`, solved in
  `Silmaril.Proofs.Sim.X86.SumTo.Wasm` with the dispatcher's cut-point rule and one
  straight-line Wasm problem per entry.
-/

@[expose] public section

namespace Silmaril.Sim.X86.SumTo

open Silmaril.X86 (Reg Word)
open Silmaril.X86.Ext (Sz RM Cond)
open Silmaril.Sim.X86.Loop

/-- `sum_to` placed at `b`, without its final `ret` (at `b + 15`). -/
def sumTab (b : Word) : XTab :=
  [(b, .alu .d .xor (.reg .rax) .rax, 2), (b + 2, .test .q (.reg .rdi) .rdi, 3),
    (b + 5, .jcc8 .e 8, 2), (b + 7, .alu .q .add (.reg .rax) .rdi, 3),
    (b + 10, .incdec .q true (.reg .rdi), 3), (b + 13, .jcc8 .ne 0xf8, 2)]

/-- The bytes of `sum_to`, one list per instruction, `ret` last. -/
def sumBytes : List (List (BitVec 8)) :=
  [[0x31, 0xc0], [0x48, 0x85, 0xff], [0x74, 0x08], [0x48, 0x01, 0xf8], [0x48, 0xff, 0xcf],
    [0x75, 0xf8], [0xc3]]

/-- `0 + 1 + ⋯ + n`. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

/-- The specification: the run ends at the `ret` (`b + 15` for code at `b`), with
`rax = 0 + 1 + ⋯ + rdi` modulo `2^64` and every register but `rax` and `rdi` unchanged. -/
def SumPost (R : Reg → Word) (b : Word) (R' : Reg → Word) (w' : Word) : Prop :=
  R' .rax = BitVec.ofNat 64 (tri (R .rdi).toNat) ∧ (∀ r, r ≠ .rax → r ≠ .rdi → R' r = R r) ∧
    w' = b + 15

end Silmaril.Sim.X86.SumTo
