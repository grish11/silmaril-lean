module

public import Silmaril.Sim.X86.G.Defs
public import Silmaril.Machine.X86.FnContract.Defs

/-!
# Example: signed `max` in x86-64, posed as a Wasm problem

The x86 function (System V, `long max(long a, long b)`):

```
48 89 f8        mov   rax, rdi
48 39 f0        cmp   rax, rsi
48 0f 4c c6     cmovl rax, rsi
c3              ret
```

`maxProg` is its straight-line body as decoded `Silmaril.X86.Ext.Instr`s with their byte lengths
(`maxBytes` the bytes; `Thms` checks that they decode to `maxProg`), `maxCode` the Wasm code the
G simulator generates for it (`emitProg maxProg = some maxCode`).

* `MaxPost`: the result register `rax` holds the signed maximum of `rdi` and `rsi`; the other
  registers are unchanged.
* **The x86 problem** `XProblem maxProg (fun _ => True) MaxPost` (`Silmaril.Sim.X86.G.XProblem`);
* **the Wasm problem** `WProblem P host maxCode (fun _ => True) MaxPost`: from any store holding
  registers `R` in its globals, every run of `maxCode` that stops leaves `rax`'s global holding
  the maximum.
* `maxSpec`: the System V contract's spec on `Open9.isa` (entry: `maxBytes` at RIP; post: `rax`
  is the signed maximum).

`Silmaril.Sim.X86.Max.Thms` solves the Wasm problem with the verification-condition generator
`wpc`, transports the solution to the x86 problem with `Silmaril.Sim.X86.G.xproblem_of_wproblem`,
lifts it to the bytes on the `Silmaril.X86.Ext` machine, and proves `maxContract`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Max

open Silmaril.Wasm
open Silmaril.X86 (Reg)
open Silmaril.X86.Ext (Sz RM Cond)
open Silmaril.Sim.X86.G

/-- The body of `max`, decoded, with byte lengths. -/
def maxProg : XProg :=
  [(.mov .q (.reg .rax) .rdi, 3), (.alu .q .cmp (.reg .rax) .rsi, 3), (.cmov .q .l .rax (.reg .rsi), 4)]

/-- The bytes of `max`, one list per instruction, `ret` last. -/
def maxBytes : List (List (BitVec 8)) :=
  [[0x48, 0x89, 0xf8], [0x48, 0x39, 0xf0], [0x48, 0x0f, 0x4c, 0xc6], [0xc3]]

/-- The Wasm code of `max` (P-inline over the G simulator). -/
def maxCode : List Instr :=
  [gget (.reg .rdi), gset (.reg .rax)] ++ nextCode 3 ++
  aluCode .cmp .rax .rsi ++ nextCode 3 ++
  cmovCode [gget .sf, gget .of, b64op .xor] .rax .rsi ++ nextCode 4

/-- The specification: `rax` is the signed maximum of the arguments `rdi`, `rsi`, and the other
registers are unchanged. -/
def MaxPost (R R' : Reg → BitVec 64) : Prop :=
  R' .rax = (if (R .rdi).slt (R .rsi) then R .rsi else R .rdi) ∧ ∀ r, r ≠ .rax → R' r = R r

/-- The contract's spec. -/
def maxSpec : Silmaril.Machine.X86.FnContract.Spec Silmaril.X86.MState where
  entry s := BytesAt s.memory s.core.rip maxBytes
  footprint _ _ := False
  post s t := t.core.read .rax =
    if (s.core.read .rdi).slt (s.core.read .rsi) then s.core.read .rsi else s.core.read .rdi

end Silmaril.Sim.X86.Max
