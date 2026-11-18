module

public import Silmaril.Sim.X86.GCert.Defs
public import Silmaril.Sim.Institution.Defs
public import Silmaril.Sim.X86.Max.Defs

/-!
# The G reduction as institution transfer (header)

The problem reduction `Silmaril.Sim.X86.G.xproblem_of_wproblem` (Wasm partial correctness ⇒ x86 property),
restated in the institution of simulators (`Silmaril.Sim.Institution`):

* `sig`: the signature: commands are the supported decoded instructions with their lengths
  (`XCmd`), locations `Loc`, values `BitVec 64`.
* `wasmM P host mi`: **the Wasm model**: a store (with the location globals laid out and
  holding registers and flag bits, `WellFormed`) steps on command `c` when the generated code
  `emit c` has a run in the Wasm semantics (`Steps P host`) that falls through; its view is
  `gview mi`. A program of commands is the P-inline program, run piece by piece.
* `x86M`: **the reference model**: `xRef` (`Ext.exec`, undefined flags concretized).
* The G simulator is a **complete** simulator of `x86M` (`complete`, a `Silmaril.Sim.CoSimulation`:
  every reference step is matched by a Wasm run, with equal views), so the
  `Institution.transfer_demonic` transfers every demonic sentence (every run of the program
  ends `Q`-related) from the Wasm model to the x86 model (`reduce_inst`).
* `maxSen`: the demonic sentence of `max` (`rax` ends as the signed maximum of `rdi`, `rsi`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GInst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim Silmaril.Sim.Institution Silmaril.Sim.X86.G Silmaril.Sim.X86.GCert
open Silmaril.X86 (Reg State)

/-- The supported commands: decoded instructions with lengths that have a method. -/
abbrev XCmd : Type := {c : Silmaril.X86.Ext.Instr × Nat // (emit c.1 c.2).isSome}

/-- The signature: supported instructions, no syscalls, the modelled locations. -/
def sig : Sig (BitVec 64) := ⟨XCmd, Empty, Loc⟩

/-- The instruction of a command of `sig`. -/
def instrOf : sig.Cmd → Silmaril.X86.Ext.Instr × Nat
  | .inl c => c.1
  | .inr e => e.elim

variable {H : Type}

/-- The frame of the simulator's instance `mi`. -/
abbrev frameOf (mi : ModuleInst) : Frame := Frame.forCall mi [] []

/-- A well-formed simulator store: location globals laid out, holding registers, RIP and
flag bits. -/
def WellFormed (mi : ModuleInst) (s : Store H) : Prop := ∃ R, GRegs s (frameOf mi) R

/-- **The Wasm model**: command `c` runs the generated code `emit c` to completion. -/
def wasmM (P : Profile) (host : HostSemantics H) (mi : ModuleInst) : Mod sig :=
  Mod.of (Machine.restrict
    { St := Store H
      view := gview mi
      step := fun c s s' => ∃ code, emit (instrOf c).1 (instrOf c).2 = some code ∧
        Steps P host ⟨s, frameOf mi, expression code⟩ ⟨s', frameOf mi, vals []⟩ }
    (WellFormed mi))

/-- **The reference model**: `Silmaril.X86.Ext.exec`, undefined flags concretized. -/
def x86M : Mod sig := Mod.of (xRef instrOf)

/-- `max`'s body as a program of `sig`. -/
def maxProgram : sig.Program :=
  Prog.block [.inl ⟨(.mov .q (.reg .rax) .rdi, 3), rfl⟩, .inl ⟨(.alu .q .cmp (.reg .rax) .rsi, 3), rfl⟩,
    .inl ⟨(.cmov .q .l .rax (.reg .rsi), 4), rfl⟩]

/-- **The sentence of `max`**: every run of the body ends with `rax` the signed maximum of the
initial `rdi` and `rsi`. -/
def maxSen : Sen sig :=
  .demonic (fun _ => True) maxProgram fun x y => ∀ a b, x (.reg .rdi) = some a →
    x (.reg .rsi) = some b → y (.reg .rax) = some (if a.slt b then b else a)

end Silmaril.Sim.X86.GInst
