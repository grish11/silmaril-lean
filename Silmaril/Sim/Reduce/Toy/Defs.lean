module

public import Silmaril.Sim.Reduce.Defs
public import Silmaril.Machine.X86.Open9.Thms
public import Silmaril.Sim.X86.Toy.Defs

/-!
# The toy reduction problem: statements

The x86 side and the Wasm statements of the toy of `docs/wasm-sim-reduction.md`
(`examples/wasm-sim/reduce/toy`): `f(a, b) = sum_to(a) + dbl(b)` calls a looping callee and a
straight-line callee. `tools/wasm-sim-reduce emit` turns its manifest into the P-calls modules
and the problem DAG whose nodes name the constants below.

* `code`: the `.text` of `toy.elf` (60 bytes; position independent, so every placement
  `base` is a problem: the `FnCorrectDet` template quantifies over it).
* `spec g base`: the System V contract of function `g` placed at `base` on `Open9.isa`.
* `isaGoal g`: the ISA problem: the contract on `Open9.isa` at every placement (the shape of
  `Silmaril.Problems.FnCorrectDet Open9.isa (spec g)`, which is the same proposition).
* `J K Init g`: the Wasm problem of `g` for a sound simulator `K` of `Open9.isa`
  (`specWasm`, every placement).
* `piece K Init g`: the per-function piece, `AGPiece (J K Init) callees g`: `g`'s Wasm problem
  assuming its callees'. Three independent pieces; `Toy.Thms.isa_of_pieces` assembles them.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Toy

open Silmaril.X86 (MState Word Byte)
open Silmaril.Machine.X86.FnContract (Spec)
open Silmaril.Machine.X86 (Open9.isa)

/-- `.text` of `examples/wasm-sim/reduce/toy/toy.elf` (`sum_to` at 0, `dbl` at `0x10`, `f` at
`0x17`). -/
def code : List Byte :=
  [0x31, 0xc0, 0x48, 0x85, 0xff, 0x74, 0x08, 0x48, 0x01, 0xf8, 0x48, 0xff, 0xcf, 0x75, 0xf8,
   0xc3, 0x48, 0x89, 0xf8, 0x48, 0x01, 0xc0, 0xc3, 0x53, 0x41, 0x54, 0x48, 0x83, 0xec, 0x08,
   0x48, 0x89, 0xf3, 0xe8, 0xda, 0xff, 0xff, 0xff, 0x49, 0x89, 0xc4, 0x48, 0x89, 0xdf, 0xe8,
   0xdf, 0xff, 0xff, 0xff, 0x4c, 0x01, 0xe0, 0x48, 0x83, 0xc4, 0x08, 0x41, 0x5c, 0x5b, 0xc3]

/-- The toy's functions. -/
inductive Fn where
  | sumTo
  | dbl
  | f
  deriving DecidableEq

/-- Offsets in `code`. -/
def Fn.off : Fn → Nat
  | .sumTo => 0
  | .dbl => 0x10
  | .f => 0x17

/-- `0 + 1 + ⋯ + n` (on `Nat`). -/
def triN : Nat → Nat
  | 0 => 0
  | n + 1 => triN n + (n + 1)

/-- `0 + 1 + ⋯ + x` modulo `2^64`. -/
def tri (x : Word) : Word := BitVec.ofNat 64 (triN x.toNat)

/-- The code is loaded at `base` and `rip` is at `g`. -/
def Entered (base : Word) (g : Fn) (s : MState) : Prop :=
  Silmaril.X86.Ext.Loaded s.memory base code ∧ s.core.rip = base + BitVec.ofNat 64 g.off

/-- The System V contracts. `f`'s entry asks for its 40-byte stack window
(`Silmaril.Sim.X86.Toy.toyWin`: two saved registers, the alignment slot, the inner return address,
the caller's) readable, writable and backed, disjoint from the code, and a return address
outside the code; its footprint is the window. -/
def spec : Fn → Word → Spec MState
  | .sumTo, base =>
    { entry := Entered base .sumTo
      footprint := fun _ _ => False
      post := fun s t => t.core.read .rax = tri (s.core.read .rdi) }
  | .dbl, base =>
    { entry := Entered base .dbl
      footprint := fun _ _ => False
      post := fun s t => t.core.read .rax = s.core.read .rdi + s.core.read .rdi }
  | .f, base =>
    { entry := fun s => Entered base .f s ∧
        Silmaril.Sim.X86.GM.WinOK s.memory (Silmaril.Sim.X86.Toy.toyWin (s.core.read .rsp)) ∧
        32 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat + 8 ≤ 2 ^ 64 ∧
        (base.toNat + 0x3c ≤ (s.core.read .rsp).toNat - 32 ∨
          (s.core.read .rsp).toNat + 8 ≤ base.toNat) ∧
        0x3c ≤ (Silmaril.Machine.X86.Open.retOf s.core s.memory - base).toNat
      footprint := fun s a => (Silmaril.Sim.X86.Toy.toyWin (s.core.read .rsp)).Mem a
      post := fun s t =>
        t.core.read .rax = tri (s.core.read .rdi) + (s.core.read .rsi + s.core.read .rsi) }

/-- **The ISA problem** of `g`: its contract on `Open9.isa` at every placement. -/
def isaGoal (g : Fn) : Prop := ∀ base, (spec g base).Total Open9.isa

/-- The call graph. -/
def callees : Fn → List Fn
  | .f => [.sumTo, .dbl]
  | _ => []

/-- Ranks witnessing that the call graph is acyclic. -/
def rank : Fn → Nat
  | .f => 1
  | _ => 0

variable {W : Type}

/-- **The Wasm problem** of `g` on a simulator `K` of `Open9.isa`. -/
def J (K : SoundSim MState W) (Init : W → Prop) (g : Fn) : Prop :=
  ∀ base, specWasm Open9.isa (spec g base) K Init

/-- **The per-function piece** of `g`. -/
def piece (K : SoundSim MState W) (Init : W → Prop) (g : Fn) : Prop :=
  AGPiece (J K Init) callees g

end Silmaril.Sim.Reduce.Toy
