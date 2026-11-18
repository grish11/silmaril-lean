module

public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Logic.SAT.Carrier.Defs

/-!
# The acceptor kit: from a checker's Core soundness to component soundness

A certificate-checking acceptor is a list-taking component (`ListLift.ListComp`) whose exports
take a problem and a certificate and answer `bool`. Its component-level soundness has the same
shape for every checker: an accepting reference behaviour of an export on the values of `p`
and `c` means that some property `Goal p c` holds, for instance `chk p c = true` for a Lean
checker `chk`, or `p ∈ L` for its language. The proof always combines the same three facts:

1. `ListLift.acceptSound`: an accepting call lowers the arguments from the instance store
   (`LParams`) and the core function returns a nonzero `i32`;
2. `ListLift.params_holds` with the component's **bump allocator** (`BumpAlloc`): the lowering
   ends in a store of the invariant whose memory holds the arguments (`FlatHolds`);
3. the checker's **Core obligation**: from such a store and flat arguments, a nonzero answer of
   the core function implies `Goal p c`.

This file names the pieces; `Silmaril.Wasm.Acceptor.Bridge.Thms` proves the composition once.

* `Kit c`: the generic, checker-independent facts of the component `c`: the instance `I` of
  its module (`ListComp.Inst`), well-formedness (`ListComp.Good`), the bump allocator at the
  allocator's address for the component's memory with an invariant `Inv` (heap pointer `t`),
  and the invariant at the instance store with the heap pointer `base`;
* `CheckerExport c α β`: an export of `c` on a problem `p : α` and a certificate `q : β`, with
  their values `enc p q` (well typed) and the property `Goal p q` an accepting call promises;
* `CheckerExport.CoreSound K e`: **the per-checker obligation**, stated at the Core level only
  (no component semantics): from every store of `K.Inv` whose ABI memory holds the arguments
  (`FlatHolds … K.base t`), every run of the export's core function returning a nonzero `i32`
  gives `Goal p q`.

The checkers of `Silmaril.Wasm.Examples.{SatAccept,LratAccept,FarkasAccept}` are instances. A
Wasm checker need not agree with a Lean reference checker on every input (the Farkas acceptor
rejects valid certificates outside its bounds, the LRAT acceptor needs no empty-clause step on a
problem with an empty input clause), so `Goal` is the property its Core proof gives; `CheckerExport.sound_accepts` and `sound_lang` (`Thms`) read it as `Accepts chk` and as
a language `L ⊇ Accepts chk` when it is `chk p q = true`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm.Execution.Core (Store Steps invoke Frame vals)
open Silmaril.Wasm.Component.Reference.ListLift (ListComp ListExport LTy LVal BumpAlloc FlatHolds
  memBytesOf)
open Silmaril.Wasm.Numerics (Profile)

/-- **The checker-independent facts of a list component**: its instance, well-formedness, its
bump allocator for its memory, and the invariant at the instance store. -/
structure Kit (c : ListComp) where
  /-- The instance of the module. -/
  I : Silmaril.Wasm.Game.ScalarInstance
  /-- The component is in the fragment. -/
  good : c.Good
  /-- `I` is the instance `acceptSound` assumes. -/
  inst : c.Inst I
  /-- The size of the ABI memory. -/
  N : Nat
  /-- The store invariant, with the heap pointer. -/
  Inv : Store Nat → Nat → Prop
  /-- The allocator is a bump allocator for the component's memory. -/
  bump : ∀ P : Profile, BumpAlloc P (c.coreAddr I c.reallocName) c.memIdx N Inv
  /-- The heap pointer of the instance store. -/
  base : Nat
  /-- The instance store meets the invariant. -/
  init : Inv I.store base

/-- **An export of a checker**: the export `x` of `c`, the values `enc p q` of its parameters
for a problem `p` and a certificate `q`, and what an accepting call promises, `Goal p q`. -/
structure CheckerExport (c : ListComp) (α β : Type) where
  /-- The export. -/
  x : ListExport
  /-- It is an export of `c`. -/
  mem : x ∈ c.exports
  /-- The values of the parameters. -/
  enc : α → β → List LVal
  /-- They have the parameter types. -/
  typed : ∀ p q, LTy.checkParams (x.params.map (·.2)) (enc p q) = true
  /-- What an accepting call means. -/
  Goal : α → β → Prop

/-- **The per-checker Core obligation**: from a store of the invariant whose memory holds the
arguments, a nonzero answer of the core function means `Goal`. -/
def CheckerExport.CoreSound {c : ListComp} {α β : Type} (K : Kit c) (e : CheckerExport c α β) :
    Prop :=
  ∀ (P : Profile) (p : α) (q : β) (s : Store Nat) (t : Nat)
    (fl : List Silmaril.Wasm.Execution.Core.Val) (s' : Store Nat) (f' : Frame) (r : BitVec 32),
    K.Inv s t → FlatHolds (memBytesOf s c.memIdx) K.base t (e.x.params.map (·.2)) (e.enc p q) fl →
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s (c.coreAddr K.I e.x.core) fl)
      ⟨s', f', vals [.i32 r]⟩ → r ≠ 0 → e.Goal p q

end Silmaril.Wasm.Acceptor
