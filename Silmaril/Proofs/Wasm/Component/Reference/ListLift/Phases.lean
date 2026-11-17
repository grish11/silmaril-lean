module

public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.RefToSpec

/-!
# The two phases of an accepting call of `ListComp.toRef`

As for simple components (`Silmaril.Proofs.Wasm.Component.Reference.Phases`), `AcceptSound` is
proved in two phases that meet at the configuration `afterInst` reached by instantiating
`c.toRef`:

* `liftedFtL x`: the resolved function type of the lift of export `x` (its named parameters at
  `LTy.toClosed`, result `bool`, synchronous), and `liftedFuncsL P c I`: the lifted functions of
  the exports, at the addresses of their core functions, with the options `memory` (address
  `memIdx`)
  and `realloc` (the allocator's address), in instance `0`;
* `InstPhaseL`: instantiating `c.toRef` only reaches `afterInst` with the instance's core store
  (up to the host type) and these functions, and the export map `exportMapL c`;
* `CallPhaseL`: every behaviour of calling the `j`-th function from there on well-typed values
  that returns `true` has the Core-level explanation of `AcceptSound`.

`acceptSound_of_phases` combines them.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Steps invoke Frame vals)

/-- The resolved function type of the lift of export `x`. -/
def liftedFtL (x : ListExport) : WIT.FuncType Empty RtId :=
  ⟨x.params.map fun p => (p.1, p.2.toClosed), some (.prim .bool), false⟩

/-- The canonical options of the lifts: memory address `memIdx` and the allocator. -/
def optsL (P : Profile) (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance) :
    CanonOpts (core3P P) :=
  { memory := some (show (core3P P).MemAddr from c.memIdx), realloc := some (c.coreAddr I c.reallocName) }

/-- The lifted functions of the exports of `c`. -/
noncomputable def liftedFuncsL (P : Profile) (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance) :
    List (CFuncInst (core3P P)) :=
  c.exports.map fun x => .lifted (c.coreAddr I x.core) (liftedFtL x) (optsL P c I) ⟨0⟩

/-- The function exports of the root instance: export `i` is function `i`. -/
def exportMapL (c : ListComp) : List (String × FuncId) :=
  c.exports.mapIdx fun i x => (x.name, ⟨i⟩)

/-- **The instantiation phase** of `c.toRef`. -/
def InstPhaseL : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance),
    c.Good → c.Inst I →
    ∃ cs : (core3P P).Store (CanonHost (core3P P)),
      Store.mapH (fun _ => 0) cs = I.store ∧
      ∀ r ∈ instBehaviours prof (refHost P) (initConfig ()) c.toRef [],
        r = .instance (afterInst P cs (liftedFuncsL P c I)) ⟨0⟩ (exportMapL c)

/-- **The call phase** of an accepting call. -/
def CallPhaseL : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance),
    c.Good → c.Inst I →
    ∀ (cs : (core3P P).Store (CanonHost (core3P P))), Store.mapH (fun _ => 0) cs = I.store →
    ∀ (j : Nat) (hj : j < c.exports.length) (vs : List LVal),
      LTy.checkParams (c.exports[j].params.map (·.2)) vs = true →
      Outcome.returns (some [.bool true]) ∈ callBehaviours prof (refHost P)
          (afterInst P cs (liftedFuncsL P c I)) ⟨0⟩ ⟨j⟩ (vs.map LVal.toRef) →
      ∃ (s : Silmaril.Wasm.Execution.Core.Store Nat) (fl : List Silmaril.Wasm.Execution.Core.Val)
        (s' : Silmaril.Wasm.Execution.Core.Store Nat) (f' : Frame) (r : BitVec 32),
        LParams P (c.coreAddr I c.reallocName) c.memIdx (c.exports[j].params.map (·.2)) vs I.store fl s ∧
        Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s (c.coreAddr I c.exports[j].core) fl)
          ⟨s', f', vals [.i32 r]⟩ ∧ r ≠ 0

/-- The export map finds every export at its index. -/
theorem exportMapL_lookup {c : ListComp} (hc : c.Good) (j : Nat) (hj : j < c.exports.length) :
    (exportMapL c).lookup c.exports[j].name = some ⟨j⟩ := by
  have h := Silmaril.Proofs.Wasm.Component.Reference.lookup_mapIdx_name (·.name) 0 c.exports j hj hc.names
  simp only [Nat.zero_add] at h
  exact h

/-- **Accepting calls have a Core-level explanation, from the two phases.** -/
theorem acceptSound_of_phases (hA : InstPhaseL) (hB : CallPhaseL) (c : ListComp) :
    AcceptSound c := by
  intro P prof I hc hi x hx vs hvs hb
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < c.exports.length, c.exports[j] = x :=
    List.getElem_of_mem hx
  obtain ⟨cs, hcs, hinst⟩ := hA P prof c I hc hi
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have he := hinst _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterInst P cs (liftedFuncsL P c I) ∧ inst = ⟨0⟩ ∧
        es = exportMapL c := by
      simpa only [InstResult.instance.injEq] using he
    have hf : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (exportMapL_lookup hc j hj))
    subst hf
    exact hB P prof c I hc hi cs hcs j hj vs hvs hb
  · cases h
  · cases h

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
