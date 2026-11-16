module

public import Silmaril.Wasm.Abstract.FullObs.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.Abstract.FunctorP.Thms
import Silmaril.Proofs.Wasm.Abstract.FullObsFaithful.Basic

/-!
# Checked code injects into the canonical full observation

The canonical full observation of a body is `FullObs.toFull f = (toAFun f, toInf f)`
(`Silmaril.Games.Abstract.FullFun`): finished behaviours (returns, payload-free traps, silent
divergence after finitely many calls) and infinite productive runs. The faithful observation of
`BodyTrace.faithful_iff` uses the pending calls `toPending` in place of the infinite runs.

**Abstract statement.** Over an import signature whose answer types are all inhabited:

* `toFull_eq_iff`: `toFull f = toFull g ↔ (toAFun f = toAFun g ∧ toPending f = toPending g)`,
  so (`toFull_eq_iff_erasedRun`) `toFull` is faithful exactly up to trap payloads. The ←
  direction is `BodyTrace.toInf_eq_of_toPending` and needs no hypothesis. For →, a call `m`
  pending after `cs` has an answer `a`, and the tree after `cs ++ [⟨m, a⟩]` has some
  observation: a finished path, or, if it has none, an infinite productive run (chosen
  classically, one answer per visible node). Both are seen by `toFull`, and their logs extend
  `cs ++ [⟨m, a⟩]`, so `m` is pending after `cs` in any body with the same full observation.
* `fullCollapseEquiv_iff_toInf`: the trap ≈ divergence version, `FullCollapseEquiv f g` exactly
  when the collapsed finished behaviours (`AFun.obsCollapse`) and the infinite runs agree.
* `exists_toFull_eq_toPending_ne`: the hypothesis is necessary. Two bodies calling different
  imports with empty answer types have no finished path and no infinite run, so the same full
  observation, and different pending calls. (`BodyTrace.exists_pend_limit_not_infPath` is a
  different matter, about limits of pending prefixes of a *family* of trees, and is not used.)

**Instance: checked code.** The internal-call signature `StoreCall.CallSig H` answers with
`Store H × Flow`, which is inhabited (`callSig_ar_nonempty`). Hence

* `toFull_denL_eq_iff`: `toFull (denL es) = toFull (denL es') ↔ OpEquivP H es es'`, through
  `toFull_eq_iff_erasedRun` and `FunctorP.opEquivP_iff`;
* `opCollapseEquivP_iff_toFull`: `OpCollapseEquivP H es es'` exactly when the full observations
  agree with trap and divergence identified in the finite part (`AFun.obsCollapse`) and the
  infinite runs equal, through `FunctorP.opCollapseEquivP_iff`.

So `toFull ∘ denL` is the **injection of code modulo the open interaction equivalence**
`OpEquivP` into the canonical `FullFun`. `OpEquivP` is operational (logged runs, logged traps
and logged pending calls of `CallXP`, at every oracle, store, frame and stack), independent of
the denotation. This is **not** contextual full abstraction: `OpEquivP` observes the code's
open interaction with an arbitrary oracle, not its behaviour in program contexts, and nothing
here relates it to a contextual equivalence.
-/

public section

namespace Silmaril.Wasm.Abstract.FullObsFaithful

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.FullObs

universe u

/-! ## The abstract statement -/

/-- **The full observation determines the pending calls** when every answer type is
inhabited. -/
theorem toFull_eq_iff {E : Sig.{u}} {S T A B : Type (u + 1)} (hE : ∀ m, Nonempty (E.Ar m))
    (f g : Hom E S T A B) :
    toFull f = toFull g ↔ (toAFun f = toAFun g ∧ toPending f = toPending g) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsFaithful.toFull_eq_iff hE f g

/-- **The full observation is faithful up to trap payloads** when every answer type is
inhabited. -/
theorem toFull_eq_iff_erasedRun {E : Sig.{u}} {S T A B : Type (u + 1)}
    (hE : ∀ m, Nonempty (E.Ar m)) (f g : Hom E S T A B) :
    toFull f = toFull g ↔ erasedRun f = erasedRun g :=
  (toFull_eq_iff hE f g).trans (faithful_iff f g)

/-- **Up to trap ≈ divergence**: collapsed finished behaviours and infinite runs. -/
theorem fullCollapseEquiv_iff_toInf {E : Sig.{u}} {S T A B : Type (u + 1)}
    (hE : ∀ m, Nonempty (E.Ar m)) (f g : Hom E S T A B) :
    FullCollapseEquiv f g ↔
      (AFun.ObsEquiv AFun.obsCollapse (toAFun f) (toAFun g) ∧ toInf f = toInf g) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsFaithful.fullCollapseEquiv_iff hE f g

/-- **The hypothesis is necessary**: with uninhabited answer types, the full observation does
not determine the pending calls. -/
theorem exists_toFull_eq_toPending_ne :
    ∃ (E : Sig.{0}) (f g : Hom E PUnit.{2} PUnit.{2} PUnit.{2} PUnit.{2}),
      toFull f = toFull g ∧ toPending f ≠ toPending g :=
  ⟨_, _, _, Silmaril.Proofs.Wasm.Abstract.FullObsFaithful.callEmpty_counterexample⟩

/-! ## Checked code -/

section
open Silmaril.Wasm.Abstract.StoreCall Silmaril.Wasm.Abstract.ExposePStruct
  Silmaril.Wasm.Abstract.FunctorP

variable {H : Type}

/-- Internal calls always have an answer. -/
theorem callSig_ar_nonempty (m : (CallSig H).Op) : Nonempty ((CallSig H).Ar m) :=
  ⟨((({} : Silmaril.Wasm.Execution.Core.Store H), Silmaril.Wasm.Binaryen.Flow.trap) :
    Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.Binaryen.Flow)⟩

/-- **Checked code injects into the canonical full observation** modulo the open interaction
equivalence `OpEquivP`. -/
theorem toFull_denL_eq_iff (es es' : List Silmaril.Wasm.Binaryen.BExpr) :
    toFull (denL (H := H) es) = toFull (denL es') ↔ OpEquivP H es es' :=
  (toFull_eq_iff_erasedRun callSig_ar_nonempty _ _).trans (opEquivP_iff es es')

/-- **Up to trap ≈ divergence**: `OpCollapseEquivP` is equality of the full observations with
trap and divergence identified in the finite part. -/
theorem opCollapseEquivP_iff_toFull (es es' : List Silmaril.Wasm.Binaryen.BExpr) :
    OpCollapseEquivP H es es' ↔
      (AFun.ObsEquiv AFun.obsCollapse (toFull (denL (H := H) es)).1 (toFull (denL es')).1 ∧
        (toFull (denL (H := H) es)).2 = (toFull (denL es')).2) :=
  (opCollapseEquivP_iff es es').symm.trans (fullCollapseEquiv_iff_toInf callSig_ar_nonempty _ _)

end

end Silmaril.Wasm.Abstract.FullObsFaithful
