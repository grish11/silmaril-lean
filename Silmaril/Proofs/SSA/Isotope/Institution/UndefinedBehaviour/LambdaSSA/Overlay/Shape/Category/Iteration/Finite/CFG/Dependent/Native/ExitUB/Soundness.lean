module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Refinement
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (Model)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (Result)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Primitives emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Codes)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind bind_return)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (routed_order)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (fault_bind diverge_bind)

universe u v w

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)]
variable {X : Silmaril.Ty Empty} {Γ R L : List (Silmaril.Ty Empty)}
variable {captures seeds results states : Nat}

private theorem forward_exit (M : Model.{u,v,w} Φ Γ.length) (i : Fin L.length) (a : Value M.α) (s : M.σ) :
    denote (.native (jump (Φ := Φ) (Γ := L.get i :: Γ) i rfl (.var 0))) (extendModel M a) s =
      WithTop.some {Outcome.ret i a s} := by
  apply WithTop.coe_inj.mpr
  ext o
  let branch : Typed Φ (L.get i :: Γ) L := jump i rfl (.var 0)
  refine (mem_nativeOutcomes_iff branch (M := extendModel M a)
    ((envOfBound_agrees M.bound).extend a) s o).trans ?_
  refine Iff.trans ?_ Set.mem_singleton_iff.symm
  cases o with
  | ret j b t =>
    have eval {label : Nat} {v : Value M.α} {final : M.σ}
        (run : Region.Eval M.instr (extend (envOfBound M.bound) a)
          (.br i.val (.var 0)) s label v final) :
        label = i.val ∧ v = a ∧ final = s := by
      cases run with | br value => cases value; exact ⟨rfl, rfl, rfl⟩
    change Region.Eval M.instr (extend (envOfBound M.bound) a)
      (.br i.val (.var 0)) s j.val b t ↔ _
    constructor
    · intro run
      obtain ⟨label, value, final⟩ := eval run
      exact (Outcome.ret.injEq ..).mpr ⟨Fin.ext label, value, final⟩
    · intro eq
      have same : (Outcome.ret j b t : Outcome L.length M.α M.σ) = .ret i a s := eq
      obtain ⟨label, value, final⟩ := Outcome.ret.inj same
      rw [label, value, final]
      exact .br .var
  | fault t =>
    constructor
    · intro run
      cases run with | br arg => cases arg
    · intro eq
      cases eq
  | diverge =>
    constructor
    · intro run
      cases run.unfold with
      | br arg => cases arg
      | core step => cases step
    · intro eq
      cases eq

theorem denote_exitContinuation (M : Model.{u,v,w} Φ Γ.length) (selected : Fin L.length → Bool)
    (i : Fin L.length) (a : Value M.α) (s : M.σ) :
    denote (exitContinuation (Γ := Γ) selected i) (extendModel M a) s =
      if selected i then ⊤ else WithTop.some {Outcome.ret i a s} := by
  unfold exitContinuation
  split
  · rfl
  · exact forward_exit M i a s

theorem denote_noExitUB (raw : Typed Φ Γ L) (M : Shape.Model.{u,0,v,w} Φ Γ) (s : M.raw.σ) :
    Shape.denote (withExitUB raw (fun _ => false)) M s = Shape.denote (.native raw) M s := by
  let result := denote (.native raw) M.raw s
  change Behaviour.bind result (fun i a t => denote (exitContinuation (fun _ => false) i)
    (extendModel M.raw a) t) = result
  calc
    _ = result.bind (fun i a t => WithTop.some {Outcome.ret i a t}) := by
      congr 1
      funext i a t
      exact forward_exit M.raw i a t
    _ = _ := bind_return result

variable [DecidableEq Φ] {raw target : Typed Φ [X] L} {left right : Readback Φ X R L}

theorem classify_exitUB (accepted : recognizeRouterUnits R raw = some left)
    (selected : Fin L.length → Bool) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) :
    Shape.denote (withExitUB raw selected) (model prim (emptyBindings.push (C.capture c))) s =
      (left.executeExitUB selected C prim c s).routed C.carrier := by
  let M := model prim (emptyBindings.push (C.capture c))
  let next (i : Fin L.length) a t := denote (exitContinuation (Γ := [X]) (Φ := Φ) selected i)
    (extendModel M.raw a) t
  change Behaviour.bind (Shape.denote (.native raw) M s) next = _
  rw [classify_recognizedRouterUnits accepted C prim c s]
  unfold Readback.executeExitUB
  cases left.execute C prim c s with
  | ub => exact Behaviour.top_bind _
  | fault t => exact fault_bind t _
  | diverge => exact diverge_bind _
  | ret b t =>
    let i := (C.result b).1
    let a := (C.result b).2.val
    refine (return_bind i a t next).trans ?_
    change denote (exitContinuation (Γ := [X]) (Φ := Φ) selected i) (extendModel M.raw a) t =
      (markExitUB C selected (.ret b t)).routed C.carrier
    by_cases h : selected (C.result b).1
    · rw [exitContinuation, ite_eq_left h, markExitUB, ite_eq_left h]
      rfl
    · rw [exitContinuation, ite_eq_right h, markExitUB, ite_eq_right h]
      exact forward_exit M.raw i a t

omit [DecidableEq Φ] in
private theorem check_codes_iff (left right : Readback Φ X R L) (lUB rUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    checkExitUB left right lUB rUB C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      (left.executeExitUB lUB C prim c s).refines (right.executeExitUB rUB C prim c s) := by
  simp [checkExitUB, counterexampleExitUB, List.mem_finRange]

theorem check_exitUB_iff (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right) (lUB rUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    checkExitUB left right lUB rUB C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      let M := model prim (emptyBindings.push (C.capture c))
      Shape.denote (withExitUB raw lUB) M s ≤ Shape.denote (withExitUB target rUB) M s := by
  rw [check_codes_iff]
  refine forall_congr' fun c => forall_congr' fun s => ?_
  dsimp only
  rw [classify_exitUB hl lUB C prim c s, classify_exitUB hr rUB C prim c s]
  exact (routed_order C.carrier _ _).symm

theorem counterexample_exitUB_point (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right) (lUB rUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    {c : Fin captures} {s : Fin states}
    (found : counterexampleExitUB left right lUB rUB C prim = some (c, s)) :
    let M := model prim (emptyBindings.push (C.capture c))
    ¬ Shape.denote (withExitUB raw lUB) M s ≤ Shape.denote (withExitUB target rUB) M s := by
  have failed : ¬ (left.executeExitUB lUB C prim c s).refines (right.executeExitUB rUB C prim c s) := by
    simpa using List.find?_some found
  dsimp only
  rw [classify_exitUB hl lUB C prim c s, classify_exitUB hr rUB C prim c s]
  exact fun le => failed ((routed_order C.carrier _ _).mp le)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB
