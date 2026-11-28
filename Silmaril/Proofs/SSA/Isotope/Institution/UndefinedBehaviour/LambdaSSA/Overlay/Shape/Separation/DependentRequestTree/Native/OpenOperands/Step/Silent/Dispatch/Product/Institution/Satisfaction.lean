module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Institution.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (lambdaSSA)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (CallerEnumeration ConfigurationEnumeration ReplyEnumeration)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Table
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open CFG.Dependent.Native (withExitUB denote_noExitUB)
open Syntax (Payload Primitives emptyBindings model)
open CategoryTheory (Discrete)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {A : Syntax.Ty} {L : List Syntax.Ty}

private theorem outcome_order {n : Nat} {σ : Type v} (p q : Behaviour n Unit σ) :
    (∀ o, observesOutcome p o → observesOutcome q o) ↔ p ≤ q := by
  induction p using WithTop.recTopCoe <;> induction q using WithTop.recTopCoe
  case top.top => simp
  case top.coe outcomes =>
    constructor
    · intro included
      exact (WithTop.coe_ne_top (included none rfl)).elim
    · intro order
      exact (WithTop.coe_ne_top (top_unique order)).elim
  case coe.top outcomes =>
    simp only [le_top, iff_true]
    intro o _
    cases o <;> simp [observesOutcome, Behaviour.possible]
  case coe.coe lower upper =>
    rw [WithTop.coe_le_coe]
    constructor
    · intro included out mem
      exact included (some out) mem
    · intro included o mem
      cases o with
      | none => exact (WithTop.coe_ne_top mem).elim
      | some _ => exact included mem

theorem sat_le_iff (M : CodedModel.{u,v} Φ A) (e f : CodedEntry Φ A L) :
    M.Sat (.le e f) ↔
      ∀ s : M.store, LambdaSSA.UB.Overlay.denote e.region (M.atEntry e) s ≤ LambdaSSA.UB.Overlay.denote f.region (M.atEntry f) s := by
  change M.observations e ⊆ M.observations f ↔ _
  simp only [CodedModel.observations, Set.subset_def, Set.mem_ofPred_eq]
  constructor
  · intro included s
    exact (outcome_order _ _).mp fun o h => included (s, o) h
  · intro order ⟨s, o⟩ h
    exact (outcome_order _ _).mpr (order s) o h

/-- On the native sublanguage the existing LambdaSSA room interprets
exactly the same observations. -/
theorem sat_native_iff (M : CodedModel.{u,v} Φ A) (r t : CFG.Dependent.Native.Typed Φ [A] L) :
    M.Sat (.le ⟨A, id, withExitUB r (fun _ => false)⟩ ⟨A, id, withExitUB t (fun _ => false)⟩) ↔
      ((lambdaSSA.{u,0,v} Φ L.length).room [A].length).Sat (Discrete.mk M.raw)
        (.le ⟨r.val, r.property.scoped⟩ ⟨t.val, t.property.scoped⟩) := by
  rw [sat_le_iff]
  let shaped := model M.handler (emptyBindings.push M.caller)
  change (∀ s, Shape.denote (withExitUB r (fun _ => false)) shaped s ≤
    Shape.denote (withExitUB t (fun _ => false)) shaped s) ↔ _
  simp only [denote_noExitUB]
  exact (native_observe_subset_iff M.raw r t).symm

variable {S : RequestSignature Φ} {R T : List Syntax.Ty} {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}

theorem sat_refinement_iff (M : CodedModel.{u,v} Φ A) :
    M.Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) ↔
      ∀ s : M.store,
        Shape.denote (withExitUB raw g.selected) (model M.handler (g.visible.bindings (decodeLeft M.caller))) s ≤
          Shape.denote (withExitUB raw' h.selected) (model M.handler (h.visible.bindings (decodeRight M.caller))) s :=
  sat_le_iff _ _ _

variable [DecidableEq Φ] {callers : CallerEnumeration A} {replies : ReplyEnumeration S}
  {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

theorem accepts_satisfies_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ M : CodedModel.{u,v} Φ A, M.Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) := by
  rw [Table.checkEntries_accepts_iff checked checked']
  exact ⟨fun all M => (sat_refinement_iff M).mpr (all M.store M.caller M.handler),
    fun all σ input handler => (sat_refinement_iff ⟨σ, input, handler⟩).mp (all ⟨σ, input, handler⟩)⟩

theorem cutoff_satisfies_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ (input : Payload A) (handler : Primitives Φ n),
        (CodedModel.mk (Fin n) input handler).Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) := by
  exact (Table.checkEntries_cutoff_iff checked checked').trans
    (forall_congr' fun input => forall_congr' fun handler => (sat_refinement_iff ⟨_, input, handler⟩).symm)

theorem countermodel
    (rejected : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    ∃ (input : Payload A) (handler : Primitives Φ n),
      ¬ (CodedModel.mk (Fin n) input handler).Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) := by
  obtain ⟨input, handler, s, fails⟩ := Table.checkEntries_witness rejected
  exact ⟨input, handler, fun sat => fails ((sat_refinement_iff ⟨_, input, handler⟩).mp sat s)⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution
