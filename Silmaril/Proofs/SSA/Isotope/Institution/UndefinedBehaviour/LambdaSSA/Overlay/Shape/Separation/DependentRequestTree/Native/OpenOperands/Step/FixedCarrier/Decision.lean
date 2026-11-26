module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Mathlib.Data.List.Dedup
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Classification
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Restrictions

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open CFG.Dependent.Native (withExitUB)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits result_order)
open ScheduleSearch (StateInventory)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {states : Nat}

theorem check_results (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) :
    g.checkAllInterpreters h caller caller' replies left right stores = true ↔
      ∀ (prim : Syntax.Primitives Φ states) (s : Fin states),
        (g.runFinite caller prim left stores ⟨g.entry, caller⟩ s).refines
          (h.runFinite caller' prim right stores ⟨h.entry, caller'⟩ s) := by
  let keys := (g.queries caller left stores ++ h.queries caller' right stores).dedup
  simp only [Table.checkAllInterpreters, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro checked prim s
    obtain ⟨script, listed, agrees⟩ := restricted replies stores keys prim
    have lower := runFinite_congr g caller left stores
      (fun q mem => agrees q (List.mem_dedup.mpr (List.mem_append_left _ mem))) ⟨g.entry, caller⟩ s
    have upper := runFinite_congr h caller' right stores
      (fun q mem => agrees q (List.mem_dedup.mpr (List.mem_append_right _ mem))) ⟨h.entry, caller'⟩ s
    rw [← lower, ← upper]
    exact checked script listed s (stores.complete s)
  · intro checked script _ s _
    exact checked (InterpreterScript.interpret script) s

theorem checkAllInterpreters_iff (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) :
    g.checkAllInterpreters h caller caller' replies left right stores = true ↔
      ∀ (prim : Syntax.Primitives Φ states) (s : Fin states),
        Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings caller')) s := by
  rw [check_results]
  refine forall_congr' fun prim => forall_congr' fun s => ?_
  rw [g.observe_entry raw hg, h.observe_entry raw' hh, classify g caller prim left stores,
    classify h caller' prim right stores, result_order]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier
