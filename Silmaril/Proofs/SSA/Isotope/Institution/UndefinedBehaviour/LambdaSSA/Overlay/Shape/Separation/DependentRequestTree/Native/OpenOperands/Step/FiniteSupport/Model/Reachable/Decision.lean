module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Separation
import Mathlib.Data.Fin.Embedding

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open Syntax (Payload Primitives StatePrimitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

private theorem count_le (input : Payload A) :
    (g.productVisits h (decodeLeft input) (decodeRight input) replies left right).length ≤
      g.reachableCutoff h callers decodeLeft decodeRight replies left right := by
  have mem := List.mem_map_of_mem (f := fun a =>
    (g.productVisits h (decodeLeft a) (decodeRight a) replies left right).length) (callers.complete input)
  rw [Table.reachableCutoff, List.max?_eq_some_max (List.ne_nil_of_mem mem)]
  exact List.le_max_of_mem mem

private theorem finite_rejects (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {n : Nat} (stores : StateInventory n) (input : Payload A) (prim : Primitives Φ n) (s : Fin n)
    (failed : ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false := by
  cases check : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores with
  | none => simpa [hg, hh] using Table.checkEntries_none_iff.mp check
  | some b =>
    cases b with
    | false => rfl
    | true => exact (failed ((Table.checkEntries_accepts_iff.mp check).2.2 input prim s)).elim

theorem rejects {σ : Type v} (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkReachableEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false := by
  obtain ⟨point, trail, found⟩ := refutation_has_mismatch (left := left) (right := right) (replies := replies)
    hg hh prim s failed
  have foundValid := g.searchProduct_correct h (decodeLeft input) (decodeRight input) replies left right
  rw [found] at foundValid
  obtain ⟨shortest, path, distinct, _⟩ := foundValid.1.shortest
  have bound := (simple_length (left := left) (right := right) path distinct).trans (count_le (callers := callers) input)
  obtain ⟨test, separates⟩ := native_path_refutes (left := left) (right := right) hg hh path foundValid.2
  let small : StateInventory (shortest.length + 1) := ⟨List.finRange _, List.mem_finRange⟩
  have rejected := finite_rejects (callers := callers) (replies := replies) (left := left) (right := right)
    hg hh small input test 0 separates
  obtain ⟨w, found⟩ := Table.checkEntries_rejects_iff.mp rejected
  apply Table.checkEntries_rejects_iff.mpr
  exact (Table.compareEntries_rejection_mono (Fin.castLEEmb bound) left right
    ⟨List.finRange _, List.mem_finRange⟩ found).2

theorem accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkReachableEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  constructor
  · intro verdict σ input prim s
    by_contra failed
    have rejected := rejects hg hh callers replies left right input prim s failed
    rw [verdict] at rejected
    cases rejected
  · intro valid
    exact (Table.finite_model_property (callers := callers) (replies := replies) (left := left)
      (right := right) hg hh).mp valid _ _

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable
