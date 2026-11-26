module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Bound
import Mathlib.Data.Fin.Embedding

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits result_order)
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open Syntax (Payload StatePrimitives)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

private theorem native_check {K : List Syntax.Ty} {f : Table S K}
    {r : CFG.Dependent.Native.Typed Φ [K.get f.entry] Exits} (checked : f.check r = true) :
    f.checkNative r = true :=
  (Bool.and_eq_true_iff.mp checked).1

private theorem reject_of_witness (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {n : Nat} (stores : StateInventory n) (input : Payload A)
    (prim : Syntax.Primitives Φ n) (s : Fin n)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false := by
  cases verdict : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores with
  | none =>
    have unsupported := Table.checkEntries_none_iff.mp verdict
    simp [hg, hh] at unsupported
  | some b =>
    cases b with
    | false => rfl
    | true => exact False.elim (failed ((Table.checkEntries_accepts_iff.mp verdict).2.2 input prim s))

theorem rejects (hg : g.check raw = true) (hh : h.check raw' = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false := by
  have hgr := Table.checked_rank hg
  have hhr := Table.checked_rank hh
  let p := g.extract hgr (decodeLeft input)
  let q := h.extract hhr (decodeRight input)
  obtain ⟨m, _, _, refuted⟩ := Table.rejecting_carrier (native_check hg) (native_check hh)
    callers replies left right input prim s failed
  let stores : StateInventory m := ⟨List.finRange m, List.mem_finRange⟩
  have bad := (refuted stores).1
  have unrelated : ¬ p.Refines q := by
    intro related
    have good := (g.checkAllInterpreters?_accepts_iff h raw raw' (decodeLeft input) (decodeRight input)
      replies left right stores).mpr ⟨native_check hg, native_check hh, fun interp t => by
        rw [← g.observe hg, ← h.observe hh, result_order]
        exact Tree.refines_execute related interp t⟩
    rw [good] at bad
    cases bad
  obtain ⟨steps, probe, lp, rp, distinguishes⟩ := Tree.exists_prefix_countermodel unrelated
  have length := Nat.le_min.mpr ⟨extract_follows_rank g hgr (decodeLeft input) lp,
    extract_follows_rank h hhr (decodeRight input) rp⟩
  let probeStores : StateInventory (steps + 1) := ⟨List.finRange _, List.mem_finRange⟩
  have failsNative : ¬ Shape.denote (withExitUB raw g.selected)
      (Syntax.model (S.primitives probe.handler) (g.bindings (decodeLeft input))) 0 ≤
    Shape.denote (withExitUB raw' h.selected)
      (Syntax.model (S.primitives probe.handler) (h.bindings (decodeRight input))) 0 := by
    rw [← g.observe hg, ← h.observe hh]
    exact distinguishes
  have probeBad := reject_of_witness (callers := callers) (replies := replies) (left := left) (right := right)
    (native_check hg) (native_check hh) probeStores input (S.primitives probe.handler) 0 failsNative
  obtain ⟨witness, found⟩ := Table.checkEntries_rejects_iff.mp probeBad
  have larger := (Table.compareEntries_rejection_mono (Fin.castLEEmb (Nat.succ_le_succ length))
    left right (g.rankedStores h) found).2
  simp only [Table.checkRankedEntries?, hgr, hhr, Bool.and_self, ite_true]
  exact Table.checkEntries_rejects_iff.mpr larger

theorem accepts_iff (hg : g.check raw = true) (hh : h.check raw' = true) :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  constructor
  · intro checked carrier input prim s
    by_contra failed
    have negative := rejects hg hh callers replies left right input prim s failed
    rw [checked] at negative
    cases negative
  · intro valid
    have all := (Table.finite_model_property (callers := callers) (replies := replies) (left := left)
      (right := right) (native_check hg) (native_check hh)).mp valid
    simpa only [Table.checkRankedEntries?, Table.checked_rank hg, Table.checked_rank hh, Bool.and_self, ite_true]
      using all (g.rankedCutoff h) (g.rankedStores h)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked
