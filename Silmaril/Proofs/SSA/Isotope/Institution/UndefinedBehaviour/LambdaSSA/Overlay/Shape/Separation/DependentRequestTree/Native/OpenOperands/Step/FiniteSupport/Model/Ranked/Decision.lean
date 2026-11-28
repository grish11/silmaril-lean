module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Witness
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
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

omit [DecidableEq Φ] in
private theorem entry_bound (ranked : g.entryCheck = true ∨ h.entryCheck = true)
    (input : Payload A) :
    Below g ⟨g.entry, decodeLeft input⟩ (g.rankedCutoff h) ∨
      Below h ⟨h.entry, decodeRight input⟩ (g.rankedCutoff h) := by
  have gl (ok : g.entryCheck = true) : (g.ranks.get g.entry).isSome = true :=
    Rank.ranked_of_checkFrom g.targets ok (by simp)
  have hr (ok : h.entryCheck = true) : (h.ranks.get h.entry).isSome = true :=
    Rank.ranked_of_checkFrom h.targets ok (by simp)
  cases lg : g.ranks.get g.entry with
  | none =>
    cases rh : h.ranks.get h.entry with
    | none =>
      exfalso
      rcases ranked with ok | ok
      · simpa [lg] using gl ok
      · simpa [rh] using hr ok
    | some b => exact Or.inr (by simp [Below, Table.rankedCutoff, lg, rh])
  | some a =>
    cases rh : h.ranks.get h.entry with
    | none => exact Or.inl (by simp [Below, Table.rankedCutoff, lg, rh])
    | some b =>
      by_cases ordered : a ≤ b
      · exact Or.inl (by simp [Below, Table.rankedCutoff, lg, rh, min_eq_left ordered])
      · exact Or.inr (by simp [Below, Table.rankedCutoff, lg, rh, min_eq_right (Nat.le_of_not_ge ordered)])

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

theorem rejects (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (ranked : g.entryCheck = true ∨ h.entryCheck = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected)
        (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false := by
  rw [g.observe_entry raw hg, h.observe_entry raw' hh] at failed
  obtain ⟨other, t, bad⟩ := point_witness g h (decodeLeft input) (decodeRight input) left right
    prim s (g.rankedCutoff h) (entry_bound ranked input) failed
  have admitted : (g.entryCheck || h.entryCheck) = true := Bool.or_eq_true_iff.mpr ranked
  rw [Table.checkRankedEntries?, ite_eq_left admitted]
  apply reject_of_witness hg hh (g.rankedStores h) input other t
  rwa [g.observe_entry raw hg, h.observe_entry raw' hh]

theorem accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (ranked : g.entryCheck = true ∨ h.entryCheck = true) :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  constructor
  · intro checked carrier input prim s
    by_contra failed
    have negative := rejects hg hh ranked callers replies left right input prim s failed
    rw [checked] at negative
    cases negative
  · intro valid
    have all := (Table.finite_model_property (callers := callers) (replies := replies) (left := left)
      (right := right) hg hh).mp valid
    have admitted : (g.entryCheck || h.entryCheck) = true := Bool.or_eq_true_iff.mpr ranked
    rw [Table.checkRankedEntries?, ite_eq_left admitted]
    exact all (g.rankedCutoff h) (g.rankedStores h)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked
