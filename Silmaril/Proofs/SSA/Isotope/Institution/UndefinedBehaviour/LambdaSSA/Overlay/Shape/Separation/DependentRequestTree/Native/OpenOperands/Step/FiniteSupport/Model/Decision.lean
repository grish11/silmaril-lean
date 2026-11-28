module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Classification
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Universe

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open Syntax (Payload StatePrimitives)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v} {n : Nat}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {stores : StateInventory n}

theorem check_true_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true ↔
      g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some .refines := by
  cases result : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores with
  | none => simp [Table.checkEntries?, result]
  | some verdict => cases verdict <;> simp [Table.checkEntries?, EntryVerdict.accepted, result]

theorem check_false_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false ↔
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
        some (.counterexample witness) := by
  cases result : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores with
  | none => simp [Table.checkEntries?, result]
  | some verdict => cases verdict <;> simp [Table.checkEntries?, EntryVerdict.accepted, result]

theorem rejecting_carrier (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    ∃ n, 0 < n ∧ RefutationBound g h (decodeLeft input) (decodeRight input) prim s n ∧
      ∀ stores : StateInventory n,
        g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
        g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false := by
  classical
  have finish (support : RunSupport σ s)
      (bound : RefutationBound g h (decodeLeft input) (decodeRight input) prim s support.values.length)
      (rejects : ∀ stores : StateInventory support.values.length,
        g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
        ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
          some (.counterexample witness)) :
      ∃ n, 0 < n ∧ RefutationBound g h (decodeLeft input) (decodeRight input) prim s n ∧
        ∀ stores : StateInventory n,
          g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
          g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false := by
    exact ⟨_, List.length_pos_of_mem support.initial_mem, bound, fun stores =>
      ⟨(rejects stores).1, check_false_iff.mpr (rejects stores).2⟩⟩
  rcases finite_or_infinite g (decodeLeft input) prim ⟨g.entry, decodeLeft input⟩ s with ⟨qs₀, t₀, finite₀⟩ | infinite₀
  · rcases finite_or_infinite h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ s with ⟨qs₁, t₁, finite₁⟩ | infinite₁
    · have compressed := Table.compress_finite_refutation hg hh finite₀ finite₁ failed callers replies left right
      exact finish (RunSupport.ofRows s (qs₀ ++ qs₁)) (.finite finite₀ finite₁ compressed.1) compressed.2.2.2.2
    · have compressed := Table.compress_mixed_refutation hg hh (.inr ⟨finite₀, infinite₁⟩)
        failed callers replies left right
      exact finish (RunSupport.ofRows s qs₀) (.infiniteRight finite₀ infinite₁ compressed.1) compressed.2.2.2.2
  · rcases finite_or_infinite h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ s with ⟨qs₁, t₁, finite₁⟩ | infinite₁
    · have compressed := Table.compress_mixed_refutation hg hh (.inl ⟨infinite₀, finite₁⟩)
        failed callers replies left right
      exact finish (RunSupport.ofRows s qs₁) (.infiniteLeft infinite₀ finite₁ compressed.1) compressed.2.2.2.2
    · exact False.elim (failed (Table.both_infinite_observations hg hh infinite₀ infinite₁).le)

theorem finite_refutation_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    (∃ (n : Nat) (stores : StateInventory n),
      g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false) ↔
    ∃ (σ : Type v) (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ),
      ¬ Shape.denote (withExitUB raw g.selected)
          (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
        Shape.denote (withExitUB raw' h.selected)
          (Syntax.model prim (h.bindings (decodeRight input))) s := by
  constructor
  · rintro ⟨n, stores, rejected⟩
    obtain ⟨w, found⟩ := check_false_iff.mp rejected
    have refutes := (Table.compareEntries_counterexample found).2.2
    exact ⟨ULift.{v} (Fin n), w.input, liftPrimitives w.interpreter, ULift.up w.initial,
      fun le => refutes ((ulift_order_iff hg hh (decodeLeft w.input) (decodeRight w.input) w.interpreter w.initial).mp le)⟩
  · rintro ⟨σ, input, prim, s, failed⟩
    obtain ⟨n, _, _, rejects⟩ := rejecting_carrier hg hh callers replies left right input prim s failed
    let stores : StateInventory n := ⟨List.finRange n, List.mem_finRange⟩
    exact ⟨n, stores, (rejects stores).2⟩

theorem all_accepts_iff :
    (∀ (n : Nat) (stores : StateInventory n),
      g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true) ↔
      g.checkNative raw = true ∧ h.checkNative raw' = true ∧
        g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  constructor
  · intro every
    have supported := Table.compareEntries_accepts_iff.mp (check_true_iff.mp (every 0 ⟨[], fun s => Fin.elim0 s⟩))
    refine ⟨supported.1, supported.2.1, ?_⟩
    intro σ input prim s
    by_contra failed
    obtain ⟨n, _, _, rejects⟩ := rejecting_carrier supported.1 supported.2.1 callers replies left right input prim s failed
    let stores : StateInventory n := ⟨List.finRange n, List.mem_finRange⟩
    have no := (rejects stores).2
    rw [every n stores] at no
    cases no
  · rintro ⟨hg, hh, valid⟩ n stores
    apply check_true_iff.mpr
    refine Table.compareEntries_accepts_iff.mpr ⟨hg, hh, fun input prim s => ?_⟩
    exact (ulift_order_iff hg hh (decodeLeft input) (decodeRight input) prim s).mp
      (valid (ULift.{v} (Fin n)) input (liftPrimitives prim) (ULift.up s))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model
