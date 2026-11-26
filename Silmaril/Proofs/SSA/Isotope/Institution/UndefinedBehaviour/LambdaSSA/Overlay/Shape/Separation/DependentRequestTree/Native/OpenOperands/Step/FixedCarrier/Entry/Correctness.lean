module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Mathlib.Data.List.Dedup
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits result_order)
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {states : Nat}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry)}
  {decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {stores : StateInventory states}

private theorem result_refines_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (a : Syntax.Payload (R.get g.entry)) (b : Syntax.Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) (prim : Syntax.Primitives Φ states) (s : Fin states) :
    (g.runFinite a prim left stores ⟨g.entry, a⟩ s).refines
        (h.runFinite b prim right stores ⟨h.entry, b⟩ s) ↔
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
        Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s := by
  rw [g.observe_entry raw hg, h.observe_entry raw' hh, g.observe_runFinite a prim left stores,
    h.observe_runFinite b prim right stores, result_order]

private theorem tested_iff :
    g.findEntryFailure h callers decodeLeft decodeRight replies left right stores = none ↔
      ∀ input ∈ callers.packets, ∀ script ∈ InterpreterScript.assignments replies stores
          (g.entryQueries h callers decodeLeft decodeRight left right stores), ∀ s ∈ stores.values,
        let prim := InterpreterScript.interpret script
        (g.runFinite (decodeLeft input) prim left stores ⟨g.entry, decodeLeft input⟩ s).refines
          (h.runFinite (decodeRight input) prim right stores ⟨h.entry, decodeRight input⟩ s) := by
  simp [Table.findEntryFailure]

private theorem no_failure_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.findEntryFailure h callers decodeLeft decodeRight replies left right stores = none ↔
      ∀ (input : Syntax.Payload A) (prim : Syntax.Primitives Φ states) (s : Fin states),
        Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s := by
  rw [tested_iff]
  constructor
  · intro tested input prim s
    have listed := callers.complete input
    obtain ⟨script, mem, agree⟩ := InterpreterScript.restricted replies stores
      (g.entryQueries h callers decodeLeft decodeRight left right stores) prim
    have ordered := (result_refines_iff hg hh (decodeLeft input) (decodeRight input) left right stores _ s).mp
      (tested input listed script mem s (stores.complete s))
    have lower := g.observeAt_congr (decodeLeft input) left stores (fun q found =>
      agree q (List.mem_dedup.mpr (List.mem_flatMap.mpr
        ⟨input, listed, List.mem_append_left _ found⟩))) ⟨g.entry, decodeLeft input⟩ s
    have upper := h.observeAt_congr (decodeRight input) right stores (fun q found =>
      agree q (List.mem_dedup.mpr (List.mem_flatMap.mpr
        ⟨input, listed, List.mem_append_right _ found⟩))) ⟨h.entry, decodeRight input⟩ s
    rw [g.observe_entry raw hg, h.observe_entry raw' hh, lower, upper] at ordered
    rw [g.observe_entry raw hg, h.observe_entry raw' hh]
    exact ordered
  · intro ordered input _ script _ s _
    exact (result_refines_iff hg hh (decodeLeft input) (decodeRight input) left right stores _ s).mpr
      (ordered input (InterpreterScript.interpret script) s)

theorem accepts_iff :
    g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some .refines ↔
      g.checkNative raw = true ∧ h.checkNative raw' = true ∧
        ∀ (input : Syntax.Payload A) (prim : Syntax.Primitives Φ states) (s : Fin states),
          Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
            Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s := by
  cases hg : g.checkNative raw <;> cases hh : h.checkNative raw' <;> simp [Table.compareEntries?, hg, hh]
  have correct := no_failure_iff (callers := callers) (decodeLeft := decodeLeft) (decodeRight := decodeRight)
    (replies := replies) (left := left) (right := right) (stores := stores) hg hh
  cases failure : g.findEntryFailure h callers decodeLeft decodeRight replies left right stores <;>
    simpa [failure] using correct

theorem counterexample {w : EntryCounterexample Φ A states}
    (found : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
      some (.counterexample w)) :
    w.input ∈ callers.packets ∧ w.initial ∈ stores.values ∧
      ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model w.interpreter (g.bindings (decodeLeft w.input))) w.initial ≤
        Shape.denote (withExitUB raw' h.selected)
          (Syntax.model w.interpreter (h.bindings (decodeRight w.input))) w.initial := by
  unfold Table.compareEntries? at found
  split at found
  · rename_i gate
    obtain ⟨hg, hh⟩ := Bool.and_eq_true_iff.mp gate
    cases result : g.findEntryFailure h callers decodeLeft decodeRight replies left right stores with
    | none => simp [result] at found
    | some w' =>
      obtain rfl := EntryVerdict.counterexample.inj (Option.some.inj (by simpa [result] using found))
      unfold Table.findEntryFailure at result
      obtain ⟨input, listed, hit⟩ := List.exists_of_findSome?_eq_some result
      obtain ⟨script, _, hit⟩ := List.exists_of_findSome?_eq_some hit
      dsimp only at hit
      cases test : stores.values.find? (fun s =>
          !decide ((g.runFinite (decodeLeft input) (InterpreterScript.interpret script)
            left stores ⟨g.entry, decodeLeft input⟩ s).refines
          (h.runFinite (decodeRight input) (InterpreterScript.interpret script)
            right stores ⟨h.entry, decodeRight input⟩ s))) with
      | none => simp [test] at hit
      | some s =>
        obtain rfl := Option.some.inj (by simpa [test] using hit)
        refine ⟨listed, List.mem_of_find?_eq_some test, ?_⟩
        have failed := List.find?_some test
        exact fun ordered => by
          have success := (result_refines_iff hg hh (decodeLeft input) (decodeRight input) left right stores
            (InterpreterScript.interpret script) s).mpr ordered
          simp [success] at failed
  · cases found

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry
