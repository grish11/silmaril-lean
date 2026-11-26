module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.State.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry.State

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {n m : Nat}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry)}
  {decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry)}
  {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {stores : StateInventory n} {w : EntryCounterexample Φ A n}

theorem mapState_refutes (e : Fin n ↪ Fin m) (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory n)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
          (Syntax.model w.interpreter (g.bindings (decodeLeft w.input))) w.initial ≤
        Shape.denote (withExitUB raw' h.selected)
          (Syntax.model w.interpreter (h.bindings (decodeRight w.input))) w.initial) :
    ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model (w.mapState e).interpreter (g.bindings (decodeLeft w.input))) (e w.initial) ≤
      Shape.denote (withExitUB raw' h.selected)
        (Syntax.model (w.mapState e).interpreter (h.bindings (decodeRight w.input))) (e w.initial) := by
  have agree (f : Φ) (a : Syntax.Payload (instrSrc f)) (s : Fin n) :
      (w.mapState e).interpreter f a (e s) = (w.interpreter f a s).mapState e :=
    InterpreterScript.interpret_mapState e w.script f a s
  have lower := g.observe_entry_mapState e raw hg (decodeLeft w.input) w.interpreter (w.mapState e).interpreter
    agree left stores w.initial
  have upper := h.observe_entry_mapState e raw' hh (decodeRight w.input) w.interpreter (w.mapState e).interpreter
    agree right stores w.initial
  rwa [lower, upper, Behaviour.mapState_le_iff]

variable {callers : CallerEnumeration A} {replies : ReplyEnumeration S}

theorem rejection_mono (e : Fin n ↪ Fin m)
    (largerLeft : ConfigurationEnumeration R) (largerRight : ConfigurationEnumeration T) (larger : StateInventory m)
    (found : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
      some (.counterexample w)) :
    (¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model (w.mapState e).interpreter (g.bindings (decodeLeft w.input))) (e w.initial) ≤
      Shape.denote (withExitUB raw' h.selected)
        (Syntax.model (w.mapState e).interpreter (h.bindings (decodeRight w.input))) (e w.initial)) ∧
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies largerLeft largerRight larger =
        some (.counterexample witness) := by
  have supported : g.checkNative raw = true ∧ h.checkNative raw' = true := by
    cases hg : g.checkNative raw <;> cases hh : h.checkNative raw' <;> simp [Table.compareEntries?, hg, hh] at found ⊢
  have transported := mapState_refutes e supported.1 supported.2 left right stores
    (Table.compareEntries_counterexample found).2.2
  refine ⟨transported, ?_⟩
  cases verdict : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies largerLeft largerRight larger with
  | none =>
    have unsupported := Table.compareEntries_none_iff.mp verdict
    simp [supported.1, supported.2] at unsupported
  | some outcome =>
    cases outcome with
    | refines =>
      have ordered := (Table.compareEntries_accepts_iff.mp verdict).2.2
      exact False.elim (transported (ordered _ _ _))
    | counterexample witness => exact ⟨witness, rfl⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.Entry.State
