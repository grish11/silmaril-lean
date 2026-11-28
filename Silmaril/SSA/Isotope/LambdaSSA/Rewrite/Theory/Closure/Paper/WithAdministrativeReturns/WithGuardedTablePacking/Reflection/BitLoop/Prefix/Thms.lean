module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Prefix.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Prefix

/-! # The request-prefix model separates requesting from silent divergence

The model is an instance of the class quantified by `Valid`. Its parts:

- Category and iterator: the Kleisli category of the ordered-trace monad
  with its least-fixed-point iterator, as in the four-reply model.
- Pure transport: pure uniformity of that Kleisli structure.
- Tensor: the shared-tensor equation holds by reflexivity.
- Primitive: `prefixRequest`. Its pure-primitive condition is vacuous.
- Coherence: `prefixCoherent`.

Complete returns of one-request programs are those of the four-reply
model. A pending request is one more observation, and it distinguishes
the two nonreturning loops of `trace_test_not_reflecting`.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace request)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns
  (TableReadback.PureIsoIteration)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged Finite)
open CategoryTheory
open scoped MonoidalCategory

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

/-! ## The model interface -/

/-- Pure transport: feedback is conjugated by every invertible pure state map. -/
theorem trace_pureIsoIteration : TableReadback.PureIsoIteration J :=
  fun p f g square => ElgotFreydCategory.pure_uniformity J f g p.hom square

/-- The value tensor is shared with the computation category on the nose. -/
theorem trace_sharedTensor : ∀ X Y : Type, ∃ h : (J).obj X ⊗ (J).obj Y = (J).obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso («J» := J) X Y = eqToIso h :=
  fun _ _ => ⟨rfl, rfl⟩

noncomputable local instance : InstructionModel J M signature.Instr := instructions prefixModel
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

/-- Two typed regions with different arrows in this model are not valid. -/
theorem not_valid_of_prefix {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {r s : Region signature.Instr}
    (hr : HasType Γ r L) (hs : HasType Γ s L) (ne : denoteRegion J M hr ≠ denoteRegion J M hs) :
    ¬ Valid hr hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.not_valid_of_ne hr hs ne

/-- A pending request is the request's outcomes and one tagged observation
with an empty log. -/
theorem prefixRequest_outcomes (label : Bool) (q : value Bit) :
    (prefixRequest label q).outcomes = (request label q).outcomes ∪ {(Except.error label, 1)} :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.prefixRequest_outcomes label q

/-- Iteration: the literal loop is the monad's iterator on the step. -/
theorem prefixObservations_eq (p : Program) (g : Bool) :
    prefixObservations p g =
      (Silmaril.Elgot.iter (m := Trace) (prefixStep p) (Sum.inl (bit g))).outcomes :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.prefixObservations_eq p g

/-- That iterator is the least fixed point of one unfolding, in the
inclusion order on observations. -/
theorem prefix_iter_lfp (p : Program) :
    (fun s => (Silmaril.Elgot.iter (m := Trace) (prefixStep p) s).outcomes) =
      (Finite.unfoldLoop (Silmaril.Elgot.ExceptT.body (prefixStep p))).lfp :=
  Tagged.iter_eq_lfp (prefixStep p)

/-! ## One-request programs -/

/-- The step sends its request on the state and routes the reply. -/
theorem prefix_oneAsk_step (label repeatLeft repeatRight : Bool) (x : value Bit) :
    prefixStep (oneAsk label repeatLeft repeatRight) (Sum.inl x) =
      (prefixRequest label x >>= fun ans => pure (route repeatLeft repeatRight ans)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.prefix_oneAsk_step label repeatLeft repeatRight x

theorem Poll.program_eq (a : Poll) : a.program = oneAsk a.label a.returnRight (!a.returnRight) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.poll_oneAsk a

theorem askSpin_eq (label : Bool) : askSpin label = oneAsk label true true := rfl

/-- Complete returns of a one-request loop are those of the four-reply model. -/
theorem complete_iff (label repeatLeft repeatRight g : Bool) (b : value Bit) (w : Word) :
    (Except.ok b, w) ∈ prefixObservations (oneAsk label repeatLeft repeatRight) g ↔
      (Except.ok b, w) ∈ loopObservations (oneAsk label repeatLeft repeatRight) g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.prefix_complete_iff label repeatLeft repeatRight g b w

theorem Poll.complete_iff (a : Poll) (g : Bool) (b : value Bit) (w : Word) :
    (Except.ok b, w) ∈ prefixObservations a.program g ↔ (Except.ok b, w) ∈ loopObservations a.program g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.prefix_poll_complete a g b w

/-- The one-round return of a poll is unchanged. -/
theorem Poll.oneRound (a : Poll) (g b : Bool) :
    (Except.ok (bit b), FreeMonoid.of (event a.label g (a.returnRight, b))) ∈
      prefixObservations a.program g :=
  (Poll.complete_iff a g _ _).2 (BitLoop.Poll.oneRound a g b)

/-- The return through the backedge is unchanged. -/
theorem Poll.twoRounds (a : Poll) (g s b : Bool) :
    (Except.ok (bit b), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event a.label s (a.returnRight, b))) ∈ prefixObservations a.program g :=
  (Poll.complete_iff a g _ _).2 (BitLoop.Poll.twoRounds a g s b)

/-! ## Requesting and silent divergence -/

/-- The first request of the always-requesting loop is observed pending. -/
theorem askSpin_pending (label g : Bool) :
    (Except.error label, (1 : Word)) ∈ prefixObservations (askSpin label) g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.askSpin_pending label g

/-- After one completed exchange its event is in the log, and the next
request is pending. -/
theorem askSpin_pending_after (label g tag payload : Bool) :
    (Except.error label, FreeMonoid.of (event label g (tag, payload)) * 1) ∈
      prefixObservations (askSpin label) g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.askSpin_pending_after label g tag payload

/-- The silent loop has no observation in this model either. -/
theorem spin_observations (g : Bool) : prefixObservations spin g = ∅ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.spin_prefix_empty g

/-- The literal always-requesting loop and the literal silent loop are
not valid: this model gives them different arrows. -/
theorem askSpin_not_valid (label : Bool) :
    ¬ Valid (loop_typed (askSpin label)).hasType (loop_typed spin).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.askSpin_not_valid label

/-- Hence the table-packing quotient does not equate them. -/
theorem askSpin_not_eqv (label : Bool) :
    ¬ Eqv false [State] (loopRegion (askSpin label)) (loopRegion spin) [Bit] :=
  fun e => askSpin_not_valid label (valid_of_eqv false e _ _)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix
