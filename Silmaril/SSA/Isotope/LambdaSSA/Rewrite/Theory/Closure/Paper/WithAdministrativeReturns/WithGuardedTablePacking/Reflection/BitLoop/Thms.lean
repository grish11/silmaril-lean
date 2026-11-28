module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Reflection

/-! # Reflection for live polling loops, and what the trace test misses

Three statements are kept apart. `Eqv` is the contextual equation of the
table-packing quotient. `Valid` is equality in every supported model.
`loopObservations` is one fixed interpreter: complete finite runs under
the four-reply policy. On spellings of polls the three agree with equality
of reflected tree keys. On the whole fragment only the implications
`key → Eqv → Valid → observations` are proved. Equal observations do not
give equal keys there, and by `Prefix.askSpin_not_valid` they do not give
`Valid` either.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (event)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)

/-! ## Every program of the fragment -/

/-- The literal loop is a one-row guarded table. In this quotient it equals
its packed single-feedback dispatcher. -/
theorem loop_packed (p : Program) :
    ∃ (R : Fin 1 → Ty Empty) (e : Region signature.Instr) (blocks : Fin 1 → Region signature.Instr)
      (he : ValueBranches [State] e (List.ofFn R ++ [Bit]))
      (hb : ∀ i, ValueBranches [R i, State] (blocks i) (List.ofFn R ++ [Bit])),
      loopRegion p = .cfg e 1 blocks ∧
        Eqv false [State] (loopRegion p) (packedReadbackRep R he hb).val [Bit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.loop_packed p

/-- Dispatcher steps are reflected in the table-packing quotient: two step
arrows are equal exactly when the reflected request trees have one key. -/
theorem stepArrow_eq_iff_key (p q : Program) : stepArrow p = stepArrow q ↔ p.tree.key = q.tree.key :=
  ⟨Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.key_of_step, Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.step_of_key⟩

/-- Equal step keys give equal loops. The steps are normalized under the
feedback label. -/
theorem loop_eqv_of_key {p q : Program} (h : p.tree.key = q.tree.key) :
    Eqv false [State] (loopRegion p) (loopRegion q) [Bit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.loop_of_key h

/-- In the fixed interpreter, the step on a Bit state has exactly the
outcomes of the reflected request tree. -/
theorem stepModel_outcomes (p : Program) (g : Bool) :
    (stepModel p (Sum.inl (bit g))).outcomes = p.tree.outcomes (fun _ => g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.stepModel_outcomes p g

/-- The literal loop has the complete runs of the interpreter's iterator
on that step. -/
theorem loopObservations_eq (p : Program) (g : Bool) :
    loopObservations p g =
      (Silmaril.Elgot.iter (m := Trace) (stepModel p) (Sum.inl (bit g))).outcomes :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.loopObservations_eq p g

/-- Validity in every model implies the fixed interpreter's test. -/
theorem observations_of_valid {p q : Program}
    (h : Valid (loop_typed p).hasType (loop_typed q).hasType) (g : Bool) :
    loopObservations p g = loopObservations q g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.observations_of_valid h g

theorem observations_of_eqv {p q : Program}
    (h : Eqv false [State] (loopRegion p) (loopRegion q) [Bit]) (g : Bool) :
    loopObservations p g = loopObservations q g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.observations_of_eqv h g

/-! ## Polls -/

/-- A reply on the returning side ends the loop with its payload. -/
theorem Poll.oneRound (a : Poll) (g b : Bool) :
    (Except.ok (bit b), FreeMonoid.of (event a.label g (a.returnRight, b))) ∈
      loopObservations a.program g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.oneRound a g b

/-- A reply on the other side takes the backedge. The second request is
sent with the first reply's payload. -/
theorem Poll.twoRounds (a : Poll) (g s b : Bool) :
    (Except.ok (bit b), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event a.label s (a.returnRight, b))) ∈ loopObservations a.program g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.twoRounds a g s b

variable {p q : Program} {a b : Poll}

/-- On spellings of polls, the contextual equation of the two literal
loops is equality of step keys. -/
theorem eqv_iff_key (hp : Spells p a) (hq : Spells q b) :
    Eqv false [State] (loopRegion p) (loopRegion q) [Bit] ↔ p.tree.key = q.tree.key :=
  ⟨fun h => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.key_of_observations hp hq (observations_of_eqv h), loop_eqv_of_key⟩

/-- On spellings of polls, validity in every model is equality of step keys. -/
theorem valid_iff_key (hp : Spells p a) (hq : Spells q b) :
    Valid (loop_typed p).hasType (loop_typed q).hasType ↔ p.tree.key = q.tree.key :=
  ⟨fun h => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.key_of_observations hp hq (observations_of_valid h),
    fun h => valid_of_eqv false (loop_eqv_of_key h) _ _⟩

/-- On spellings of polls, the fixed interpreter's test is also equality
of step keys. -/
theorem observations_iff_key (hp : Spells p a) (hq : Spells q b) :
    (∀ g, loopObservations p g = loopObservations q g) ↔ p.tree.key = q.tree.key :=
  ⟨Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.key_of_observations hp hq, fun h => observations_of_eqv (loop_eqv_of_key h)⟩

/-- Reflection holds at the literal loops of any two spellings of polls. -/
theorem reflects (hp : Spells p a) (hq : Spells q b) : Reflects false (loop_typed p) (loop_typed q) :=
  fun h => (eqv_iff_key hp hq).2 ((valid_iff_key hp hq).1 h)

/-- Two polls have equal loops only when they are the same poll. -/
theorem Poll.eqv_iff (a b : Poll) :
    Eqv false [State] (loopRegion a.program) (loopRegion b.program) [Bit] ↔ a = b :=
  ⟨fun h => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.poll_eq_of_observations (observations_of_eqv h false),
    fun h => h ▸ Paper.Extension.Eqv.refl (loop_typed a.program).hasType⟩

theorem aliased_spells (label : Bool) : Spells (aliased label) ⟨label, false⟩ := rfl

/-- The aliased spelling is a different written program with an equal loop. -/
theorem aliased_eqv (label : Bool) :
    (aliased label).written ≠ (Poll.program ⟨label, false⟩).written ∧
      Eqv false [State] (loopRegion (aliased label)) (loopRegion (Poll.program ⟨label, false⟩)) [Bit] :=
  ⟨fun h => (by cases h), loop_eqv_of_key (aliased_spells label)⟩

/-! ## The fixed interpreter does not reflect on the whole fragment -/

theorem spin_observations (g : Bool) : loopObservations spin g = ∅ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.spin_observations g

theorem askSpin_observations (label g : Bool) : loopObservations (askSpin label) g = ∅ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.askSpin_observations label g

/-- A loop that sends a request on every round and a loop that sends none
have the same complete runs, namely none. Their steps differ in this
quotient. `Prefix.askSpin_not_valid` shows that the two loops are not
valid, in a model that also observes pending requests. -/
theorem trace_test_not_reflecting (label : Bool) :
    (∀ g, loopObservations (askSpin label) g = loopObservations spin g) ∧
      stepArrow (askSpin label) ≠ stepArrow spin :=
  ⟨fun g => (askSpin_observations label g).trans (spin_observations g).symm,
    fun h => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.askSpin_key_ne label ((stepArrow_eq_iff_key _ _).1 h)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
