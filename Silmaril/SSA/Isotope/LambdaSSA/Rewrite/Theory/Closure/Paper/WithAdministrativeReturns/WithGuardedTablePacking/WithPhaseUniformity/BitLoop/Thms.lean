module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Unrolled.Valid.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Prefix.Thms

/-! # Five-round replay and reflection with phase uniformity

In `WithPhaseUniformity` the written request loops of the Bit slice unroll
at every round count. On spellings of polls the quotient equation, validity
in every supported model and equality of one-round keys coincide at any
two round counts. The quotient still separates distinct polls and the
requesting loop from the silent one.

These are statements about `WithPhaseUniformity.Eqv`. The corresponding
equations of `WithGuardedTablePacking` at five rounds stay open.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

variable {p q : Program} {a b : Poll}

/-- Every unrolled loop of the fragment equals the one-round loop. -/
theorem unrolled_eqv (p : Program) (n : Nat) :
    Eqv false [State] (unrolled p n) (loopRegion p) [Bit] :=
  WithPhaseUniformity.unrolled_eqv false n (step_typed p)

/-- The literal five-round polling pair. -/
theorem Poll.fiveRounds_eqv (a : Poll) :
    Eqv false [State] (unrolled a.program 4) (loopRegion a.program) [Bit] :=
  unrolled_eqv a.program 4

/-- Whole-loop replay at any two round counts: two unrolled spellings of
polls are equal exactly when the one-round keys agree. -/
theorem replay (hp : Spells p a) (hq : Spells q b) (m n : Nat) :
    Eqv false [State] (unrolled p m) (unrolled q n) [Bit] ↔ p.tree.key = q.tree.key :=
  ⟨fun h => (unrolled_valid_iff_key hp hq m n).1 (valid_of_eqv false h _ _),
    fun h => (unrolled_eqv p m).trans
      ((ofTablePacking false (loop_eqv_of_key h)).trans (unrolled_eqv q n).symm)⟩

/-- On that slice the quotient equation is validity in every supported model. -/
theorem eqv_iff_valid (hp : Spells p a) (hq : Spells q b) (m n : Nat) :
    Eqv false [State] (unrolled p m) (unrolled q n) [Bit] ↔
      Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType :=
  (replay hp hq m n).trans (unrolled_valid_iff_key hp hq m n).symm

/-- Reflection: validity in every supported model gives the quotient equation. -/
theorem reflects (hp : Spells p a) (hq : Spells q b) (m n : Nat)
    (valid : Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType) :
    Eqv false [State] (unrolled p m) (unrolled q n) [Bit] :=
  (eqv_iff_valid hp hq m n).2 valid

/-- The five-round loop of one spelling against the one-round loop of another. -/
theorem fiveRounds_replay (hp : Spells p a) (hq : Spells q b) :
    Eqv false [State] (unrolled p 4) (loopRegion q) [Bit] ↔ p.tree.key = q.tree.key :=
  replay hp hq 4 0

/-- Unrolled polls are equal only when they unroll the same poll. -/
theorem Poll.unrolled_eqv_iff (a b : Poll) (m n : Nat) :
    Eqv false [State] (unrolled a.program m) (unrolled b.program n) [Bit] ↔ a = b :=
  (replay (p := a.program) (q := b.program) rfl rfl m n).trans
    ((eqv_iff_key (p := a.program) (q := b.program) rfl rfl).symm.trans
      (WithGuardedTablePacking.BitLoop.Poll.eqv_iff a b))

/-- A five-round loop on one label is not the one-round loop on the other. -/
theorem Poll.fiveRounds_ne (side : Bool) :
    ¬ Eqv false [State] (unrolled (Poll.program ⟨false, side⟩) 4)
      (loopRegion (Poll.program ⟨true, side⟩)) [Bit] :=
  fun h => by cases (Poll.unrolled_eqv_iff ⟨false, side⟩ ⟨true, side⟩ 4 0).1 h

/-- Nor is it the one-round loop that returns on the other reply side. -/
theorem Poll.fiveRounds_side_ne (label : Bool) :
    ¬ Eqv false [State] (unrolled (Poll.program ⟨label, false⟩) 4)
      (loopRegion (Poll.program ⟨label, true⟩)) [Bit] :=
  fun h => by cases (Poll.unrolled_eqv_iff ⟨label, false⟩ ⟨label, true⟩ 4 0).1 h

/-- The requesting and the silent nonreturning loops remain different. -/
theorem askSpin_not_eqv (label : Bool) :
    ¬ Eqv false [State] (loopRegion (askSpin label)) (loopRegion spin) [Bit] :=
  fun e => Prefix.askSpin_not_valid label (valid_of_eqv false e _ _)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitLoop
