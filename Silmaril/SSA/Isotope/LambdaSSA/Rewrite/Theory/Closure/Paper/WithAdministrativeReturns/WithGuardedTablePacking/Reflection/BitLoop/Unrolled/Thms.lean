module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Unrolled.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Unrolled

/-! # Whole-loop replay across round groupings

Two written loops with different numbers of inline rounds have different
steps, and an unrolled step is not the step of a program. Their comparison
uses the unrolling laws of the quotient at the whole loop. The laws are
explicit premises of the general statements and are proved for round
counts that are products of twos and threes. For any other count the
premise `Unrolls _ n` is neither derived nor refuted here.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false

variable {p q : Program} {a b : Poll} {m n : Nat}

theorem unrolled_zero (p : Program) : unrolled p 0 = loopRegion p := rfl

/-- Two rounds: the repeat arm of the first step continues with a second
copy of the step. -/
theorem unrolled_one (p : Program) :
    unrolled p 1 = SyntacticCategory.iterateRegion State (thenRegion (stepRegion p) (stepRegion p)) := rfl

/-! ## Every program of the fragment -/

/-- An unrolled loop is a one-row guarded table. In this quotient it
equals its packed single-feedback dispatcher. -/
theorem unrolled_packed (p : Program) (n : Nat) :
    ∃ (R : Fin 1 → Ty Empty) (e : Region signature.Instr) (blocks : Fin 1 → Region signature.Instr)
      (he : ValueBranches [State] e (List.ofFn R ++ [Bit]))
      (hb : ∀ i, ValueBranches [R i, State] (blocks i) (List.ofFn R ++ [Bit])),
      unrolled p n = .cfg e 1 blocks ∧
        Eqv false [State] (unrolled p n) (packedReadbackRep R he hb).val [Bit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.unrolled_packed p n

/-- With the law for `n + 1` rounds, the unrolled loop equals the loop. -/
theorem unrolled_eqv_of_law (p : Program) (law : Unrolls N n) :
    Eqv false [State] (unrolled p n) (loopRegion p) [Bit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.unrolled_loop p law

/-- The law holds, with no premise, when `n + 1` is a product of twos and threes. -/
theorem unrolled_eqv (p : Program) (h : Smooth n) :
    Eqv false [State] (unrolled p n) (loopRegion p) [Bit] :=
  unrolled_eqv_of_law p (unrolls false h)

/-- Two unrolled loops are equal exactly when the one-round loops are. -/
theorem unrolled_eqv_iff_loops (lm : Unrolls N m) (ln : Unrolls N n) :
    Eqv false [State] (unrolled p m) (unrolled q n) [Bit] ↔
      Eqv false [State] (loopRegion p) (loopRegion q) [Bit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.unrolled_iff_loops lm ln

/-- The same reduction for validity in every model. -/
theorem unrolled_valid_iff_loops (lm : Unrolls N m) (ln : Unrolls N n) :
    Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType ↔
      Valid (loop_typed p).hasType (loop_typed q).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.unrolled_valid_iff_loops lm ln

/-! ## Replay on spellings of polls -/

/-- Whole-loop replay with the laws as premises: two unrolled spellings
of polls are equal exactly when the one-round keys agree. -/
theorem replay_of_laws (hp : Spells p a) (hq : Spells q b) (lm : Unrolls N m) (ln : Unrolls N n) :
    Eqv false [State] (unrolled p m) (unrolled q n) [Bit] ↔ p.tree.key = q.tree.key :=
  (unrolled_eqv_iff_loops lm ln).trans (eqv_iff_key hp hq)

/-- Whole-loop replay for round counts that are products of twos and threes. -/
theorem replay (hp : Spells p a) (hq : Spells q b) (hm : Smooth m) (hn : Smooth n) :
    Eqv false [State] (unrolled p m) (unrolled q n) [Bit] ↔ p.tree.key = q.tree.key :=
  replay_of_laws hp hq (unrolls false hm) (unrolls false hn)

/-- On the same slice, validity in every model is also equality of keys. -/
theorem replay_valid (hp : Spells p a) (hq : Spells q b) (hm : Smooth m) (hn : Smooth n) :
    Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType ↔ p.tree.key = q.tree.key :=
  (unrolled_valid_iff_loops (unrolls false hm) (unrolls false hn)).trans (valid_iff_key hp hq)

/-- Reflection at two unrolled spellings of polls. -/
theorem unrolled_reflects (hp : Spells p a) (hq : Spells q b) (hm : Smooth m) (hn : Smooth n) :
    Reflects false (unrolled_typed p m) (unrolled_typed q n) :=
  fun h => (replay hp hq hm hn).2 ((replay_valid hp hq hm hn).1 h)

/-! ## The smallest pair and a separation -/

/-- The poll with two requests per iteration equals the poll with one. -/
theorem Poll.twoRounds_eqv (a : Poll) :
    Eqv false [State] (unrolled a.program 1) (loopRegion a.program) [Bit] :=
  unrolled_eqv a.program (.double .one)

/-- Three requests per iteration equal two. -/
theorem Poll.threeRounds_eqv_two (a : Poll) :
    Eqv false [State] (unrolled a.program 2) (unrolled a.program 1) [Bit] :=
  (unrolled_eqv a.program (.triple .one)).trans (Poll.twoRounds_eqv a).symm

/-- Unrolled polls are equal only when they unroll the same poll. -/
theorem Poll.unrolled_eqv_iff (a b : Poll) (hm : Smooth m) (hn : Smooth n) :
    Eqv false [State] (unrolled a.program m) (unrolled b.program n) [Bit] ↔ a = b :=
  (unrolled_eqv_iff_loops (unrolls false hm) (unrolls false hn)).trans (Poll.eqv_iff a b)

/-- A two-round loop on one label is not the one-round loop on the other. -/
theorem Poll.twoRounds_ne (side : Bool) :
    ¬ Eqv false [State] (unrolled (Poll.program ⟨false, side⟩) 1) (loopRegion (Poll.program ⟨true, side⟩)) [Bit] :=
  fun h => by cases (Poll.unrolled_eqv_iff ⟨false, side⟩ ⟨true, side⟩ (.double .one) .one).1 h

/-! ## The same whole behaviour in the fixed interpreter -/

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- By soundness, an unrolled loop has the complete runs of the one-round loop. -/
theorem unrolled_observations (p : Program) (law : Unrolls N n) (g : Bool) :
    ((denoteSingletonRegion J M (unrolled_typed p n).hasType).of (Sum.inl (bit g))).outcomes =
      loopObservations p g := by
  have eq := (unrolled_eqv_of_law p law).sound false J M (fun _ _ => ⟨rfl, rfl⟩)
    (unrolled_typed p n).hasType (loop_typed p).hasType
  unfold loopObservations denoteSingletonRegion
  rw [eq]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
