module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Unrolled.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Prefix.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.RoundsModel

/-! # Two models validate unrolling at every round count

These are calculations in the four-reply model and in the request-prefix
model. They hold for every number of rounds, five included, and for every
guarded step over the Bit-query signature. They are not derivations: no
equation of the quotient is inferred from them, and `Unrolls _ 4` stays
open. `Unrolled.Valid` proves the same for every supported model.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

section FourReply

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- In the four-reply model, the written loop on any number of rounds of a
guarded step has the arrow of the written loop on one round. -/
theorem rounds_fourReply {A B : Ty Empty} {s : Region signature.Instr}
    (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) (a : value A) :
    (denoteSingletonRegion J M
      (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType).of a =
    (denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hs).hasType).of a :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.rounds_model hs n a

/-- Every unrolled loop of the fragment has the complete runs of the
one-round loop. No unrolling law of the quotient is used. -/
theorem unrolled_observations_every (p : Program) (n : Nat) (g : Bool) :
    ((denoteSingletonRegion J M (unrolled_typed p n).hasType).of (Sum.inl (bit g))).outcomes =
      loopObservations p g :=
  congrArg Tagged.outcomes (rounds_fourReply (step_typed p) n (Sum.inl (bit g)))

/-- Five requests per iteration of a poll, against one. -/
theorem Poll.fiveRounds_observations (a : Poll) (g : Bool) :
    ((denoteSingletonRegion J M (unrolled_typed a.program 4).hasType).of (Sum.inl (bit g))).outcomes =
      loopObservations a.program g :=
  unrolled_observations_every a.program 4 g

end FourReply

section RequestPrefix

open Prefix

noncomputable local instance : InstructionModel J M signature.Instr := instructions prefixModel
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

/-- The same in the request-prefix model, pending requests included. -/
theorem rounds_prefix {A B : Ty Empty} {s : Region signature.Instr}
    (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) (a : value A) :
    (denoteSingletonRegion J M
      (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType).of a =
    (denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hs).hasType).of a :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.rounds_model hs n a

/-- So the request-prefix model does not separate an unrolled loop from
the one-round loop at any round count. -/
theorem unrolled_prefixObservations_every (p : Program) (n : Nat) (g : Bool) :
    ((denoteSingletonRegion J M (unrolled_typed p n).hasType).of (Sum.inl (bit g))).outcomes =
      prefixObservations p g :=
  congrArg Tagged.outcomes (rounds_prefix (step_typed p) n (Sum.inl (bit g)))

theorem Poll.fiveRounds_prefixObservations (a : Poll) (g : Bool) :
    ((denoteSingletonRegion J M (unrolled_typed a.program 4).hasType).of (Sum.inl (bit g))).outcomes =
      prefixObservations a.program g :=
  unrolled_prefixObservations_every a.program 4 g

end RequestPrefix

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
