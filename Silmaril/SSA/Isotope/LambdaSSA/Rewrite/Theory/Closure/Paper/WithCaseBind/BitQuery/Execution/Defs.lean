module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Defs

/-! # Evaluation of the opt-in query profile at its ordered exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.Execution

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery
open CategoryTheory
open Semantics.Categorical
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

noncomputable abbrev runAt {Γ : VCtx (Ty Empty)} {r : Region signature.Instr}
    (h : ValueBranches Γ r Exits) (x : ctxObj M Γ) : Trace (value (packedExitType Exits)) :=
  (denoteRegion J M h.hasType ≫ (J).map (packLabel M Exits)).of x

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.Execution
