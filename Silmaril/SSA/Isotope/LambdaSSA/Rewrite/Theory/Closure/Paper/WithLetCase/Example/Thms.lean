module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.Example

/-! # The original packed region with both reply tags -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase.Example

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery
  (Trace signature model modelCoherent)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (bit)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open CategoryTheory

/-- The original source and distributed region have equal native packed arrows. -/
theorem packed_eq :
    Paper.Extension.Singleton.ofRegion Step source_typed.packExits =
      Paper.Extension.Singleton.ofRegion Step target_typed.packExits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.packed_eq

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The full trace computation of the original packed source runs the test
once and the selected arm once. The shared continuation receives its reply. -/
theorem packed_execution (g : Bool) :
    ((denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)).map
      (Paper.Extension.Singleton.ofRegion Step source_typed.packExits)).of (bit g) = expected g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.packed_execution g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase.Example
