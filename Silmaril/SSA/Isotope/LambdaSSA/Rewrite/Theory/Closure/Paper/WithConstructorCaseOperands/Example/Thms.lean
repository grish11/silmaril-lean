module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.WithCaseOperandBeta.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.Example

/-! # Native replay and evaluation of the effectful packed fixture -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery hiding denote
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

/-- Every exact focused Bit generator is an instance of the general seed. -/
theorem focused_replay {Γ L : VCtx (Ty Empty)} {r s : Region signature.Instr}
    (h : Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta.Step Γ r s L) :
    Eqv Γ r s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.focused_replay h

/-- The original regions agree under the surrounding captured unit binder. -/
theorem replay : Eqv [Bit] source target Exits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.replay

/-- Equality holds on the original representatives with their ordered exits packed. -/
theorem packed_eq :
    Paper.Extension.Singleton.ofRegion Step source_typed.packExits =
      Paper.Extension.Singleton.ofRegion Step target_typed.packExits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.packed_eq

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The selected arm runs one request on the captured Bit. The second request
uses that reply's payload and forwards its own tagged reply to the original
ordered exit. This equality describes the entire trace computation. -/
theorem packed_execution (g : Bool) :
    ((denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)).map
      (Paper.Extension.Singleton.ofRegion Step source_typed.packExits)).of (bit g) =
      (request false (bit g) >>= fun first =>
        let q := match first with | .inl a | .inr a => a
        request true q >>= fun
          | .inl a => pure (Sum.inl a)
          | .inr a => pure (Sum.inr (Sum.inl a))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.packed_execution g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands.Example
