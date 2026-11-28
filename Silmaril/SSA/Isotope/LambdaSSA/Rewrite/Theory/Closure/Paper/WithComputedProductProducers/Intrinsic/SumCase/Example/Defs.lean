module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs

/-! # An effectful discriminator and two ordered exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Semantics.Categorical Semantics.Interaction.Typed
open Silmaril.Elgot.ITree CategoryTheory

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)

abbrev Atom := ULift.{1} Unit
abbrev Payload : Ty Atom := .base ⟨()⟩
abbrev Labels := [Payload, Payload]

instance : AtomValues Atom where
  carrier _ := ULift.{1} Nat

abbrev PayloadValue := Ty.denote (AtomValues.carrier (κ := Atom)) Payload

inductive Op where
  | choose
  | left
  | right

instance : HasTy Op (Ty Atom) where
  src
    | .choose => Payload
    | .left | .right => product Payload Payload
  trg
    | .choose => coprod Payload Payload
    | .left | .right => Payload

instance : HasEff Op Bool where
  eff _ := true

inductive Request : Type → Type where
  | choose (original : Nat) : Request (Nat ⊕ Nat)
  | left (original payload : Nat) : Request Nat
  | right (original payload : Nat) : Request Nat

abbrev Model := ModelTree Request

attribute [local instance] typeModel

instance : InstructionModel Op (Ty Atom) Bool Model where
  denote
    | .choose, x => vis (.choose x.down) (fun n => pure (n.map ULift.up ULift.up))
    | .left, (x, a) => vis (.left x.down a.down) (fun n => pure (ULift.up n))
    | .right, (x, b) => vis (.right x.down b.down) (fun n => pure (ULift.up n))
  denotePure p h := by cases h
  denote_pure p h := by cases h

local notation "M" => ofMonadicTypeModel (τ := Ty Atom)

def program : SumCase Op Payload Labels where
  leftType := Payload
  rightType := Payload
  discriminator := .call Op.choose .input
  onLeft := ⟨Payload, 1, rfl, .returned (.call Op.left .input)⟩
  onRight := ⟨Payload, 0, rfl, .returned (.call Op.right .input)⟩

noncomputable def exit0 (n : Nat) : labelObj M Labels := labelInject M 0 (rfl : At Labels 0 Payload) (ULift.up n)
noncomputable def exit1 (n : Nat) : labelObj M Labels := labelInject M 1 (rfl : At Labels 1 Payload) (ULift.up n)

noncomputable def expected (x : PayloadValue) : Model (labelObj M Labels) :=
  vis (.choose x.down) fun
    | .inl a => vis (.left x.down a) (fun n => pure (exit1 n))
    | .inr b => vis (.right x.down b) (fun n => pure (exit0 n))

namespace Typing

inductive Annotation where
  | plain
  | marked

instance : TypeFormers Annotation where
  product _ _ := .plain
  unit := .plain
  coprod _ _ := .plain
  empty := .plain

instance : HasTy Unit Annotation where
  src _ := .plain
  trg _ := .plain

/-- Changing the right factor preserves the type of the discriminator and the
packed type of the right arm in this noninjective type algebra. -/
def annotated (B : Annotation) : SumCase Unit Annotation.plain [Annotation.plain, Annotation.plain] where
  leftType := .plain
  rightType := B
  discriminator := .call () .input
  onLeft := ⟨.plain, 1, rfl, .branchInput⟩
  onRight := ⟨.plain, 0, rfl, .branchInput⟩

end Typing

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example
