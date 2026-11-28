module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.ITree.Defs

/-! # A captured return whose second request reads both fields -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet.Generation.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Atom Payload)
open Paper.WithComputedCallReturns.Example.ITree (Atoms PayloadValue)
open Paper.Extension.Singleton (denoteFunctor ofType ofRegion)
open Paper.PackedBody (applyPackedTerm_typed)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree

inductive Op where
  | produce
  | consume

instance : HasTy Op (Ty Atom) where
  src
    | .produce => Payload
    | .consume => product Payload Payload
  trg _ := Payload

instance : HasEff Op Bool where
  eff _ := true

def retained : Tm Op :=
  .let₁ (.op .produce (.var 0)) (.op .consume (.pair (.var 1) (.var 0)))

theorem producer_typed : Tm.HasType [Payload] (.op Op.produce (.var 0)) Payload :=
  .op (.var rfl)

theorem packedBody_typed : Tm.HasType [product Payload Payload] (.op Op.consume (.var 0)) Payload :=
  .op (.var rfl)

theorem retained_typed : Tm.HasType [Payload] retained Payload :=
  .let₁ producer_typed (applyPackedTerm_typed packedBody_typed)

inductive Request : Type → Type where
  | produce (input : Nat) : Request Nat
  | consume (original result : Nat) : Request Nat

abbrev TreeModel := ModelTree Request

def reply (n : Nat) : PayloadValue := ⟨n⟩

attribute [local instance] typeModel

instance : InstructionModel Op (Ty Atom) Bool TreeModel where
  denote
    | .produce, x => vis (.produce x.down) (fun n => pure (reply n))
    | .consume, (x, y) => vis (.consume x.down y.down) (fun n => pure (reply n))
  denotePure p h := by cases h
  denote_pure p h := by cases h

def raw : Primitive Request Op (Sigma Atoms)
  | .produce, .atom x => vis (.produce x.2.down) (fun n => pure (encodeValue Atoms Payload (reply n)))
  | .consume, .pair (.atom x) (.atom y) =>
      vis (.consume x.2.down y.2.down) (fun n => pure (encodeValue Atoms Payload (reply n)))
  | _, _ => diverge

theorem compatible :
    Compatible (κ' := Atom) ⟨fun p x =>
      InstructionModel.denote (τ := Ty Atom) (ε := Bool) (m := TreeModel) p x⟩ raw := by
  have call (e : Request Nat) :
      vis e (fun n => pure (encodeValue Atoms Payload (reply n))) =
        ((vis e (fun n => (pure (reply n) : TreeModel PayloadValue))) >>= fun y =>
          pure (encodeValue Atoms Payload y)) := by simp only [vis_bind, pure_bind]
  intro p x
  cases p with
  | produce => exact call (.produce x.down)
  | consume => exact call (.consume x.1.down x.2.down)

attribute [local instance] categoricalInstructions

abbrev Seed := Paper.WithComputedCallReturns.JoinedStep (τ := Ty Atom) (Φ := Op) false

noncomputable def interpretation :
    Paper.Extension.Singleton.TypeCategory Seed ⥤ Kleisli (ofTypeMonad TreeModel) :=
  letI := regionTypingCoherent raw compatible
  denoteFunctor (typeJ (m := TreeModel)) (Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom))
    (fun _ _ => ⟨rfl, rfl⟩) (Paper.WithComputedCallReturns.joined_seedDenotes false _ _ (fun _ _ => ⟨rfl, rfl⟩))

def retainedArrow : ofType Seed Payload ⟶ ofType Seed Payload :=
  ofRegion Seed (returnRegion_typed retained_typed)

/-- The consumer receives the original input and the producer's reply. -/
def expected (x : PayloadValue) : TreeModel PayloadValue :=
  vis (.produce x.down) (fun n => vis (.consume x.down n) (fun m => pure (reply m)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet.Generation.Example
