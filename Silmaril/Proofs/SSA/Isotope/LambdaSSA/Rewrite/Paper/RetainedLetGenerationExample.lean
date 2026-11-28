module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Example.Defs

/-! # The retained bind runs its producer once and passes both values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGenerationExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet.Generation.Example
open Paper.WithComputedCallReturns.Example (Atom Payload)
open Paper.WithComputedCallReturns.Example.ITree (Atoms PayloadValue)
open CategoryTheory
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Elgot.ITree

theorem retained_generated : Generated Seed retainedArrow :=
  Paper.WithComputedCallReturns.generated_returnFragment false
    (.retained (ha := producer_typed) (hc := packedBody_typed)
      (.primitive Op.produce (.var rfl)) (.primitive Op.consume (.var rfl)))

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := TreeModel)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

private def encode (x : PayloadValue) : Transfer (Sigma Atoms) :=
  (0, encodeValue Atoms Payload x)

private def decode : Transfer (Sigma Atoms) → TreeModel PayloadValue
  | (0, .atom a) => pure a.2
  | _ => diverge

private theorem decode_encode (x : PayloadValue) : decode (encode x) = pure x := rfl

set_option backward.isDefEq.respectTransparency false in
theorem retained_visible (x : PayloadValue) :
    (interpretation.map retainedArrow).of x = expected x := by
  let := regionTypingCoherent raw compatible
  let ht := returnRegion_typed retained_typed
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithComputedCallReturns.joined_seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩))).map
    (ofRegion Seed ht)).of x = expected x
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  have eval := singletonDenote_tree raw compatible ht.hasType x (fun _ => .unit)
  have rawBody :
      region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x)) (returnRegion retained) =
        (expected x >>= fun y => pure (encode y)) := by
    change region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x))
      (.let₁ (.op .produce (.var 0)) (.let₁ (.op .consume (.pair (.var 1) (.var 0))) (.br 0 (.var 0)))) = _
    simp [region, term, raw, reply, encodeValue, encode, expected, extend, vis_bind, -bind_pure_comp]
  let result : TreeModel PayloadValue := (Semantics.Categorical.denoteSingletonRegion J M ht.hasType).of x
  change (result >>= fun y => pure (encode y)) =
    region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x)) _ at eval
  change result = expected x
  simpa only [bind_assoc, pure_bind, decode_encode, bind_pure] using congrArg (· >>= decode) (eval.trans rawBody)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGenerationExample
