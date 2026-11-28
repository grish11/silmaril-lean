module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallITree

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling
open ComputedCallExample
open Paper.WithComputedCallReturns.Example
open Paper.WithComputedCallReturns.Example.ITree
  (TreeModel Atoms PayloadValue raw compatible reply)
open CategoryTheory
open Paper.Extension.Singleton (ofRegion)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Semantics (extend)
open Silmaril.Elgot.ITree

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := TreeModel)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

private def encode (x : Ty.denote Atoms Result) : Transfer (Sigma Atoms) :=
  (0, encodeValue Atoms Result x)

private def decode : Transfer (Sigma Atoms) → TreeModel (Ty.denote Atoms Result)
  | (0, .pair (.atom a) (.atom b)) => pure (a.2, b.2)
  | _ => diverge

private theorem decode_encode (x : Ty.denote Atoms Result) : decode (encode x) = pure x := by
  cases x
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem source_visible (x : PayloadValue) :
    (treeInterpretation.map sourceArrow).of x = expected x := by
  let := regionTypingCoherent raw compatible
  let ht := source_typed
  change ((denoteFunctor false J M (fun _ _ => ⟨rfl, rfl⟩)).map (ofRegion Seed ht)).of x = expected x
  unfold denoteFunctor
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  have eval := singletonDenote_tree raw compatible ht.hasType x (fun _ => .unit)
  have body :
      region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x)) source =
        (expected x >>= fun y => pure (encode y)) := by
    change region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x))
      (.let₁ (.op .consume (.let₁ (.op .produce (.var 0)) (.var 0)))
        (.br 0 (.pair (.var 1) (.var 0)))) = _
    simp [region, term, raw, reply, encodeValue, encode, expected, extend, vis_bind, -bind_pure_comp]
  let result : TreeModel (Ty.denote Atoms Result) :=
    (Semantics.Categorical.denoteSingletonRegion J M ht.hasType).of x
  change (result >>= fun y => pure (encode y)) =
    region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x)) _ at eval
  change result = expected x
  simpa only [bind_assoc, pure_bind, decode_encode, bind_pure] using congrArg (· >>= decode) (eval.trans body)

theorem retained_images_eq : treeInterpretation.map sourceArrow = treeInterpretation.map explicitArrow := by
  let := regionTypingCoherent raw compatible
  exact denoteFunctor_map_computedCall_post false J M (fun _ _ => ⟨rfl, rfl⟩)
    Op.consume operand_typed keepInput_typed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallITree
