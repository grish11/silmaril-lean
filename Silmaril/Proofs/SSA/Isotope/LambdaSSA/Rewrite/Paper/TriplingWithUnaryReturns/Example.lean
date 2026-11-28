module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns
  (Step fromWithComputedCalls lowering generated_returnFragment generated_literalLet)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example (explicitArrow)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example
  (retained_ne singleBindArrow)
open Paper.RetainedLet (returnOnce_typed unpackBody_typed)
open Paper.Extension.Singleton (ofRegion_eq_iff)
open Paper.WithComputedCallReturns.Example (Atom)
open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Op Payload sequenced_typed operand_typed nested_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (ReturnFragment)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (Result keepInput_typed explicitSequence_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example (singleBind_typed)
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)

abbrev Seed := Step (τ := Ty Atom) (Φ := Op) false

theorem retained_eq : (fromWithComputedCalls false).map explicitArrow =
    (fromWithComputedCalls false).map singleBindArrow :=
  (ofRegion_eq_iff Seed explicitSequence_typed singleBind_typed).2
    (.lsubstPost (lowering false sequenced_typed) (returnRegion_typed sequenced_typed)
      (returnOnce_typed sequenced_typed) (fun _ _ hi => (keepInput_typed hi).hasType))

private theorem sequenced_fragment : ReturnFragment false sequenced_typed := by
  let hv : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload := .var rfl
  let produce := Tm.HasType.op (f := Op.produce) hv.hasType
  let consume := Tm.HasType.op (f := Op.consume) hv.hasType
  have first : ReturnFragment false operand_typed :=
    .seq (ha := produce) (hb := hv.hasType) (.call Op.produce (.value hv)) (.value hv)
  exact .seq (ha := operand_typed) (hb := consume) first (.call Op.consume (.value hv))

theorem singleBind_generated : Generated Seed (ofRegion Seed singleBind_typed) := by
  let body : ValueBranches [Payload, Payload] (.br 0 (.pair (.var 1) (.var 0)) : Region Op) [Result] :=
    .br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))
  let identity : ValueBranches [Result] (.br 0 (.var 0) : Region Op) [Result] := .br (ℓ := 0) rfl (.var rfl)
  have unpack := (ofRegion_eq_iff Seed (unpackBody_typed body) identity).2
    (.paper (.productEta (.let₂Eta rfl rfl)))
  have gid := Paper.Extension.Singleton.Generation.generated_branchValue Seed
    (.var (i := 0) (A := Result) (Γ := [Result]) rfl)
  exact generated_literalLet false sequenced_typed body
    (generated_returnFragment false sequenced_fragment) (unpack.symm ▸ gid)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns
