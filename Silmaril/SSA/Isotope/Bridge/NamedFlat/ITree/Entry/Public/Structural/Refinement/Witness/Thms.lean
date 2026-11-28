module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

theorem StructuralEntry.explainRefinementOverCaptures?_sound {witness : CaptureTraceWitness V signature}
    (found : left.explainRefinementOverCaptures? right = some witness) : witness.Refutes left right :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.Witness.sound left right found

theorem StructuralEntry.explainRefinementOverCaptures?_isSome_iff :
    (left.explainRefinementOverCaptures? right).isSome = true ↔
      (left.refinementOverCaptures right).verdict = some false :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.Witness.has_witness left right

/-- Return the named representative and its directed trace, together with
their proof for the original runners. Use the aggregate's `emptyDomain`
flag to identify vacuous successes. -/
@[expose] def StructuralEntry.refinementCounterexample? :
    Option {witness : CaptureTraceWitness V signature // witness.Refutes left right} :=
  match found : left.explainRefinementOverCaptures? right with
  | none => none
  | some witness => some ⟨witness, left.explainRefinementOverCaptures?_sound right found⟩

theorem StructuralEntry.refinementCounterexample?_isSome_iff :
    (left.refinementCounterexample? right).isSome = true ↔
      (left.refinementOverCaptures right).verdict = some false := by
  rw [← left.explainRefinementOverCaptures?_isSome_iff right]
  unfold StructuralEntry.refinementCounterexample?
  split
  · rename_i found
    change false = true ↔ _
    rw [found]
    rfl
  · rename_i found
    change true = true ↔ _
    rw [found]
    rfl

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
