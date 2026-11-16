module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Thms
public import Silmaril.Logic.Algebraic.OrderSorted.Examples

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Representation.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
namespace Relocation
open Silmaril.Logic.Algebraic.OrderSorted.Examples

theorem filtered : LocallyFiltered signature := by
  intro s t u _ _
  exact ⟨max t u, le_max_left _ _, le_max_right _ _⟩

/-- The existing concrete byte/word/address model becomes literal subsets. -/
noncomputable def literal : LiteralModel signature := represent filtered model

/-- Original direct/staged byte widening remains equal in the literal model. -/
theorem coherence : coherenceEquation.Holds literal.algebra :=
  (satisfies_represent_iff filtered model coherenceEquation).mpr (coherence_valid model)

/-- Literal widening retains precisely the original ambient value. -/
theorem byte_address (x : model.algebra.carrier byte) :
    embed filtered model address (model.algebra.coerce (by decide : byte ≤ address) x) =
      embed filtered model byte x := embed_coerce filtered model _ x

/-- Evaluation retains the actual original relocation computation. -/
theorem relocation (base : Fin (bound address)) (addend : Fin (bound byte)) :
    (Silmaril.Logic.Algebraic.OrderSorted.Examples.relocation directAddend).eval literal.algebra
      (fun i => carrierEquiv filtered model (context i) (assignment base addend i)) =
      carrierEquiv filtered model address (relocate base addend) := by
  exact (eval_represent filtered model (Silmaril.Logic.Algebraic.OrderSorted.Examples.relocation directAddend) (assignment base addend)).trans
    (congrArg (carrierEquiv filtered model address) (eval_relocation base addend))
end Relocation

/-- Disconnected sorts, no operations and no values in either carrier. -/
abbrev emptyBase : EQ.Signature := ⟨Bool, fun _ _ _ => Empty⟩
abbrev emptySignature : Signature := discrete emptyBase
abbrev emptyAlgebra : EQ.Algebra emptyBase := ⟨fun _ => Empty, fun o => Empty.elim o⟩
abbrev emptyModel : Model emptySignature := expand emptyAlgebra

theorem empty_filtered : LocallyFiltered emptySignature := by
  intro s t u ht hu
  change s = t at ht
  change s = u at hu
  subst t
  subst u
  exact ⟨s, le_refl _, le_refl _⟩

/-- Local filtration does not require the distinct components to meet. -/
theorem empty_not_global : ¬ ∃ u : Bool,
    (show emptySignature.base.S from true) ≤ u ∧
      (show emptySignature.base.S from false) ≤ u := by
  rintro ⟨u, ht, hf⟩
  change true = u at ht
  change false = u at hf
  cases ht.trans hf.symm

/-- No nonemptiness is hidden in the represented literal carrier. -/
theorem empty_carrier (s : Bool) : IsEmpty ((represent empty_filtered emptyModel).carrier s) :=
  ⟨fun x => Empty.elim ((carrierEquiv empty_filtered emptyModel s).symm x)⟩

end Silmaril.Logic.Algebraic.OrderSorted.Representation.Examples
