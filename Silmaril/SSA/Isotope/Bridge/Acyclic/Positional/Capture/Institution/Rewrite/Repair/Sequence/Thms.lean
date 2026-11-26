module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Normalize

/-! # Normalization by the typed empty-sequencing rule -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open Isotope.LetCase.LocallyNameless (AbortCongr Tm)
open LambdaSSA.Acyclic (Operand)

/-- Canonicalize empty elimination at any surrounding bound context. -/
theorem Body.normalize (p : Body) {n : Nat} (β : BoundCtx Sorts n) :
    AbortCongr (Ctx.nil : Ctx Empty Sorts) (p.operand β).2 (p.canonical.operand β).2 :=
  normalize_operand p β

/-- The ordered effect sequence does not read its surrounding context. -/
theorem Body.operand_bsubst (p : Body) {n m : Nat} (β : BoundCtx Sorts n) (δ : BoundCtx Sorts m)
    (σ : Fin n → Tm Empty signature.Instr m) :
    (p.operand β).1.bsubst σ = (p.operand δ).1 :=
  operand_bsubst_proof p β δ σ

/-- The same context independence holds on the actual typing data. -/
theorem Body.operand_rename (p : Body) {n m : Nat} {β : BoundCtx Sorts n} {δ : BoundCtx Sorts m}
    (ρ : BoundCtx.Renaming β δ) :
    (⟨_, (p.operand β).2.rename ρ⟩ : Operand signature.Instr δ Ty.unit) = p.operand δ :=
  operand_rename_proof p ρ

/-- Matching traces give a derivation by the new rule under the actual entry
and operand binders. The selected exit and its ordered interface are preserved. -/
theorem sequencesEmpty_of_normal (tail : List Sorts) (p q : Body) (h : p.normal = q.normal) :
    SequencesEmpty (equation tail p q) :=
  sequencesEmpty_normal_proof tail p q h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
