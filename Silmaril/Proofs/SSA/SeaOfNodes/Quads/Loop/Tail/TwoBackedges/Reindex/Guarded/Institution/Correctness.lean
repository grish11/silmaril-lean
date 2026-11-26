module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Composition.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Proofs

open CategoryTheory
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Sentence)

variable {S T U : Signature} {result : Width}

/-- The actual deterministic checker fixes the certificate at a given
program and fact bank. Its proof fields need no separate transport law. -/
private theorem admitted_eq (p q : AdmittedAt S result)
    (source : @Admitted.source _ _ S.bankEq p = @Admitted.source _ _ S.bankEq q)
    (facts_eq : @Admitted.facts _ _ S.bankEq p = @Admitted.facts _ _ S.bankEq q) : p = q := by
  cases p with
  | mk p input cert admitted =>
    cases q with
    | mk q facts other success =>
      dsimp only at source facts_eq
      subst q
      cases facts_eq
      cases Except.ok.inj (admitted.symm.trans success)
      rfl

theorem mapAdmitted_id (p : AdmittedAt S result) : mapAdmitted (𝟙 S) p = p := by
  let _ := S.bankEq
  exact admitted_eq _ _ (program_refl p.source) (push_refl p.facts)

theorem mapAdmitted_comp (h : S ⟶ T) (k : T ⟶ U) (p : AdmittedAt S result) :
    mapAdmitted (h ≫ k) p = mapAdmitted k (mapAdmitted h p) := by
  let _ := S.bankEq
  exact admitted_eq _ _ (program_trans h k p.source).symm (push_trans h k p.facts).symm

theorem generated_id (p : Generated S result) : p.map (𝟙 S) = p := by
  cases p with
  | mk source artifacts generated =>
    cases generated
    change Generated.lower (mapAdmitted (𝟙 S) source) = Generated.lower source
    rw [mapAdmitted_id]

theorem sentence_id {P : Type} (f : P → P) (apply_id : ∀ p, f p = p) :
    Sentence.map f = id := by
  funext sentence
  cases sentence <;> simp only [Sentence.map, id, apply_id]

theorem sentence_comp {P Q R : Type} (f : P → Q) (g : Q → R) (composite : P → R)
    (apply_comp : ∀ p, composite p = g (f p)) :
    Sentence.map composite = Sentence.map g ∘ Sentence.map f := by
  funext sentence
  cases sentence <;> simp only [Function.comp_apply, Sentence.map, apply_comp]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Proofs
