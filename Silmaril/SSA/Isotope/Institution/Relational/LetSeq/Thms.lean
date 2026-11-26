module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetSeq.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Relational.LetSeq

public section

namespace Silmaril.Isotope.Institution.Relational.LetSeq

open CategoryTheory Semantics Theory Silmaril.Logic.Institution
open Silmaril.Isotope.LetSeq.LocallyNameless

universe u v

variable {τ ε ν : Type u} [DecidableEq ν] [HasProduct τ] [HasUnit τ]
variable {Γ : Ctx ν τ} {P Q : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D]

/-- The existing sentence translation commutes with native relational evaluation. -/
theorem denoteRelation_translate (g : P ⟶ Q) (M : Model D Q)
    {i : TypingIndex τ} (p : Program P Γ i)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D i.bound) (b : D i.result) :
    (Program.translate g p).2.denoteRelation D M γ ρ b ↔
      p.2.denoteRelation D (M.reduct g) γ ρ b :=
  denoteRelation_translate_proof g M p γ ρ b

theorem Sentence.satisfaction (g : P ⟶ Q) (M : Model D Q) (e : Sentence P Γ) :
    Sentence.Satisfies M (Sentence.translate g e) ↔ Sentence.Satisfies (M.reduct g) e :=
  forall_congr' fun γ => forall_congr' fun ρ => forall_congr' fun b =>
    iff_congr (denoteRelation_translate g M e.2.1 γ ρ b)
      (denoteRelation_translate g M e.2.2 γ ρ b)

/-- The relational LetSeq institution in one free context and one value interpretation. -/
@[expose] def institution (D : τ → Type v) (Γ : Ctx ν τ)
    [ProductModel D] [UnitModel D] :
    InstrSig τ ε ⥤ Room where
  obj P := ⟨Sentence P Γ, Cat.of (Model D P), Sentence.Satisfies⟩
  map g := ⟨Sentence.translate g, Model.reductFunctor D g, Sentence.satisfaction g⟩
  map_id P := by
    have h := congrArg Corridor.sen ((Silmaril.Isotope.Institution.LetSeq.inst Γ).map_id P)
    exact Room.hom_ext h (Model.reductFunctor_id D)
  map_comp f g := by
    have h := congrArg Corridor.sen ((Silmaril.Isotope.Institution.LetSeq.inst Γ).map_comp f g)
    exact Room.hom_ext h (Model.reductFunctor_comp D f g)

/-- The relational interpretation uses the existing exact institution's sentence functor. -/
theorem sentenceFunctor_eq (D : τ → Type v) (Γ : Ctx ν τ)
    [ProductModel D] [UnitModel D] :
    sentenceFunctor (institution (ε := ε) D Γ) =
      sentenceFunctor (Silmaril.Isotope.Institution.LetSeq.inst (ε := ε) Γ) := rfl

end Silmaril.Isotope.Institution.Relational.LetSeq
