module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetIter.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Relational.LetIter

public section

namespace Silmaril.Isotope.Institution.Relational.LetIter

open CategoryTheory Semantics Theory Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel (Algebra)
open Silmaril.Isotope.LetIter.LocallyNameless

universe u v

variable {τ ε ν : Type u} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

/-- The inherited translation is the exact syntax fold, including its derivation. -/
theorem Program.translate_eq_fold (g : P ⟶ Q) {i : TypingIndex τ}
    (p : Program P Γ i) :
    Program.translate g p =
      Models.denote (Algebra.reductObj (Silmaril.Isotope.Institution.LetIter.sigHom Γ g)
        (Models.syntaxAlgebra Q.Instr Γ)) p.2 :=
  translate_eq_fold_proof g p

/-- The primitive clause casts the translated argument to the target opcode's input type
and casts the resulting derivation back to the original result type. -/
theorem Program.translate_op (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    (op : P.Instr) (p : Program P Γ ⟨n, β, instrSrc op⟩) :
    Program.translate g (⟨.op op p.1, .op p.2⟩ : Program P Γ ⟨n, β, instrTrg op⟩) =
      ⟨.op (g.instr op) (Program.translate g p).1,
        g.target op ▸ .op ((g.source op).symm ▸ (Program.translate g p).2)⟩ :=
  translate_op_proof g op p

/-- Sentence translation keeps the judgment and folds each selected endpoint. -/
theorem Sentence.translate_endpoints (g : P ⟶ Q) (e : Sentence P Γ) :
    Sentence.translate g e = ⟨e.1, Program.translate g e.2.1, Program.translate g e.2.2⟩ :=
  rfl

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

/-- The relational LetIter institution in one free context and one value interpretation. -/
@[expose] def institution (D : τ → Type v) (Γ : Ctx ν τ)
    [ProductModel D] [UnitModel D] [CoproductModel D] :
    InstrSig τ ε ⥤ Room where
  obj P := ⟨Sentence P Γ, Cat.of (Model D P), Sentence.Satisfies⟩
  map g := ⟨Sentence.translate g, Model.reductFunctor D g, Sentence.satisfaction g⟩
  map_id P := by
    have h := congrArg Corridor.sen ((Silmaril.Isotope.Institution.LetIter.inst Γ).map_id P)
    exact Room.hom_ext h (Model.reductFunctor_id D)
  map_comp f g := by
    have h := congrArg Corridor.sen ((Silmaril.Isotope.Institution.LetIter.inst Γ).map_comp f g)
    exact Room.hom_ext h (Model.reductFunctor_comp D f g)

/-- The relational interpretation uses the existing exact institution's sentence functor. -/
theorem sentenceFunctor_eq (D : τ → Type v) (Γ : Ctx ν τ)
    [ProductModel D] [UnitModel D] [CoproductModel D] :
    sentenceFunctor (institution (ε := ε) D Γ) =
      sentenceFunctor (Silmaril.Isotope.Institution.LetIter.inst (ε := ε) Γ) := rfl

end Silmaril.Isotope.Institution.Relational.LetIter
