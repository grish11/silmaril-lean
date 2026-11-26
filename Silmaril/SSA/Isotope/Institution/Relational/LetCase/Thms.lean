module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetCase.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Relational.LetCase

public section

namespace Silmaril.Isotope.Institution.Relational.LetCase

open CategoryTheory Semantics Theory Silmaril.Logic.Institution
open Silmaril.Isotope.LetCase.LocallyNameless

universe u v w

variable {τ ε : Type u} {ν : Type w} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q R : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

/-- The exact derivation map preserves identity. `HEq` accounts for the native term index. -/
theorem mapDerivation_id {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n} {A : τ}
    (d : Derivation P.Instr Γ β t A) : HEq (mapDerivation (𝟙 P) d) d :=
  mapDerivation_id_proof d

/-- The exact derivation map composes along the native term map. -/
theorem mapDerivation_comp (f : P ⟶ Q) (g : Q ⟶ R)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n} {A : τ}
    (d : Derivation P.Instr Γ β t A) :
    HEq (mapDerivation (f ≫ g) d) (mapDerivation g (mapDerivation f d)) :=
  mapDerivation_comp_proof f g d

@[simp] theorem Program.translate_id {i : TypingIndex τ} (p : Program P Γ i) :
    Program.translate (𝟙 P) p = p :=
  Sigma.ext (Tm.mapInstr_id p.1) (mapDerivation_id p.2)

@[simp] theorem Program.translate_comp (f : P ⟶ Q) (g : Q ⟶ R)
    {i : TypingIndex τ} (p : Program P Γ i) :
    Program.translate (f ≫ g) p = Program.translate g (Program.translate f p) :=
  Sigma.ext (Tm.mapInstr_comp f.instr g.instr p.1).symm (mapDerivation_comp f g p.2)

/-- Evaluating a relabelled derivation agrees with evaluation in the reduct. -/
theorem denoteRelation_translate (g : P ⟶ Q) (M : Model D Q)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n} {A : τ}
    (d : Derivation P.Instr Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A) :
    (mapDerivation g d).denoteRelation D M γ ρ b ↔
      d.denoteRelation D (M.reduct g) γ ρ b :=
  denoteRelation_translate_proof g M d γ ρ b

@[simp] theorem Sentence.translate_id (e : Sentence P Γ) :
    Sentence.translate (𝟙 P) e = e := by
  cases e
  simp [Sentence.translate, Equation.map]

@[simp] theorem Sentence.translate_comp (f : P ⟶ Q) (g : Q ⟶ R) (e : Sentence P Γ) :
    Sentence.translate (f ≫ g) e = Sentence.translate g (Sentence.translate f e) := by
  cases e
  simp [Sentence.translate, Equation.map]

theorem Sentence.satisfaction (g : P ⟶ Q) (M : Model D Q) (e : Sentence P Γ) :
    Sentence.Satisfies M (Sentence.translate g e) ↔ Sentence.Satisfies (M.reduct g) e := by
  simp only [Sentence.Satisfies, Sentence.translate, Equation.map, Program.translate,
    denoteRelation_translate]

/-- The relational LetCase institution in one free context and one value interpretation. -/
@[expose] def institution (D : τ → Type v) (Γ : Ctx ν τ)
    [ProductModel D] [UnitModel D] [CoproductModel D] :
    InstrSig τ ε ⥤ Room where
  obj P := ⟨Sentence P Γ, Cat.of (Model D P), Sentence.Satisfies⟩
  map g := ⟨Sentence.translate g, Model.reductFunctor D g, Sentence.satisfaction g⟩
  map_id _ := Room.hom_ext (funext Sentence.translate_id) (Model.reductFunctor_id D)
  map_comp f g :=
    Room.hom_ext (funext (Sentence.translate_comp f g)) (Model.reductFunctor_comp D f g)

end Silmaril.Isotope.Institution.Relational.LetCase
