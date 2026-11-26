module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Defs
public import Silmaril.SSA.Isotope.Institution.LetCase.Thms
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Relation

/-! # Typed LetCase equations with native relational evaluation -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Relational.LetCase

open CategoryTheory Semantics Theory
open Silmaril.Isotope.LetCase.LocallyNameless

universe u v

variable {τ ε ν : Type u} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

/-- The exact program carrier of the existing presented syntax. -/
abbrev Program (P : InstrSig τ ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  Models.Carrier P.Instr Γ i

/-- The existing exact equational institution's sentences, interpreted relationally. -/
abbrev Sentence (P : InstrSig τ ε) (Γ : Ctx ν τ) :=
  ((Silmaril.Isotope.Institution.LetCase.inst (ε := ε) Γ).obj P).Sen

/-- The existing exact syntax fold, at a fixed judgment index. -/
abbrev Program.translate (g : P ⟶ Q) {i : TypingIndex τ} (p : Program P Γ i) :
    Program Q Γ i :=
  (PresSig.translate ((Silmaril.Isotope.Institution.LetCase.pres Γ).map g)).map p

/-- The existing exact equational institution's forward sentence map. -/
abbrev Sentence.translate (g : P ⟶ Q) (e : Sentence P Γ) : Sentence Q Γ :=
  ((Silmaril.Isotope.Institution.LetCase.inst Γ).map g).sen e

/-- The two programs have the same successful results in every environment. -/
def Sentence.Satisfies (M : Model D P) (e : Sentence P Γ) : Prop :=
  ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D e.1.bound) (b : D e.1.result),
    e.2.1.2.denoteRelation D M γ ρ b ↔ e.2.2.2.denoteRelation D M γ ρ b

end Silmaril.Isotope.Institution.Relational.LetCase
