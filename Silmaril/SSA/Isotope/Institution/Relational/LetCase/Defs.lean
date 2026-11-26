module

public import Silmaril.SSA.Isotope.Institution.Relational.Model.Defs
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetCase
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Relation

/-! # Typed LetCase equations with native relational evaluation -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Relational.LetCase

open CategoryTheory Semantics Theory
open Silmaril.Isotope.LetCase.LocallyNameless

universe u v w

variable {τ ε : Type u} {ν : Type w} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q R : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

/-- An exactly typed locally nameless program at the given bound context and result. -/
abbrev Program (P : InstrSig τ ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  Σ t : Tm ν P.Instr i.depth, Derivation P.Instr Γ i.bound t i.result

abbrev Sentence (P : InstrSig τ ε) (Γ : Ctx ν τ) := Equation (Program P Γ)

/-- Relabel the exact typing data along the native term map. -/
def mapDerivation (g : P ⟶ Q) : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν P.Instr n} →
    {A : τ} → Derivation P.Instr Γ β t A → Derivation Q.Instr Γ β (t.mapInstr g.instr) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op (f := f) a =>
      g.target f ▸ .op (f := g.instr f) ((g.source f).symm ▸ mapDerivation g a)
  | _, _, _, _, .let₁ a b => .let₁ (mapDerivation g a) (mapDerivation g b)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair a b => .pair (mapDerivation g a) (mapDerivation g b)
  | _, _, _, _, .let₂ a b => .let₂ (mapDerivation g a) (mapDerivation g b)
  | _, _, _, _, .inl a => .inl (mapDerivation g a)
  | _, _, _, _, .inr b => .inr (mapDerivation g b)
  | _, _, _, _, .case e l r => .case (mapDerivation g e) (mapDerivation g l) (mapDerivation g r)
  | _, _, _, _, .abort a => .abort (mapDerivation g a)

/-- Relabel a program's primitive instructions without changing its judgment. -/
def Program.translate (g : P ⟶ Q) {i : TypingIndex τ} (p : Program P Γ i) :
    Program Q Γ i :=
  ⟨p.1.mapInstr g.instr, mapDerivation g p.2⟩

/-- Translate both sides of an equation along the signature arrow. -/
def Sentence.translate (g : P ⟶ Q) (e : Sentence P Γ) : Sentence Q Γ :=
  e.map (fun _ => Program.translate g)

/-- The two programs have the same successful results in every environment. -/
def Sentence.Satisfies (M : Model D P) (e : Sentence P Γ) : Prop :=
  ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D e.index.bound) (b : D e.index.result),
    e.lhs.2.denoteRelation D M γ ρ b ↔ e.rhs.2.denoteRelation D M γ ρ b

end Silmaril.Isotope.Institution.Relational.LetCase
