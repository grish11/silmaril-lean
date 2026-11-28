module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Thms
public import Silmaril.SSA.Isotope.LetCase.Categorical.Defs
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Quot
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}

/-- An exact native term with one typed input slot and no free names. A
product input can carry a whole packet, and a sum return retains its tag. -/
abbrev Program (Φ : Type v) [HasTy Φ τ] (A B : τ) :=
  Σ t : Tm Empty Φ 1, Derivation Φ Ctx.nil (.snoc .nil A) t B

namespace Program

variable {A B C : τ}

/-- Return the sole input slot. -/
def id (A : τ) : Program Φ A A :=
  ⟨.bv 0, .bv⟩

/-- Sequence by a native let. Weakening inserts the old input below the
new return binder of the second program. -/
def seq (p : Program Φ A B) (q : Program Φ B C) : Program Φ A C :=
  ⟨.let₁ p.1 q.1.underBinder, .let₁ p.2 q.2.underBinder⟩

/-- Run the exact native typing witness on the entire typed input. -/
def run (M : InstructionModel D Φ (Tree Events)) (p : Program Φ A B) (a : D A) :
    Tree Events (D B) :=
  p.2.denote D M (fun x => x.elim) (BoundEnv.snoc (β := .nil) (fun i => i.elim0) a)

/-- Uniform finite handled-trace inclusion at a fixed policy. Every
handler state is tested so the comparison is available after a handoff. -/
def Refines (M : InstructionModel D Φ (Tree Events)) (policy : Handler State Events)
    (p q : Program Φ A B) : Prop :=
  ∀ a x, HandledTraceLE policy x (p.run M a) (q.run M a)

theorem Refines.refl (M : InstructionModel D Φ (Tree Events)) (policy : Handler State Events)
    (p : Program Φ A B) : Refines M policy p p :=
  fun _ _ => .refl _

theorem Refines.trans {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
    {p q r : Program Φ A B} (pq : Refines M policy p q) (qr : Refines M policy q r) :
    Refines M policy p r :=
  fun a x => (pq a x).trans (qr a x)

/-- Quotient exact native typing witnesses by mutual semantic inclusion. -/
def setoid (M : InstructionModel D Φ (Tree Events)) (policy : Handler State Events)
    (A B : τ) : Setoid (Program Φ A B) where
  r p q := Refines M policy p q ∧ Refines M policy q p
  iseqv := ⟨fun p => ⟨.refl M policy p, .refl M policy p⟩, And.symm,
    fun pq qr => ⟨pq.1.trans qr.1, qr.2.trans pq.2⟩⟩

end Program

/-- Native interface types at one fixed primitive interpretation and policy. -/
structure Interface (M : InstructionModel D Φ (Tree Events)) (policy : Handler State Events) where
  ty : τ

variable {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

/-- A native typed program modulo mutual finite handled-trace inclusion. -/
abbrev Arrow (A B : Interface M policy) :=
  Quotient (Program.setoid M policy A.ty B.ty)

namespace Arrow

/-- Descend the oriented comparison to the two observational classes. -/
def le {A B : Interface M policy} (f g : Arrow A B) : Prop :=
  Quotient.liftOn₂' f g (Program.Refines M policy) fun _ _ _ _ left right =>
    propext ⟨fun h => left.2.trans (h.trans right.1), fun h => left.1.trans (h.trans right.2)⟩

end Arrow
end Silmaril.Isotope.LetCase.HandledTrace
