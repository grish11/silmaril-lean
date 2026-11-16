module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Substitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Weakening

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Substitute one free name by a bound-closed object term in any de Bruijn scope. -/
def Tm.fsubst {k : ℕ} (t : Tm k) (x : String) (v : Tm 0) : Tm k :=
  match t with
  | .fv y => if y = x then v.castLE (Nat.zero_le k) else .fv y
  | .bv i => .bv i
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ t => .succ (t.fsubst x v)
  | .natrec C s z t => .natrec (C.fsubst x v) (s.fsubst x v)
      (z.fsubst x v) (t.fsubst x v)
  | .pi A B => .pi (A.fsubst x v) (B.fsubst x v)
  | .sigma A B => .sigma (A.fsubst x v) (B.fsubst x v)
  | .abs A b => .abs (A.fsubst x v) (b.fsubst x v)
  | .app f a => .app (f.fsubst x v) (a.fsubst x v)
  | .pair a b => .pair (a.fsubst x v) (b.fsubst x v)
  | .fst t => .fst (t.fsubst x v)
  | .snd t => .snd (t.fsubst x v)
  | .id A a b => .id (A.fsubst x v) (a.fsubst x v) (b.fsubst x v)
  | .refl a => .refl (a.fsubst x v)
  | .absurd C e => .absurd (C.fsubst x v) (e.fsubst x v)
  | .wtype A B => .wtype (A.fsubst x v) (B.fsubst x v)
  | .sup A B a f => .sup (A.fsubst x v) (B.fsubst x v) (a.fsubst x v) (f.fsubst x v)
  | .wrec A B C s t => .wrec (A.fsubst x v) (B.fsubst x v)
      (C.fsubst x v) (s.fsubst x v) (t.fsubst x v)


/-- Free names in declaration types; declaration keys are recorded separately by `dv`. -/
def Ctx.typeFvs : Ctx → Finset String
  | .nil => ∅
  | .cons Γ _ A => Γ.typeFvs ∪ A.fvs

/-- Every source lookup has an actual same-bound substituted typing in the target. -/
def Ctx.SubstB (levels : RuleBudget) (x : String) (a : Tm 0) (Γ Δ : Ctx) (H : Set Jdg := ∅) : Prop :=
  ∀ {y B}, Γ.Lookup y B → Δ.JEqB levels H (B.fsubst x a)
    ((Tm.fv y).fsubst x a) ((Tm.fv y).fsubst x a)

/-- Substitution transport is required only for the original hypothesis leaves. -/
def HypothesisSubstitution (levels : RuleBudget) (H H' : Set Jdg) (x : String) (v : Tm 0) : Prop :=
  ∀ {Γ Δ : Ctx} {A a b : Tm 0}, (⟨Γ, A, a, b⟩ : Jdg) ∈ H → Ctx.SubstB levels x v Γ Δ H' →
    Δ.JEqB levels H' .unit .star .star →
      Δ.JEqB levels H' (A.fsubst x v) (a.fsubst x v) (b.fsubst x v)

/-- A theory's actual leaves admit the structural operations used in dependent telescopes. -/
structure StructuralTheory (levels : RuleBudget) (H : Set Jdg) : Prop where
  weakening : HypothesisTransport levels H H
  substitution : ∀ x v, HypothesisSubstitution levels H H x v

/-- Each original axiom has empty context and no free names in its three terms.
This syntactic condition alone does not assert that the axioms are valid.
-/
def ClosedHypotheses (H : Set Jdg) : Prop :=
  ∀ j ∈ H, j.Γ = .nil ∧ j.A.fvs = ∅ ∧ j.a.fvs = ∅ ∧ j.b.fvs = ∅

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
