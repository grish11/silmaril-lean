module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Substitute one free name by a bound-closed object term in any de Bruijn scope. -/
def ETm.fsubst {k : ℕ} (t : ETm k) (x : String) (v : ETm 0) : ETm k :=
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



/-- Free names in declaration types; declaration keys are recorded separately by `dv`. -/
def ECtx.typeFvs : ECtx → Finset String
  | .nil => ∅
  | .cons Γ _ A => Γ.typeFvs ∪ A.fvs

/-- Every source lookup has an actual substituted typing in the target. -/
def ECtx.Subst (x : String) (a : ETm 0) (Γ Δ : ECtx) : Prop :=
  ∀ {y B}, Γ.Lookup y B → ECtx.JEqH ∅ Δ (B.fsubst x a)
    ((ETm.fv y).fsubst x a) ((ETm.fv y).fsubst x a)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
