module

public import Silmaril.SSA.Isotope.LetParIter.Defs

/-! # Typed bound-variable operations on the iterative tier -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter

open Parallel

universe u v w

variable {τ : Type u} [TypeFormers τ] {ν : Type v} [DecidableEq ν]
  {Φ : Type w} [HasTy Φ τ] {Γ : Ctx ν τ} {n k : Nat}
  {β : BoundCtx τ n} {δ : BoundCtx τ k}

abbrev Subst (β : BoundCtx τ n) (δ : BoundCtx τ k) (σ : Fin n → Tm ν Φ k) :=
  ∀ i, Derivation Φ Γ δ (σ i) (β.get i)

namespace Typing

/-- Lift a type-preserving renaming through the native binders and both parallel branches. -/
def rename {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
    (r : BoundCtx.Renaming β δ) :
    {a : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β a A →
      Derivation Φ Γ δ (a.rename r.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (i := i) => r.typed i ▸ .bv
  | _, _, .op ha => .op (rename r ha)
  | _, _, .let₁ ha hb => .let₁ (rename r ha) (rename (r.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (rename r ha) (rename r hb)
  | _, _, .let₂ ha hb => .let₂ (rename r ha) (rename ((r.up _).up _) hb)
  | _, _, .inl ha => .inl (rename r ha)
  | _, _, .inr ha => .inr (rename r ha)
  | _, _, .case he hl hr => .case (rename r he) (rename (r.up _) hl) (rename (r.up _) hr)
  | _, _, .abort ha => .abort (rename r ha)
  | _, _, .iter ha hb => .iter (rename r ha) (rename (r.up _) hb)
  | _, _, .par ha hb => .par (rename r ha) (rename r hb)

end Typing

namespace Subst

/-- The new binder is preserved and old substitution images are weakened. -/
def up {σ : Fin n → Tm ν Φ k} (s : Subst (Γ := Γ) β δ σ) (A : τ) :
    Subst (Γ := Γ) (.snoc β A) (.snoc δ A) (Parallel.Tm.upSub σ) :=
  Fin.cases .bv (fun i => Typing.rename (BoundCtx.Renaming.succ δ A) (s i))

end Subst

namespace Typing

/-- Typed simultaneous bound substitution. Equational use additionally requires pure images. -/
def bsubst {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
    {σ : Fin n → Tm ν Φ k} (s : Subst (Γ := Γ) β δ σ) :
    {a : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β a A → Derivation Φ Γ δ (a.bsubst σ) A
  | _, _, .fv h => .fv h
  | _, _, .bv (i := i) => s i
  | _, _, .op ha => .op (bsubst s ha)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, .let₂ ha hb => .let₂ (bsubst s ha) (bsubst ((s.up _).up _) hb)
  | _, _, .inl ha => .inl (bsubst s ha)
  | _, _, .inr ha => .inr (bsubst s ha)
  | _, _, .case he hl hr => .case (bsubst s he) (bsubst (s.up _) hl) (bsubst (s.up _) hr)
  | _, _, .abort ha => .abort (bsubst s ha)
  | _, _, .iter ha hb => .iter (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .par ha hb => .par (bsubst s ha) (bsubst s hb)

def lift {a : Tm ν Φ n} {A B : τ} (d : Derivation Φ Γ β a A) :
    Derivation Φ Γ (.snoc β B) a.lift A :=
  rename (BoundCtx.Renaming.succ β B) d

def underBinder {a : Tm ν Φ (n + 1)} {A X Y : τ} (d : Derivation Φ Γ (.snoc β Y) a A) :
    Derivation Φ Γ (.snoc (.snoc β X) Y) a.underBinder A :=
  rename (BoundCtx.Renaming.underBinder β X Y) d

def underTwoBinders {a : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (d : Derivation Φ Γ (.snoc (.snoc β Y) Z) a A) :
    Derivation Φ Γ (.snoc (.snoc (.snoc β X) Y) Z) a.underTwoBinders A :=
  rename (BoundCtx.Renaming.underTwoBinders β X Y Z) d

def leftResultRenaming (β : BoundCtx τ n) (A B : τ) :
    BoundCtx.Renaming (.snoc β A) (.snoc (.snoc β A) B) :=
  ⟨Fin.cases 1 (fun i => i.succ.succ), Fin.cases rfl (fun _ => rfl)⟩

/-- Rename a map on the left result into a tuple-destructuring scope. -/
def leftResult {a : Tm ν Φ (n + 1)} {A B C : τ} (d : Derivation Φ Γ (.snoc β A) a C) :
    Derivation Φ Γ (.snoc (.snoc β A) B) a.leftResult C :=
  rename (leftResultRenaming β A B) d

/-- Open the newest bound slot with a well-typed term. -/
def instantiate {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (db : Derivation Φ Γ (.snoc β A) b B) (da : Derivation Φ Γ β a A) :
    Derivation Φ Γ β (b.instantiate a) B :=
  bsubst (σ := Fin.cases a .bv) (Fin.cases da (fun _ => .bv)) db

end Typing
end Silmaril.Isotope.LetParIter
