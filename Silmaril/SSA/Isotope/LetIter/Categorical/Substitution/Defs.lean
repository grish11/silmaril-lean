module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

/-! # Typed substitutions for native categorical LetIter -/

@[expose] public section

universe u v w c

namespace Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}

/-- The typed images of a bound substitution, retaining their exact derivations. -/
abbrev DerivSubst {n m : Nat} (β : BoundCtx τ n) (δ : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Type (max u v w) :=
  (i : Fin n) → Derivation Φ Γ δ (σ i) (β.get i)

namespace Derivation

/-- Rename a derivation, preserving every choice of intermediate type. -/
def rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (ρ : TypedRenaming β δ) :
    {t : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
      Derivation Φ Γ δ (t.rename ρ.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => ρ.typed i ▸ .bv
  | _, _, .op h => .op (rename ρ h)
  | _, _, .let₁ h k => .let₁ (rename ρ h) (rename (TypedRenaming.up ρ _) k)
  | _, _, .unit => .unit
  | _, _, .pair h k => .pair (rename ρ h) (rename ρ k)
  | _, _, .let₂ h k => .let₂ (rename ρ h) (rename (TypedRenaming.up (TypedRenaming.up ρ _) _) k)
  | _, _, .inl h => .inl (rename ρ h)
  | _, _, .inr h => .inr (rename ρ h)
  | _, _, .case h l r => .case (rename ρ h) (rename (TypedRenaming.up ρ _) l) (rename (TypedRenaming.up ρ _) r)
  | _, _, .abort h => .abort (rename ρ h)
  | _, _, .iter h k => .iter (rename ρ h) (rename (TypedRenaming.up ρ _) k)

/-- Insert an extra newest bound slot, leaving the derivation's term unchanged up to weakening. -/
def lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (d : Derivation Φ Γ β t A) : Derivation Φ Γ (.snoc β B) t.lift A :=
  d.rename (TypedRenaming.succ β B)

end Derivation

namespace DerivSubst

/-- Lift a substitution under a binder, retaining the new variable. -/
def up {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ) (A : τ) :
    DerivSubst (Γ := Γ) (.snoc β A) (.snoc δ A) (Tm.upSub σ) :=
  Fin.cases .bv (fun i => (s i).lift)

end DerivSubst

namespace Derivation

/-- Apply a bound substitution at its supplied exact derivations. -/
def bsubst {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ) :
    {t : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
      Derivation Φ Γ δ (t.bsubst σ) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ h k => .let₁ (bsubst s h) (bsubst (s.up _) k)
  | _, _, .unit => .unit
  | _, _, .pair h k => .pair (bsubst s h) (bsubst s k)
  | _, _, .let₂ h k => .let₂ (bsubst s h) (bsubst ((s.up _).up _) k)
  | _, _, .inl h => .inl (bsubst s h)
  | _, _, .inr h => .inr (bsubst s h)
  | _, _, .case h l r => .case (bsubst s h) (bsubst (s.up _) l) (bsubst (s.up _) r)
  | _, _, .abort h => .abort (bsubst s h)
  | _, _, .iter h k => .iter (bsubst s h) (bsubst (s.up _) k)

/-- Instantiate one bound slot and keep the earlier variables. -/
def instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (db : Derivation Φ Γ (.snoc β A) b B) (da : Derivation Φ Γ β a A) :
    Derivation Φ Γ β (Tm.instantiate b a) B :=
  db.bsubst (σ := Fin.cases a (fun i => .bv i)) (Fin.cases da (fun _ => .bv))

end Derivation

end Silmaril.Isotope.LetIter.LocallyNameless

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {ν : Type w} {V : Type v}
  [Category.{c} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V] (M : TypeModel τ V)

/-- The tuple of the chosen values for a bound context. -/
noncomputable def boundTuple {R : V} : {n : Nat} → (β : BoundCtx τ n) →
    (∀ i, R ⟶ M.obj (β.get i)) → (R ⟶ boundObj M β)
  | _, .nil, _ => toUnit R
  | _, .snoc β _, p => lift (boundTuple β (fun i => p i.succ)) (p 0)

/-- Construct an environment from new bound slots while retaining its free context. -/
noncomputable def envSubstMap (Γ : Ctx ν τ) {n m : Nat} (β : BoundCtx τ n) (δ : BoundCtx τ m)
    (p : ∀ i, envObj M Γ δ ⟶ M.obj (β.get i)) : envObj M Γ δ ⟶ envObj M Γ β :=
  lift (fst _ _) (boundTuple M β p)

/-- The environment map that reads each bound slot at its renamed index. -/
noncomputable def envRenameMap (Γ : Ctx ν τ) {n m : Nat}
    {β : BoundCtx τ n} {δ : BoundCtx τ m} (ρ : LocallyNameless.TypedRenaming β δ) :
    envObj M Γ δ ⟶ envObj M Γ β :=
  envSubstMap M Γ β δ (fun i => boundVar M (Γ := Γ) (ρ.toFun i) ≫
    eqToHom (congrArg M.obj (ρ.typed i)))

/-- Forget the newest bound variable while retaining all earlier slots. -/
def dropSlot {Γ : Ctx ν τ} {n : Nat} (β : BoundCtx τ n) (A : τ) :
    envObj M Γ (.snoc β A) ⟶ envObj M Γ β :=
  (envSnocIso M Γ β A).inv ≫ fst _ _

end Silmaril.Isotope.LetIter.Semantics.Categorical
