module

public import Silmaril.Logic.Algebraic.OrderSorted.Thms
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.OrderSorted.Free
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {A : Signature} {k : ℕ} {Γ : Fin k → A.base.S}

mutual
/-- A core retains its principal sort: a variable or a base operation whose
arguments are already normal. Coercions are not core constructors. -/
inductive Core (A : Signature) {k : ℕ} (Γ : Fin k → A.base.S) : A.base.S → Type where
  | var (i : Fin k) : Core A Γ (Γ i)
  | app {n w s} (o : A.base.Op n w s) (args : ∀ i, Normal A Γ (w i)) : Core A Γ s
/-- One root inclusion packages a core at its principal sort. Nested inclusions
are composed, not retained as independent syntax nodes. -/
inductive Normal (A : Signature) {k : ℕ} (Γ : Fin k → A.base.S) : A.base.S → Type where
  | up {s t} (h : s ≤ t) (core : Core A Γ s) : Normal A Γ t
end

/-- Forget no core data when widening: only the root order witness changes. -/
def coerce {s t : A.base.S} (h : s ≤ t) : Normal A Γ s → Normal A Γ t
  | .up k c => .up (le_trans k h) c

def embed {s : A.base.S} (c : Core A Γ s) : Normal A Γ s := .up (le_refl s) c

def generator (i : Fin k) : Normal A Γ (Γ i) := embed (.var i)

@[simp] theorem coerce_identity {s : A.base.S} (x : Normal A Γ s) : coerce (le_refl s) x = x := by
  cases x
  rfl

theorem coerce_injective {s t : A.base.S} (h : s ≤ t) :
    Function.Injective (coerce (A := A) (Γ := Γ) h) := by
  intro x y he
  cases x with
  | up p c =>
    cases y with
    | up q d =>
      cases he
      rfl

@[simp] theorem coerce_composition {s t u : A.base.S} (h : s ≤ t) (j : t ≤ u)
    (x : Normal A Γ s) : coerce j (coerce h x) = coerce (le_trans h j) x := by
  cases x
  rfl

/-- Free coherent algebra, using the existing compiled EQ signature and model
category. Base operations create cores; inclusion operations compose root paths. -/
def model (A : Signature) {k : ℕ} (Γ : Fin k → A.base.S) : Model A where
  algebra := {
    carrier := Normal A Γ
    op := fun o args => match o with
      | .base o => embed (.app o args)
      | .inclusion _ _ h => coerce h (args 0) }
  coherent := {
    identity := fun _ => coerce_identity
    injective := coerce_injective
    composition := fun h j => coerce_composition h j }

mutual
/-- Evaluate a principal core using the actual base operations. -/
def evalCore (M : Model A) (v : ∀ i, M.algebra.carrier (Γ i)) :
    {s : A.base.S} → Core A Γ s → M.algebra.carrier s
  | _, .var i => v i
  | _, .app o args => M.algebra.op (.base o) (fun i => eval M v (args i))
/-- Evaluate the root inclusion using the model's actual coherent coercion. -/
def eval (M : Model A) (v : ∀ i, M.algebra.carrier (Γ i)) :
    {s : A.base.S} → Normal A Γ s → M.algebra.carrier s
  | _, .up h c => M.algebra.coerce h (evalCore M v c)
end

@[simp] theorem eval_embed (M : Model A) (v : ∀ i, M.algebra.carrier (Γ i))
    {s} (c : Core A Γ s) : eval M v (embed c) = evalCore M v c :=
  M.coherent.identity _ _

@[simp] theorem eval_generator (M : Model A) (v : ∀ i, M.algebra.carrier (Γ i)) (i : Fin k) :
    eval M v (generator i) = v i := eval_embed M v (.var i)

theorem eval_coerce (M : Model A) (v : ∀ i, M.algebra.carrier (Γ i))
    {s t} (h : s ≤ t) (x : Normal A Γ s) :
    eval M v (coerce h x) = M.algebra.coerce h (eval M v x) := by
  cases x with
  | up p c => exact (M.coherent.composition p h _).symm

/-- Evaluation is an actual homomorphism of the existing coherent model category. -/
def foldHom (M : Model A) (v : ∀ i, M.algebra.carrier (Γ i)) : model A Γ ⟶ M where
  map _ := eval M v
  map_op o args := by
    cases o with
    | base o => exact eval_embed M v (.app o args)
    | inclusion s t h =>
      change eval M v (coerce h (args 0)) = _
      rw [eval_coerce]
      apply congrArg (M.algebra.op (.inclusion _ _ h))
      funext i
      exact congrArg (fun j => eval M v (args j)) (Subsingleton.elim 0 i)

abbrev closedContext (A : Signature) : Fin 0 → A.base.S := Fin.elim0
abbrev closedModel (A : Signature) := model A (closedContext A)

end Silmaril.Logic.Algebraic.OrderSorted.Free
