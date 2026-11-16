module

public import Silmaril.Logic.Rewriting.Defs
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
namespace Silmaril.Logic.Rewriting
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {A : Algebraic.ManySorted.Signature S}

/-- Simultaneous, sort-correct substitution between finite contexts. -/
def substitute {k l} {Γ : Fin k → S} {Δ : Fin l → S}
    (σ : ∀ i, Algebraic.ManySorted.Term A Δ (Γ i)) {s} : Algebraic.ManySorted.Term A Γ s → Algebraic.ManySorted.Term A Δ s
  | .var i => σ i
  | .app op args => .app op (fun i => substitute σ (args i))

theorem eval_substitute (M : Algebraic.ManySorted.Model A) {k l} {Γ : Fin k → S} {Δ : Fin l → S}
    (σ : ∀ i, Algebraic.ManySorted.Term A Δ (Γ i)) (v : ∀ i, M.carrier (Δ i))
    {s} (t : Algebraic.ManySorted.Term A Γ s) :
    M.eval v (substitute σ t) = M.eval (fun i => M.eval v (σ i)) t := by
  induction t with
  | var => rfl
  | app op args ih => simp only [substitute, Algebraic.ManySorted.Model.eval]; congr; funext i; exact ih i

theorem eval_monotone (M : Model A) {k} {Γ : Fin k → S}
    (v w : ∀ i, M.algebra.carrier (Γ i)) (h : ∀ i, M.reaches (Γ i) (v i) (w i))
    {s} (t : Algebraic.ManySorted.Term A Γ s) : M.reaches s (M.algebra.eval v t) (M.algebra.eval w t) := by
  induction t with
  | var i => exact h i
  | app op args ih => exact M.congruence op _ _ ih

/-- Source replacement permits the substituted subterms themselves to advance. -/
theorem replacement (M : Model A) (e : Algebraic.ManySorted.Equation A)
    (rule : Sentence.Satisfies M (.rewrite e)) {l} {Δ : Fin l → S}
    (σ τ : ∀ i, Algebraic.ManySorted.Term A Δ (e.context i)) (v : ∀ i, M.algebra.carrier (Δ i))
    (h : ∀ i, M.reaches (e.context i) (M.algebra.eval v (σ i)) (M.algebra.eval v (τ i))) :
    M.reaches e.sort (M.algebra.eval v (substitute σ e.lhs))
      (M.algebra.eval v (substitute τ e.rhs)) := by
  rw [eval_substitute, eval_substitute]
  exact M.trans _ (rule _) (eval_monotone M _ _ h e.rhs)

/-- Equations transport a directed rewrite; opposite rewrites are not equality. -/
theorem modulo_equations (M : Model A) {s} {a a' b b' : M.algebra.carrier s}
    (ha : a = a') (hb : b = b') : M.reaches s a b ↔ M.reaches s a' b' := by
  cases ha; cases hb; rfl

def underlying (A : Algebraic.ManySorted.Signature S) : Model A ⥤ Algebraic.ManySorted.Model A where
  obj M := M.algebra
  map h := h.algebra

def discrete (M : Algebraic.ManySorted.Model A) : Model A where
  algebra := M
  reaches _ x y := x = y
  refl _ _ := rfl
  trans _ {_ _ _} h k := h.trans k
  congruence _ _ _ h := congrArg _ (funext h)

def equationToRewriting (S : Type) : Algebraic.ManySorted.institution S ⟶ institution S where
  app A := ⟨Sentence.equation, underlying A, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · rfl
    · rfl

def equationalInst (S : Type) : Inst := ⟨Algebraic.ManySorted.Signature S, Algebraic.ManySorted.institution S⟩
def rewritingInst (S : Type) : Inst := ⟨Algebraic.ManySorted.Signature S, institution S⟩

def fromEquational (S : Type) : Inst.CoHom (equationalInst S) (rewritingInst S) where
  Φ := 𝟭 _
  ρ := equationToRewriting S ≫ (Functor.leftUnitor (institution S)).inv

theorem fromEquational_modelExpansive (S : Type) : (fromEquational S).ModelExpansive :=
  fun _ M => ⟨discrete M, rfl⟩


theorem fromEquational_entails_iff (S : Type) (A : Algebraic.ManySorted.Signature S)
    (H : Set (Algebraic.ManySorted.Equation A)) (e : Algebraic.ManySorted.Equation A) :
    ((Algebraic.ManySorted.institution S).obj A).Entails H e ↔
      ((institution S).obj A).Entails (Sentence.equation '' H) (.equation e) :=
  (fromEquational S).entails_iff (fromEquational_modelExpansive S) A H e

end Silmaril.Logic.Rewriting
