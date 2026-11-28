module

public import Silmaril.Logic.BrookesSC.Defs

public section

namespace Silmaril.Proofs.Logic.BrookesSC

open CategoryTheory Silmaril.Logic.BrookesSC

universe u v

variable {W : World.{u}} {S T U : Signature W} {D : Target.{u,v} W} {A : Type u}

theorem program_translate_id (p : Program S A) : p.translate (𝟙 S) = p := by
  induction p with
  | ret => rfl
  | call op next ih => exact congrArg (Program.call op) (funext ih)

theorem program_translate_comp (f : S ⟶ T) (g : T ⟶ U) (p : Program S A) :
    p.translate (f ≫ g) = (p.translate f).translate g := by
  induction p with
  | ret => rfl
  | call op next ih => exact congrArg (Program.call (g.label (f.label op))) (funext ih)

theorem eval_translate (f : S ⟶ T) (M : Model D T) (p : Program S A) :
    M.eval (p.translate f) = (M.reduct f).eval p := by
  induction p with
  | ret => rfl
  | @call d op next ih =>
    have hop : M.operation (f.label op) = (M.reduct f).operation op := by cases d <;> rfl
    exact congrArg₂ D.bind hop (funext ih)

theorem eval_mono {M N : Model D S} (h : M ⟶ N) (p : Program S A) :
    (D.order A).le (M.eval p) (N.eval p) := by
  induction p with
  | ret value => exact @le_refl _ (D.order A) (D.pure value)
  | @call d op next ih =>
    apply D.bind_mono _ ih
    cases d with
    | primitive p => exact @le_refl _ (D.order p.Reply) (D.primitive p)
    | external s => exact h.down op

theorem sentence_translate_id (e : Sentence S) : e.translate (𝟙 S) = e := by
  cases e
  simp only [Sentence.translate, program_translate_id]

theorem sentence_translate_comp (f : S ⟶ T) (g : T ⟶ U) (e : Sentence S) :
    e.translate (f ≫ g) = (e.translate f).translate g := by
  cases e
  simp only [Sentence.translate, program_translate_comp]

theorem satisfaction (f : S ⟶ T) (M : Model D T) (e : Sentence S) :
    (e.translate f).Satisfies M ↔ e.Satisfies (M.reduct f) := by
  simp only [Sentence.Satisfies, Sentence.translate, eval_translate]
  rfl

end Silmaril.Proofs.Logic.BrookesSC
