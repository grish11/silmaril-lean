module

public import Silmaril.Logic.Separation.Parameterized.Transport.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized
open CategoryTheory Silmaril.Logic.Institution
variable {A B C : Signature}

@[simp] theorem Term.map_id {k} (p : Term A k) : p.map (𝟙 A) = p := by
  induction p with
  | var i => rfl
  | app op args ih => exact congrArg (Term.app op) (funext ih)

@[simp] theorem Term.map_comp (f : A ⟶ B) (g : B ⟶ C) {k} (p : Term A k) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | var i => rfl
  | app op args ih => exact congrArg (Term.app _) (funext ih)

theorem Term.eval_map (f : A ⟶ B) (M : Model B) {k} (p : Term A k) (ρ : Tuple M k) :
    (p.map f).eval M ρ = p.eval (reduct f M) ρ := by
  induction p with
  | var i => rfl
  | app op args ih => exact congrArg (M.operation (f.operation op)) (funext ih)

@[simp] theorem Assertion.map_id {k} (p : Assertion A k) : p.map (𝟙 A) = p := by
  induction p with
  | eq t u => simp only [map,Term.map_id]
  | atom a args => exact congrArg (Assertion.atom a) (funext fun i => (args i).map_id)
  | emp => rfl
  | neg p ih => exact congrArg Assertion.neg ih
  | conj p q hp hq => exact congrArg₂ Assertion.conj hp hq
  | sep p q hp hq => exact congrArg₂ Assertion.sep hp hq
  | wand p q hp hq => exact congrArg₂ Assertion.wand hp hq

@[simp] theorem Assertion.map_comp (f : A ⟶ B) (g : B ⟶ C) {k} (p : Assertion A k) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | eq t u => simp only [map,Term.map_comp]
  | atom a args => exact congrArg (Assertion.atom _) (funext fun i => (args i).map_comp f g)
  | emp => rfl
  | neg p ih => exact congrArg Assertion.neg ih
  | conj p q hp hq => exact congrArg₂ Assertion.conj hp hq
  | sep p q hp hq => exact congrArg₂ Assertion.sep hp hq
  | wand p q hp hq => exact congrArg₂ Assertion.wand hp hq

theorem Assertion.denote_map (f : A ⟶ B) (M : Model B) {k} (p : Assertion A k) (ρ : Tuple M k) :
    (p.map f).denote M ρ = p.denote (reduct f M) ρ := by
  induction p with
  | eq t u =>
      simp only [map,denote,Term.eval_map]
  | atom a args => exact congrArg (M.atom (f.atom a)) (funext fun i => (args i).eval_map f M ρ)
  | emp => rfl
  | neg p ih => exact congrArg Set.compl ih
  | conj p q hp hq => exact congrArg₂ Set.inter hp hq
  | sep p q hp hq => exact congrArg₂ M.resource.sep hp hq
  | wand p q hp hq => exact congrArg₂ M.resource.wand hp hq

@[simp] theorem Pattern.map_id {r k} {P : Fin r → Nat} (p : Pattern A P k) :
    p.map (𝟙 A) = p := by
  induction p with
  | base p => exact congrArg Pattern.base p.map_id
  | pred i args => exact congrArg (Pattern.pred i) (funext fun j => (args j).map_id)
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ Pattern.disj hp hq
  | sep p q hp hq => exact congrArg₂ Pattern.sep hp hq
  | wand p q hq => exact congrArg₂ Pattern.wand p.map_id hq
  | ex p ih => exact congrArg Pattern.ex ih
  | all p ih => exact congrArg Pattern.all ih
  | lfp body args ih => exact congrArg₂ Pattern.lfp ih (funext fun j => (args j).map_id)

@[simp] theorem Pattern.map_comp (f : A ⟶ B) (g : B ⟶ C) {r k} {P : Fin r → Nat}
    (p : Pattern A P k) : p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | base p => exact congrArg Pattern.base (p.map_comp f g)
  | pred i args => exact congrArg (Pattern.pred i) (funext fun j => (args j).map_comp f g)
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ Pattern.disj hp hq
  | sep p q hp hq => exact congrArg₂ Pattern.sep hp hq
  | wand p q hq => exact congrArg₂ Pattern.wand (p.map_comp f g) hq
  | ex p ih => exact congrArg Pattern.ex ih
  | all p ih => exact congrArg Pattern.all ih
  | lfp body args ih => exact congrArg₂ Pattern.lfp ih (funext fun j => (args j).map_comp f g)

/-- Exact signature reduct agreement includes captured parameters and the
entire powerset fixed point, not a bounded unfolding. -/
theorem Pattern.denote_map (f : A ⟶ B) (M : Model B) {r k} {P : Fin r → Nat}
    (p : Pattern A P k) (η : RelEnv M P) :
    (p.map f).denote M η = p.denote (reduct f M) η := by
  induction p with
  | base p =>
      ext s
      change s.2 ∈ (p.map f).denote M s.1 ↔ s.2 ∈ p.denote (reduct f M) s.1
      rw [p.denote_map]
  | pred i args =>
      change {s : State M _ | ((fun j => ((args j).map f).eval M s.1),s.2) ∈ η i} = _
      simp only [Term.eval_map]
      rfl
  | conj p q hp hq => exact congrArg₂ Set.inter (hp η) (hq η)
  | disj p q hp hq => exact congrArg₂ Set.union (hp η) (hq η)
  | sep p q hp hq =>
      change {s : State M _ | ∃ a b, _ ∧ (s.1,a) ∈ (p.map f).denote M η ∧
        (s.1,b) ∈ (q.map f).denote M η} = _
      rw [hp η,hq η]
      rfl
  | wand p q hq =>
      change {s : State M _ | ∀ a b, _ → a ∈ (p.map f).denote M s.1 →
        (s.1,b) ∈ (q.map f).denote M η} = _
      simp only [Assertion.denote_map,hq η]
      rfl
  | ex p ih =>
      change {s : State M _ | ∃ x, (consValues M x s.1,s.2) ∈ (p.map f).denote M η} = _
      rw [ih η]
      rfl
  | all p ih =>
      change {s : State M _ | ∀ x, (consValues M x s.1,s.2) ∈ (p.map f).denote M η} = _
      rw [ih η]
      rfl
  | @lfp r k P' body args ih =>
      have hb : ∀ ρ, bodyOperator M (body.map f) η ρ = bodyOperator (reduct f M) body η ρ := by
        intro ρ
        apply OrderHom.ext
        funext X
        change {s : State M (P' 0) | (appendValues M s.1 ρ,s.2) ∈
          (body.map f).denote M (insert M P' η X)} = _
        rw [ih (insert M P' η X)]
        rfl
      ext s
      rcases s with ⟨ρ,h⟩
      change ((fun j => ((args j).map f).eval M ρ),h) ∈ lfpSet M (body.map f) η ρ ↔
        ((fun j => (args j).eval (reduct f M) ρ),h) ∈ lfpSet (reduct f M) body η ρ
      simp only [Term.eval_map,lfpSet,hb]

end Silmaril.Logic.Separation.Parameterized
