module

public import Silmaril.Logic.Smt.Uflia.Models.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia
open CategoryTheory

variable {U : Type} {A B C : Signature U} {M N : Model A}

@[simp] theorem Model.reductFunctor_id (A : Signature U) :
    Model.reductFunctor (𝟙 A) = 𝟭 (Model A) := rfl

@[simp] theorem Model.reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    Model.reductFunctor (f ≫ g) = Model.reductFunctor g ⋙ Model.reductFunctor f := rfl

@[simp] theorem EmbeddingModel.reduct_id (A : Signature U) :
    EmbeddingModel.reduct (𝟙 A) = 𝟭 (EmbeddingModel A) := rfl

@[simp] theorem EmbeddingModel.reduct_comp (f : A ⟶ B) (g : B ⟶ C) :
    EmbeddingModel.reduct (f ≫ g) = EmbeddingModel.reduct g ⋙ EmbeddingModel.reduct f := rfl

/-- The inclusion retains the actual maps, not just their existence. -/
theorem EmbeddingModel.forget_faithful (A : Signature U) :
    (EmbeddingModel.forget A).Faithful :=
  ⟨fun h => Model.Embedding.ext _ _ h⟩

/-- Forgetting injectivity commutes with changing the UF signature, on arrows too. -/
theorem EmbeddingModel.forget_reduct (f : A ⟶ B) :
    EmbeddingModel.reduct f ⋙ EmbeddingModel.forget A =
      EmbeddingModel.forget B ⋙ Model.reductFunctor f := rfl

/-- Injectivity is exactly what makes the standard equality operation commute
with a carrier map. All other interpreted operations need no extra premise. -/
theorem Model.Embedding.apply (h : Model.Embedding M N) {n inputs output}
    (op : Operation A n inputs output)
    (args : (i : Fin n) → M.carriers.value (inputs i)) :
    h.toHom.value output (M.apply op args) =
      N.apply op (fun i => h.toHom.value (inputs i) (args i)) := by
  classical
  cases op with
  | uf symbol => exact h.operation symbol args
  | boolean _ => rfl
  | integer _ => rfl
  | add => rfl
  | sub => rfl
  | scale _ => rfl
  | le => rfl
  | lt => rfl
  | not => rfl
  | and => rfl
  | or => rfl
  | eq sort =>
      have injective := Carriers.mapValue_injective h.user h.injective sort
      change decide (args 0 = args 1) =
        decide (Carriers.mapValue h.user sort (args 0) =
          Carriers.mapValue h.user sort (args 1))
      simp only [injective.eq_iff]
  | ite _ =>
      change h.toHom.value _ (if args 0 = true then args 1 else args 2) =
        if args 0 = true then h.toHom.value _ (args 1) else h.toHom.value _ (args 2)
      exact apply_ite _ _ _ _

/-- Every ground term commutes with an embedding, including Boolean UF
arguments, equality on user sorts, and conditionals with user-sort results. -/
theorem Model.Embedding.eval (h : Model.Embedding M N) {s : SortCode U}
    (t : Term A s) : h.toHom.value s (M.eval t) = N.eval t := by
  induction t with
  | var i => exact Fin.elim0 i
  | app op args ih =>
      change h.toHom.value _ (M.apply op (fun i => M.eval (args i))) =
        N.apply op (fun i => N.eval (args i))
      rw [h.apply]
      congr 1
      funext i
      exact ih i

/-- Bool is fixed, so embeddings preserve and reflect every ground assertion. -/
theorem Model.Embedding.holds (h : Model.Embedding M N) (φ : Formula A) :
    M.Holds φ ↔ N.Holds φ := by
  have same : M.eval φ = N.eval φ := h.eval φ
  exact congrArg (fun b => b = true) same |>.to_iff

theorem Model.Embedding.problem_holds (h : Model.Embedding M N) (Γ : Problem A) :
    Γ.Holds M ↔ Γ.Holds N := by
  exact forall_congr' fun φ => forall_congr' fun _ => h.holds φ

end Silmaril.Logic.Smt.Uflia
