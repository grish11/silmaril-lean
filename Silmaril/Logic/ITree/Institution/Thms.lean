module

public import Silmaril.Logic.ITree.Institution.Defs
import Silmaril.Proofs.Logic.ITree.Institution.Laws

@[expose] public section

namespace Silmaril.Logic.ITree

open CategoryTheory Silmaril.Elgot.ITree Opposite

universe u v w

variable {S T U : Signature.{u}} {E : Type u → Type u} {A : Type v} {X : Type w}

@[simp] theorem Model.reduct_id (M : Model.{u,w} S) : M.reduct (𝟙 S) = M :=
  Proofs.reduct_id M

theorem Model.reduct_comp (f : S ⟶ T) (g : T ⟶ U) (M : Model.{u,w} U) :
    M.reduct (f ≫ g) = (M.reduct g).reduct f :=
  Proofs.reduct_comp f g M

@[simp] theorem Model.renameState_refl (M : Model.{u,w} S) :
    M.renameState (Equiv.refl M.State) = M := rfl

theorem Model.renameState_trans (M : Model.{u,w} S) (e : M.State ≃ X) {Y : Type w} (d : X ≃ Y) :
    (M.renameState e).renameState d = M.renameState (e.trans d) := rfl

theorem Model.reduct_renameState (f : S ⟶ T) (M : Model.{u,w} T) (e : M.State ≃ X) :
    (M.renameState e).reduct f = (M.reduct f).renameState e := rfl

@[simp] theorem Sentence.translate_id (φ : Sentence.{u,v} S) : φ.translate (𝟙 S) = φ := by
  cases φ
  simp [Sentence.translate]

theorem Sentence.translate_comp (f : S ⟶ T) (g : T ⟶ U) (φ : Sentence.{u,v} S) :
    φ.translate (f ≫ g) = (φ.translate f).translate g :=
  congrArg (fun t => Sentence.mk φ.Result t φ.post) (Signature.Hom.tree_comp f g id id φ.program)

@[simp] theorem runs_ret (step : Handler X E) (x : X) (a b : A) :
    Runs step a 0 x (ret b) ↔ b = a :=
  Proofs.runs_ret step x a b

@[simp] theorem runs_vis (step : Handler X E) {R : Type u} (ev : E R)
    (k : R → Tree E A) (x : X) (n : Nat) (a : A) :
    Runs step a (n + 1) x (vis ev k) ↔ ∃ r y, step ⟨R, ev⟩ x r y ∧ Runs step a n y (k r) :=
  Proofs.runs_vis step ⟨R, ev⟩ k x n a

@[simp] theorem runs_vis_zero (step : Handler X E) {R : Type u} (ev : E R)
    (k : R → Tree E A) (x : X) (a : A) : ¬ Runs step a 0 x (vis ev k) := by
  simp [Runs, Part.eq_some_iff, Part.mem_some_iff]

@[simp] theorem runs_ret_succ (step : Handler X E) (x : X) (a b : A) (n : Nat) :
    ¬ Runs step a (n + 1) x (ret b) := by
  simp [Runs, Part.mem_some_iff]

theorem runs_iff_handledTrace (step : Handler X E) (n : Nat) (x : X)
    (t : Tree E A) (a : A) :
    Runs step a n x t ↔ ∃ p, TraceReturns a n p ∧ HandledTrace step x t p :=
  Proofs.runs_iff_handledTrace step n x t a

theorem runs_translate (f : S ⟶ T) (step : Handler X T.Event) (n : Nat)
    (x : X) (t : Tree S.Event A) (a : A) :
    Runs step a n x (f.tree id t) ↔ Runs (f.restrict step) a n x t :=
  Proofs.runs_translate f step n x t a

theorem sat_renameState (M : Model.{u,w} S) (e : M.State ≃ X) (φ : Sentence.{u,v} S) :
    Sat (M.renameState e) φ ↔ Sat M φ :=
  Proofs.sat_renameState M e φ

/-- Satisfaction commutes with each typed request/reply morphism. -/
theorem satisfaction (f : S ⟶ T) (M : Model.{u,w} T) (φ : Sentence.{u,v} S) :
    Sat M (φ.translate f) ↔ Sat (M.reduct f) φ := by
  simp only [Sat, Model.reduct, Sentence.translate, runs_translate]

/-- The covariant sentence functor. -/
def sentences : Signature.{u} ⥤ Type (max (u + 1) (v + 1)) where
  obj := Sentence.{u,v}
  map f := TypeCat.ofHom (Sentence.translate f)
  map_id _ := congrArg TypeCat.ofHom (funext Sentence.translate_id)
  map_comp f g := congrArg TypeCat.ofHom (funext (Sentence.translate_comp f g))

/-- The contravariant model functor. Its fibers have equality arrows only. -/
def models : Signature.{u}ᵒᵖ ⥤ Cat.{max (u + 1) (w + 1), max (u + 1) (w + 1)} where
  obj S := Cat.of (Discrete (Model.{u,w} S.unop))
  map f := Cat.Hom.ofFunctor (Discrete.functor fun M => Discrete.mk (M.reduct f.unop))
  map_id _ := Cat.Hom.ext (Functor.ext fun ⟨M⟩ => congrArg Discrete.mk (Model.reduct_id M))
  map_comp f g := Cat.Hom.ext (Functor.ext fun ⟨M⟩ =>
    congrArg Discrete.mk (Model.reduct_comp g.unop f.unop M))

/-- The classic institution of universally quantified finite return laws. -/
def institution : Silmaril.Logic.Institution.ClassicInstitution.{u + 1, u + 1,
    max (u + 1) (v + 1), max (u + 1) (w + 1), max (u + 1) (w + 1)} Signature.{u} where
  Sen := sentences.{u,v}
  Mod := models.{u,w}
  Sat _ M := Sat M.as
  satisfaction f M := satisfaction f M.as

end Silmaril.Logic.ITree
