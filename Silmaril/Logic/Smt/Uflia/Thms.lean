module

public import Silmaril.Logic.Smt.Uflia.Defs

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia

open CategoryTheory Silmaril.Inst Silmaril.Logic.Algebraic

variable {U : Type} {A B C : Signature U}

/-- Extend a sort-preserving UF renaming by fixing every built-in operation. -/
def Operation.map (f : A ⟶ B) : {n : Nat} → {inputs : Fin n → SortCode U} →
    {output : SortCode U} → Operation A n inputs output → Operation B n inputs output
  | _, _, _, .uf symbol => .uf (f.operations symbol)
  | _, _, _, .boolean b => .boolean b
  | _, _, _, .integer i => .integer i
  | _, _, _, .add => .add
  | _, _, _, .sub => .sub
  | _, _, _, .scale c => .scale c
  | _, _, _, .le => .le
  | _, _, _, .lt => .lt
  | _, _, _, .eq s => .eq s
  | _, _, _, .not => .not
  | _, _, _, .and => .and
  | _, _, _, .or => .or
  | _, _, _, .ite s => .ite s

def Signature.expandMap (f : A ⟶ B) : A.expanded ⟶ B.expanded :=
  ⟨Operation.map f⟩

theorem Signature.expandMap_id (A : Signature U) :
    Signature.expandMap (𝟙 A) = 𝟙 A.expanded := by
  apply ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op <;> rfl

theorem Signature.expandMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    Signature.expandMap (f ≫ g) = Signature.expandMap f ≫ Signature.expandMap g := by
  apply ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op <;> rfl

/-- Formula/term renaming reuses the existing sorted term map. -/
def Term.map (f : A ⟶ B) {s : SortCode U} (t : Term A s) : Term B s :=
  ManySorted.Term.map (Signature.expandMap f) t

theorem Term.map_id {s : SortCode U} (t : Term A s) : Term.map (𝟙 A) t = t := by
  unfold Term.map
  rw [Signature.expandMap_id]
  exact ManySorted.Term.map_id t

theorem Term.map_comp (f : A ⟶ B) (g : B ⟶ C) {s : SortCode U} (t : Term A s) :
    Term.map (f ≫ g) t = Term.map g (Term.map f t) := by
  unfold Term.map
  rw [Signature.expandMap_comp]
  exact ManySorted.Term.map_comp (Signature.expandMap f) (Signature.expandMap g) t

/-- Restrict a model to the source's uninterpreted symbols. -/
def Model.reduct (f : A ⟶ B) (M : Model B) : Model A :=
  ⟨M.carriers, fun symbol args => M.operation (f.operations symbol) args⟩

theorem Model.reduct_id (M : Model A) : M.reduct (𝟙 A) = M := by
  cases M
  rfl

theorem Model.reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    M.reduct (f ≫ g) = (M.reduct g).reduct f := rfl

theorem Model.apply_map (f : A ⟶ B) (M : Model B)
    {n inputs output} (op : Operation A n inputs output)
    (args : (i : Fin n) → M.carriers.value (inputs i)) :
    M.apply (Operation.map f op) args = (M.reduct f).apply op args := by
  cases op <;> rfl

/-- Evaluation is invariant under renaming and reduct. -/
theorem Model.eval_map (f : A ⟶ B) (M : Model B) {s : SortCode U} (t : Term A s) :
    M.eval (Term.map f t) = (M.reduct f).eval t := by
  induction t with
  | var i => exact Fin.elim0 i
  | app op args ih =>
    change M.apply (Operation.map f op) (fun i => M.eval (Term.map f (args i))) =
      (M.reduct f).apply op (fun i => (M.reduct f).eval (args i))
    rw [Model.apply_map]
    congr 1
    funext i
    exact ih i

/-- The satisfaction condition for the fixed-sort QF-UFLIA presentation. -/
theorem Model.holds_map (f : A ⟶ B) (M : Model B) (φ : Formula A) :
    M.Holds (Term.map f φ) ↔ (M.reduct f).Holds φ := by
  simp only [Model.Holds, Model.eval_map]

theorem Problem.unsat_iff (Γ : Problem A) : Γ.Unsat ↔ ∀ M, ¬ Γ.Holds M := by
  simp only [Problem.Unsat, Problem.Sat, not_exists]

theorem Problem.empty_sat (A : Signature U) : Problem.Sat ([] : Problem A) := by
  refine ⟨Model.trivial A, ?_⟩
  intro φ h
  cases h

theorem Model.holds_boolean (M : Model A) (b : Bool) :
    M.Holds (Term.boolean b) ↔ b = true := Iff.rfl

theorem Problem.false_unsat (A : Signature U) :
    Problem.Unsat ([Term.boolean false] : Problem A) := by
  intro ⟨M, h⟩
  have hf := h (Term.boolean false) (List.mem_cons_self)
  exact Bool.noConfusion hf

/-- The genuine abstract institution: signatures vary their UF symbols, while
the sort family and interpreted arithmetic core remain fixed. Model morphisms
are discrete; this does not assert a category of general model homomorphisms. -/
noncomputable def plain (U : Type) : Plain (Signature U) where
  Sen := Formula
  map f φ := Term.map f φ
  map_id _ := Term.map_id
  map_comp f g φ := Term.map_comp f g φ
  Mod := Model
  reduct := Model.reduct
  reduct_id _ := Model.reduct_id
  reduct_comp := Model.reduct_comp
  Sat := Model.Holds
  sat_map f M φ := Model.holds_map f M φ

noncomputable abbrev institution (U : Type) := (plain U).toInst

noncomputable abbrev room (A : Signature U) := (plain U).room A

end Silmaril.Logic.Smt.Uflia
