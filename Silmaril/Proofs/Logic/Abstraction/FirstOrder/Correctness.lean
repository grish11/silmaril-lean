module

public import Silmaril.Logic.Abstraction.FirstOrder.Defs

public section

namespace Silmaril.Proofs.Logic.Abstraction.FirstOrder

open CategoryTheory
open Silmaril.Inst (Disc)
open Silmaril.Logic.Abstraction
open Silmaril.Logic.Abstraction.FirstOrder
open Silmaril.Logic.Institution.Examples

variable {S T : UFOL.Signature} {k l : Nat}

private theorem eval_ordinary {n : Nat} (M : UFOL.Structure S) (ν : Valuation (M.carrier ⊕ Bool))
    (env : Fin l → M.carrier ⊕ Bool) (a : Symbol S (Shape.ordinary n))
    (args : Fin n → Term (signature S) l) :
    (ordinary a args).eval (algebra M) ν env =
      (algebra M).op a (fun j _ => (args j).eval (algebra M) ν env) := by
  change (algebra M).op a _ = _
  congr 1
  funext j xs
  congr 1
  funext i
  exact Fin.addCases_left i

theorem eval_term (M : UFOL.Structure S) (ν : Valuation (M.carrier ⊕ Bool))
    (scope : Fin k → Fin l) (env : Fin l → M.carrier ⊕ Bool) (ρ : Fin k → M.carrier)
    (h : ∀ i, env (scope i) = .inl (ρ i)) (t : UFOL.Term S k) :
    (term scope t).eval (algebra M) ν env = .inl (t.eval M ρ) := by
  induction t with
  | var i => exact h i
  | app o args ih =>
    rw [term, eval_ordinary]
    change Sum.inl (M.op o (fun j => object (Classical.choice M.nonempty)
      ((term scope (args j)).eval (algebra M) ν env))) = Sum.inl (M.op o _)
    simp only [ih, object]

private theorem classifiesTrue_truthValue {D : Type} (p : Prop) :
    classifiesTrue (truthValue (D := D) p) ↔ p := by
  simpa only [FirstOrder.classifiesTrue, truthValue, Sum.inr.injEq] using
    (@decide_eq_true_iff p (Classical.propDecidable p))

theorem holds_formula (M : UFOL.Structure S) (ν : Valuation (M.carrier ⊕ Bool))
    (scope : Fin k → Fin l) (env : Fin l → M.carrier ⊕ Bool) (ρ : Fin k → M.carrier)
    (h : ∀ i, env (scope i) = .inl (ρ i)) (φ : UFOL.Formula S k) :
    classifiesTrue ((formula scope φ).eval (algebra M) ν env) ↔ φ.Holds M ρ := by
  induction φ generalizing l with
  | eq t u =>
    rw [formula, eval_ordinary]
    change classifiesTrue (truthValue (D := M.carrier)
      ((term scope t).eval (algebra M) ν env = (term scope u).eval (algebra M) ν env)) ↔ _
    simp only [classifiesTrue_truthValue, eval_term M ν scope env ρ h, UFOL.Formula.Holds]
    exact ⟨Sum.inl.inj, congrArg Sum.inl⟩
  | rel r args =>
    rw [formula, eval_ordinary]
    change classifiesTrue (truthValue (D := M.carrier) (M.rel r (fun j => object (Classical.choice M.nonempty)
      ((term scope (args j)).eval (algebra M) ν env)))) ↔ _
    simp only [classifiesTrue_truthValue, eval_term M ν scope env ρ h, object, UFOL.Formula.Holds]
  | tt =>
    change Sum.inr true = (Sum.inr true : M.carrier ⊕ Bool) ↔ True
    simp
  | not φ ih =>
    rw [formula, eval_ordinary]
    change classifiesTrue (truthValue (D := M.carrier)
      (¬ classifiesTrue ((formula scope φ).eval (algebra M) ν env))) ↔ ¬ φ.Holds M ρ
    rw [classifiesTrue_truthValue, ih scope env ρ h]
  | and φ ψ ihφ ihψ =>
    rw [formula, eval_ordinary]
    change classifiesTrue (truthValue (D := M.carrier)
      (classifiesTrue ((formula scope φ).eval (algebra M) ν env) ∧
        classifiesTrue ((formula scope ψ).eval (algebra M) ν env))) ↔ φ.Holds M ρ ∧ ψ.Holds M ρ
    rw [classifiesTrue_truthValue, ihφ scope env ρ h, ihψ scope env ρ h]
  | all φ ih =>
    change classifiesTrue (truthValue (D := M.carrier) (∀ x : M.carrier,
      classifiesTrue ((formula (underBinder scope) φ).eval (algebra M) ν
        (Fin.addCases env (fun _ : Fin 1 => .inl x))))) ↔ ∀ x, φ.Holds M (Fin.cons x ρ)
    rw [classifiesTrue_truthValue]
    refine forall_congr' fun x => ih _ _ _ ?_
    let values : Fin 1 → M.carrier ⊕ Bool := fun _ => .inl x
    intro i
    let assignment : Fin (_ + 1) → M.carrier := Fin.cons x ρ
    change Fin.addCases env values (underBinder scope i) = (Sum.inl (assignment i) : M.carrier ⊕ Bool)
    induction i using Fin.cases with
    | zero => exact Fin.addCases_right (0 : Fin 1)
    | succ j =>
      change Fin.addCases env values (Fin.castAdd 1 (scope j)) = (Sum.inl (ρ j) : M.carrier ⊕ Bool)
      rw [Fin.addCases_left, h]

theorem sat_sentence (M : UFOL.Structure S) (φ : UFOL.Sentence S) :
    (model M).Sat (sentence φ) ↔ UFOL.Sentence.Holds M φ := by
  have holds (ν : Valuation (M.carrier ⊕ Bool)) :=
    holds_formula M ν id Fin.elim0 Fin.elim0 (fun i => i.elim0) φ
  constructor
  · intro h
    let ν : Valuation (M.carrier ⊕ Bool) := fun _ _ _ => .inr true
    exact (holds ν).mp (h ν (Set.mem_univ _) True (by simp [sentence, Rule.formula]) trivial)
  · intro h ν _ b _ hb
    exact (holds ν).mpr h

theorem term_map (f : S ⟶ T) (scope : Fin k → Fin l) (t : UFOL.Term S k) :
    term scope (t.map f) = (term scope t).map (signatureFunctor.map f) := by
  induction t with
  | var i => rfl
  | app o args ih =>
    change ordinary (.op (f.ops o)) _ = ordinary (.op (f.ops o)) _
    exact congrArg (ordinary (.op (f.ops o))) (funext ih)

theorem formula_map (f : S ⟶ T) (scope : Fin k → Fin l) (φ : UFOL.Formula S k) :
    formula scope (φ.map f) = (formula scope φ).map (signatureFunctor.map f) := by
  induction φ generalizing l with
  | eq t u =>
    change ordinary (.eq : Symbol T _) _ = ordinary .eq _
    congr 1
    funext j
    induction j using Fin.cases with
    | zero => exact term_map f scope t
    | succ j =>
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact term_map f scope u
  | rel r args =>
    change ordinary (.rel (f.rels r)) _ = ordinary (.rel (f.rels r)) _
    exact congrArg (ordinary (.rel (f.rels r))) (funext fun j => term_map f scope (args j))
  | tt =>
    change ordinary (.tt : Symbol T _) _ = ordinary .tt _
    exact congrArg (ordinary .tt) (funext fun i => i.elim0)
  | not φ ih =>
    change ordinary (.not : Symbol T _) _ = ordinary .not _
    congr 1
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ih scope
  | and φ ψ ihφ ihψ =>
    change ordinary (.and : Symbol T _) _ = ordinary .and _
    congr 1
    funext j
    induction j using Fin.cases with
    | zero => exact ihφ scope
    | succ j =>
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact ihψ scope
  | all φ ih =>
    change Term.app (S := signature T) (.all : Symbol T _) _ =
      Term.app (S := signature T) (.all : Symbol T _) _
    exact congrArg (Term.app (S := signature T) (.all : Symbol T universalShape)) (funext fun _ => ih _)

theorem model_reduct (f : S ⟶ T) (M : UFOL.Structure T) :
    (model M).reduct (signatureFunctor.map f) = model ((UFOL.Structure.reduct f).obj M) := by
  have hop : (fun {s} (a : Symbol S s) => (algebra M).op (symbolMap f a)) =
      (fun {s} (a : Symbol S s) => (algebra ((UFOL.Structure.reduct f).obj M)).op a) := by
    funext s a args
    cases a <;> rfl
  let build (op : ∀ {s : Shape}, Symbol S s →
      ((i : Fin s.arity) → Operation (M.carrier ⊕ Bool) (s.binders i)) → M.carrier ⊕ Bool) :
      Model (signature S) :=
    let A : Algebra (signature S) := ⟨M.carrier ⊕ Bool, ⟨.inr true⟩, op⟩
    ⟨A, (model M).truth, ValuationSpace.full A⟩
  exact congrArg build hop

theorem toUFOLModels_natural (f : S ⟶ T) :
    toUFOLModels T ⋙ UFOL.Structure.reduct f =
      Disc.functor (UFOL.Structure.reduct f).obj ⋙ toUFOLModels S := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M N h
  have e := h.down
  cases e
  have : h = 𝟙 M := Subsingleton.elim _ _
  subst h
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  let M' := (UFOL.Structure.reduct f).obj M
  change 𝟙 M' = eqToHom (rfl : M' = M') ≫ eqToHom (rfl : M' = M')
  simp

end Silmaril.Proofs.Logic.Abstraction.FirstOrder
