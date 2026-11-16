module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Predicates.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Predicates
open CategoryTheory

variable {scope : Kore.Modules.Scope} {objects : Names} {sort : String}

/-- Leaf adequacy reuses the proved original raw interpreter theorem. -/
theorem Value.denote_lower (p : Value scope objects sort)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (v : Env M objects) :
    p.lower.denote (expand M) v (fun i => i.elim0) = p.denote M v := by
  rw [Value.lower, Matching.GeneralFixedPoint.Pattern.denote_map]
  change p.typed.denote M v (fun i => i.elim0) = _
  unfold Value.denote
  have h := Semantics.elaborate_sound M p.fuel [] objects sort p.raw p.typed
    v (fun i => i.elim0) p.accepted
  simpa only [Semantics.interpret, FixedPoint.Semantics.interpret, Option.getD_some] using
    (congrArg (fun z => z.getD ∅) h).symm

/-- Ordinary relational homomorphisms extend to actual canonical native models;
universal definedness graphs impose no additional map condition. -/
def expansionFunctor (scope : Kore.Modules.Scope) :
    Matching.GeneralFixedPoint.Model scope.signature ⥤
      Matching.GeneralFixedPoint.Model (signature scope) where
  obj := expand
  map f := ⟨f.map, by
    intro n inputs output op args result h
    cases op with
    | source op => exact f.operation op args result h
    | ceil input output => exact Set.mem_univ _⟩
  map_id _ := Matching.FirstOrder.Model.Hom.ext _ _ rfl
  map_comp _ _ := Matching.FirstOrder.Model.Hom.ext _ _ rfl

theorem Value.denote_typed (p : Value scope objects sort)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (v : Env M objects) :
    p.denote M v = p.typed.denote M v (fun i => i.elim0) := by
  rw [← p.denote_lower, Value.lower, Matching.GeneralFixedPoint.Pattern.denote_map]
  rfl

theorem ceiling_denote (M : Matching.GeneralFixedPoint.Model scope.signature)
    {input : String} (output : String) (p : NativePattern scope objects input)
    (v : Env M objects) (x : M.carrier output) :
    x ∈ (ceiling output p).denote (expand M) v (fun i => i.elim0) ↔
      (p.denote (expand M) v (fun i => i.elim0)).Nonempty := by
  constructor
  · rintro ⟨args, hargs, _⟩
    exact ⟨args 0, hargs 0⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, fun _ => ha, Set.mem_univ _⟩

theorem equal_denote (M : Matching.GeneralFixedPoint.Model scope.signature)
    {input : String} (output : String) (p q : NativePattern scope objects input)
    (v : Env M objects) (x : M.carrier output) :
    x ∈ (equal output p q).denote (expand M) v (fun i => i.elim0) ↔
      p.denote (expand M) v (fun i => i.elim0) =
        q.denote (expand M) v (fun i => i.elim0) := by
  classical
  unfold equal
  rw [Matching.GeneralFixedPoint.Pattern.denote]
  change (¬ x ∈ (ceiling output ((Matching.GeneralFixedPoint.Pattern.conj p (.neg q)).disj (.conj (.neg p) q))).denote (expand M) v (fun i => i.elim0)) ↔ _
  rw [ceiling_denote]
  simp only [Matching.GeneralFixedPoint.Pattern.disj, Matching.GeneralFixedPoint.Pattern.denote,
    Set.compl_inter, compl_compl, Set.nonempty_def, Set.mem_union,
    Set.mem_compl_iff, not_exists]
  constructor
  · intro h
    ext a
    specialize h a
    tauto
  · intro h a
    have same := Set.ext_iff.mp h a
    tauto

/-- Every output point of every actual result carrier has exactly the independent
source truth value. This is uniform, not a finite specialization of a scheme. -/
theorem Predicate.lower_adequate (p : Predicate scope objects)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (result : String)
    (v : Env M objects) (x : M.carrier result) :
    x ∈ (p.lower result).denote (expand M) v (fun i => i.elim0) ↔ p.truth M v := by
  induction p with
  | top =>
      change x ∈ (expand M).denote v Matching.FirstOrder.Pattern.top ↔ True
      rw [Matching.FirstOrder.Model.denote_top]
      rfl
  | bottom =>
      change x ∈ (expand M).denote v Matching.FirstOrder.Pattern.bottom ↔ False
      rw [Matching.FirstOrder.Model.denote_bottom]
      rfl
  | equal s p q =>
      exact (equal_denote M result p.lower q.lower v x).trans
        (by rw [p.denote_lower, q.denote_lower]; rfl)
  | member s p q =>
      rw [Predicate.lower, Predicates.member, ceiling_denote]
      change (p.lower.denote (expand M) v (fun i => i.elim0) ∩
        q.lower.denote (expand M) v (fun i => i.elim0)).Nonempty ↔ _
      rw [p.denote_lower, q.denote_lower]
      rfl
  | neg p ih => exact not_congr (ih v)
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | disj p q hp hq =>
      exact (not_congr (and_congr (not_congr (hp v)) (not_congr (hq v)))).trans
        (by simp only [Predicate.truth]; tauto)
  | ex name bound p ih =>
      apply exists_congr
      intro a
      exact ih (Fin.cases a v)

theorem Value.lower_admitted (p : Value scope objects sort) :
    p.lower.admissible = true := by
  rw [Value.lower, Matching.GeneralFixedPoint.Pattern.admissible_map]
  exact p.admitted

theorem Predicate.lower_admitted (p : Predicate scope objects) (result : String) :
    (p.lower result).admissible = true := by
  induction p with
  | top | bottom => rfl
  | equal s p q =>
      change (p.lower.admissible && q.lower.admissible &&
        (p.lower.admissible && q.lower.admissible)) && true = true
      rw [p.lower_admitted, q.lower_admitted]
      rfl
  | member s p q =>
      change ((p.lower.admissible && q.lower.admissible) && true) = true
      rw [p.lower_admitted, q.lower_admitted]
      rfl
  | neg p ih => exact ih
  | conj p q hp hq =>
      change ((p.lower result).admissible && (q.lower result).admissible) = true
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      change ((p.lower result).admissible && (q.lower result).admissible) = true
      rw [hp, hq]
      rfl
  | ex name bound p ih => exact ih

theorem Predicate.satisfies_iff (p : Predicate scope objects)
    (M : Matching.GeneralFixedPoint.Model scope.signature) :
    p.Satisfies M ↔ ∀ v, p.truth M v := by
  constructor
  · intro h v
    exact h Unit v ()
  · intro h Result _ v x
    exact h v

end Silmaril.Logic.Kore.GeneralFixedPoint.Predicates
