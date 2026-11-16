module

public import Silmaril.Logic.Algebraic.Initial.Matching.Presented.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.PresentedCompiler
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization

/-- Constructor trees use the original public term syntax. -/
def ground {D : Constructors} : Tree D → Ground D.signature.public ()
  | .node c args => .app ⟨c, rfl⟩ (fun i => ground (args i))

theorem ground_evaluate {D : Constructors} (M : EQ.Algebra D.signature.public)
    (t : Tree D) : evaluate M (ground t) = fold D M t := by
  induction t with
  | node c args ih =>
    change M.op ⟨c, rfl⟩ (fun i => evaluate M (ground (args i))) =
      M.op ⟨c, rfl⟩ (fun i => fold D M (args i))
    exact congrArg (M.op (w := fun _ => ()) (s := ()) ⟨c, rfl⟩) (funext ih)

/-- This bridge concerns all raw terms, independently of any equations. -/
theorem generated_iff_fold_surjective {D : Constructors}
    (M : EQ.Algebra D.signature.public) :
    Initial.Presented.Characterization.Generated M ↔ Function.Surjective (fold D M) := by
  constructor
  · intro h x
    obtain ⟨t, ht⟩ := h () x
    refine ⟨t.eval (treeAlgebra D) (fun i => i.elim0), ?_⟩
    have he := Initial.Presented.eval_hom (foldHom D M) (fun i => i.elim0) t
    have hv : (fun i : Fin 0 => (foldHom D M).map _ (Fin.elim0 i)) =
        (fun i : Fin 0 => (Fin.elim0 i : M.carrier ((closedContext D.signature.public) i))) :=
      funext fun i => i.elim0
    rw [hv] at he
    exact he.trans ht
  · intro h s x
    cases s
    obtain ⟨t, ht⟩ := h x
    exact ⟨ground t, (ground_evaluate M t).trans ht⟩

theorem bottom_denote {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) {r : Nat}
    (v : FixedPoint.ObjEnv _ N.base (fun _ : Fin 0 => targetSort σ))
    (η : FixedPoint.SetEnv _ N.base (fun _ : Fin r => targetSort σ)) :
    (bottom σ).denote N.base v η = ∅ := by
  ext x
  change ((∃ value, x = value) ∧ ¬ ∃ value, x = value) ↔ False
  simp

theorem disjunction_mem {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) {r : Nat}
    (ps : List (Pat σ r))
    (v : FixedPoint.ObjEnv _ N.base (fun _ : Fin 0 => targetSort σ))
    (η : FixedPoint.SetEnv _ N.base (fun _ : Fin r => targetSort σ))
    (x : N.base.carrier (targetSort σ)) :
    x ∈ (disjunction σ ps).denote N.base v η ↔
      ∃ p ∈ ps, x ∈ p.denote N.base v η := by
  induction ps with
  | nil =>
    rw [disjunction, bottom_denote σ N]
    simp
  | cons p ps ih =>
    change (x ∈ p.denote N.base v η ∨ x ∈ (disjunction σ ps).denote N.base v η) ↔ _
    simp [ih]

/-- No behavior on inactive operation arguments is assumed in this identity. -/
theorem generatedBody_mem {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : Set (N.base.carrier (targetSort σ))) (x : N.base.carrier (targetSort σ)) :
    x ∈ (generatedBody σ).denote N.base (fun i => i.elim0)
      (Fin.cases X (fun i => i.elim0)) ↔
      ∃ (c : Fin D.count) (args : Fin (D.arity c) → N.base.carrier (targetSort σ)),
        (∀ i, args i ∈ X) ∧
          x ∈ N.base.operation
            (.function (σ.ops (w := fun _ => ()) (s := ()) ⟨c, rfl⟩)) args := by
  rw [generatedBody, disjunction_mem]
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨args, hargs, hop⟩ := hx
    exact ⟨c, args, hargs, hop⟩
  · rintro ⟨c, args, hargs, hop⟩
    exact ⟨_, List.mem_map.mpr ⟨c, List.mem_finRange c, rfl⟩,
      ⟨args, hargs, hop⟩⟩

/-- The scalar native μ denotes exactly finite evaluations of original symbols.
All tuples used in the proof are active, so raw inactive graph behavior is irrelevant. -/
theorem generated_denote {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :
    (generated σ).denote N.base (fun i => i.elim0) (fun i => i.elim0) =
      Set.range (fun t => (fold D (reduct σ N) t).val) := by
  apply Set.Subset.antisymm
  · apply FixedPoint.mu_induction
    intro x hx
    obtain ⟨c, args, hargs, hop⟩ := (generatedBody_mem σ N _ x).mp hx
    choose trees htrees using hargs
    have he : args = fun i => (fold D (reduct σ N) (trees i)).val :=
      funext fun i => (htrees i).symm
    subst args
    rw [GuardedFOL.function_graph N _ (fun i => fold D (reduct σ N) (trees i))] at hop
    exact ⟨.node c trees, hop.symm⟩
  · rintro x ⟨t, rfl⟩
    induction t with
    | node c args ih =>
      apply Eq.mpr (congrArg
        (fun X => (fold D (reduct σ N) (.node c args)).val ∈ X)
        (FixedPoint.mu_unfold N.base (generatedBody σ)
          (fun i => i.elim0) (fun i => i.elim0)))
      apply (generatedBody_mem σ N _ _).mpr
      refine ⟨c, (fun i => (fold D (reduct σ N) (args i)).val), ih, ?_⟩
      exact Eq.mpr (congrArg
        (fun X => (fold D (reduct σ N) (.node c args)).val ∈ X)
        (GuardedFOL.function_graph N
          (σ.ops (w := fun _ => ()) (s := ()) ⟨c, rfl⟩)
          (fun i => fold D (reduct σ N) (args i)))) rfl

theorem active_denote {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B)
    (v : FixedPoint.ObjEnv _ N.base (fun _ : Fin 0 => targetSort σ)) :
    N.base.denote v (.app (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0)) =
      N.base.operation (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0) := by
  ext x
  constructor
  · rintro ⟨values, _, hop⟩
    have he : values = (fun i => i.elim0) := funext fun i => i.elim0
    simpa only [he] using hop
  · intro hx
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), hx⟩

theorem generationClause_satisfaction {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :
    (generationClause σ).Satisfies N.base ↔
      Initial.Presented.Characterization.Generated (reduct σ N) := by
  rw [generated_iff_fold_surjective]
  constructor
  · intro h x
    have hx := h (fun i => i.elim0) (fun i => i.elim0) x.val
    change (x.val ∉ N.base.denote (fun i => i.elim0)
      (.app (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0)) ∨
      x.val ∈ (generated σ).denote N.base (fun i => i.elim0) (fun i => i.elim0)) at hx
    rw [active_denote σ N] at hx
    obtain inactive | hx := hx
    · exact (inactive x.property).elim
    · rw [generated_denote] at hx
      obtain ⟨t, ht⟩ := hx
      exact ⟨t, Subtype.ext ht⟩
  · intro h v η x
    have hv : v = (fun i => i.elim0) := funext fun i => i.elim0
    have hη : η = (fun i => i.elim0) := funext fun i => i.elim0
    subst v
    subst η
    change x ∉ N.base.denote (fun i => i.elim0)
      (.app (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0)) ∨
      x ∈ (generated σ).denote N.base (fun i => i.elim0) (fun i => i.elim0)
    rw [active_denote σ N]
    by_cases active : x ∈ N.base.operation (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0)
    · right
      rw [generated_denote]
      obtain ⟨t, ht⟩ := h ⟨x, active⟩
      exact ⟨t, congrArg Subtype.val ht⟩
    · exact Or.inl active

/-- The presentation is never pushed forward or reclosed under ambient collisions. -/
theorem compiled_satisfaction {D : Constructors} (E : Set (Equations D))
    {B : EQ.Signature} (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Satisfies N (compiled E σ) ↔
      Initial.Presented.Characterization.Generated (reduct σ N) ∧
        ExactGroundKernel (theory D E) (reduct σ N) := by
  constructor
  · intro h
    refine ⟨(generationClause_satisfaction σ N).mp (h _ (Or.inl rfl)), ?_⟩
    apply (SignedSpectrum.satisfies_iff_exactGroundKernel (T := theory D E) σ N).mp
    intro q hq
    exact (FixedPoint.firstOrder_satisfies N.base q).mp
      (h _ (Or.inr ⟨q, hq, rfl⟩))
  · rintro ⟨hg, hk⟩ q (hq | hq)
    · obtain rfl := hq
      exact (generationClause_satisfaction σ N).mpr hg
    · obtain ⟨p, hp, rfl⟩ := hq
      exact (FixedPoint.firstOrder_satisfies N.base p).mpr
        ((SignedSpectrum.satisfies_iff_exactGroundKernel (T := theory D E) σ N).mpr hk p hp)

/-- Native theory satisfaction gives modelhood and actual initiality for arbitrary
original equations, without assuming either property in the target model. -/
theorem compiled_initial_iff {D : Constructors} (E : Set (Equations D))
    {B : EQ.Signature} (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Satisfies N (compiled E σ) ↔
      (∃ h : ∀ e ∈ (theory D E).axioms, e.down.Holds (reduct σ N),
        Nonempty (IsInitial (⟨reduct σ N, h⟩ : Initial.Models (theory D E)))) :=
  (compiled_satisfaction E σ N).trans
    (Initial.Presented.Characterization.modelhood_initial_iff (T := theory D E) (reduct σ N)).symm

theorem initialConstraint_iff_modelhood_initial (T : Initial.Theory)
    (M : EQ.Algebra T.sig) :
    Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational M
      (Initial.initialConstraint T) ↔
      (∃ h : ∀ e ∈ T.axioms, e.down.Holds M,
        Nonempty (IsInitial (⟨M, h⟩ : Initial.Models T))) := by
  constructor
  · intro h
    have hs := h
    unfold Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.initialConstraint at hs
    rw [Initial.equational.map_id] at hs
    obtain ⟨modelhood, _⟩ := hs
    exact ⟨modelhood, (Initial.initialConstraint_sat_iff T ⟨M, modelhood⟩).mp h⟩
  · rintro ⟨modelhood, h⟩
    exact (Initial.initialConstraint_sat_iff T ⟨M, modelhood⟩).mpr h

/-- The native theory checks the existing translated freeness constraint. -/
theorem compiled_actual_iff {D : Constructors} (E : Set (Equations D))
    {B : EQ.Signature} (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Satisfies N (compiled E σ) ↔
      Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational
        (SignedSpectrum.decode N) (actual E σ) := by
  exact (compiled_initial_iff E σ N).trans
    ((initialConstraint_iff_modelhood_initial (theory D E) (reduct σ N)).symm.trans
      (Silmaril.Logic.Institution.Structured.Constraints.satisfaction Initial.equational σ
        (SignedSpectrum.decode N) (Initial.initialConstraint (theory D E))).symm)

/-- Evaluation in a padded native expansion recovers the original active value. -/
theorem expansion_evaluate {A : EQ.Signature} (M : EQ.Algebra A) {s : A.S}
    (t : Ground A s) :
    GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s
      (evaluate (SignedSpectrum.decode (GuardedFOL.expand (SignedSpectrum.structureOf M))) t) =
        evaluate M t := by
  let f := (GuardedFOL.decodeExpansionIso (SignedSpectrum.structureOf M)).hom.toAlgebraHom
  have h := Initial.Presented.eval_hom f (fun i => i.elim0) t
  have hv : (fun i : Fin 0 => f.map _ (Fin.elim0 i)) =
      (fun i : Fin 0 => (Fin.elim0 i : M.carrier ((closedContext A) i))) :=
    funext fun i => i.elim0
  rw [hv] at h
  exact h

theorem expansion_evaluate_eq_iff {A : EQ.Signature} (M : EQ.Algebra A) {s : A.S}
    (a b : Ground A s) :
    evaluate (SignedSpectrum.decode (GuardedFOL.expand (SignedSpectrum.structureOf M))) a =
        evaluate (SignedSpectrum.decode (GuardedFOL.expand (SignedSpectrum.structureOf M))) b ↔
      evaluate M a = evaluate M b := by
  constructor
  · intro h
    exact (expansion_evaluate M a).symm.trans
      ((congrArg (GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s) h).trans
        (expansion_evaluate M b))
  · intro h
    apply (GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s).injective
    exact (expansion_evaluate M a).trans (h.trans (expansion_evaluate M b).symm)

theorem expansion_generated_iff {A : EQ.Signature} (M : EQ.Algebra A) :
    Initial.Presented.Characterization.Generated
      (SignedSpectrum.decode (GuardedFOL.expand (SignedSpectrum.structureOf M))) ↔
        Initial.Presented.Characterization.Generated M := by
  constructor
  · intro h s x
    obtain ⟨t, ht⟩ := h s ((GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s).symm x)
    refine ⟨t, ?_⟩
    exact (expansion_evaluate M t).symm.trans
      ((congrArg (GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s) ht).trans
        ((GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s).apply_symm_apply x))
  · intro h s x
    obtain ⟨t, ht⟩ := h s (GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s x)
    refine ⟨t, ?_⟩
    apply (GuardedFOL.activeEquiv (SignedSpectrum.structureOf M) s).injective
    exact (expansion_evaluate M t).trans ht

/-- In particular every presented quotient supplies a concrete satisfying native
expansion; this does not require an effective equality algorithm. -/
theorem quotient_expansion_satisfies {D : Constructors} (E : Set (Equations D)) :
    Satisfies
      (GuardedFOL.expand (SignedSpectrum.structureOf (quotientModel (theory D E)).obj))
      (compiled E (𝟙 D.signature.public)) := by
  apply (compiled_satisfaction E (𝟙 D.signature.public) _).mpr
  have properties := generated_kernel_of_initial (quotientModel (theory D E))
    (quotientModel_isInitial (theory D E))
  constructor
  · exact (expansion_generated_iff _).mpr properties.1
  · intro s a b
    exact (expansion_evaluate_eq_iff _ a b).trans (properties.2 s a b)

end Silmaril.Logic.Algebraic.Initial.Matching.PresentedCompiler
