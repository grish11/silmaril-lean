module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization
open FixedPoint.Simultaneous

private theorem cast_symm {S : Type} (D : S → Type) {s t : S}
    (h : s = t) (x : D t) : (h ▸ (h.symm ▸ x : D s) : D t) = x := by
  cases h
  rfl

theorem operationsAt_mem (D : Profile) (i : Fin D.sortCount)
    (c : {c : Fin D.operationCount // D.output c = i}) :
    c ∈ operationsAt D i := by
  apply List.mem_filterMap.mpr
  exact ⟨c.val, List.mem_finRange c.val, by simp [c.property]⟩

theorem recursionVariable_denote {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : RawFamily σ N) (i : Fin D.sortCount) :
    (recursionVariable σ i).denote N.base (fun j => j.elim0)
      (joinEnv N.base (fun j => j.elim0) X) = X i := by
  simp only [recursionVariable, id_eq]
  rw [FixedPoint.denote_setvar_cast]
  simpa only [joinEnv, Fin.addCases_left] using
    (cast_symm (fun s => Set (N.base.carrier s))
      (append_left (coordinate σ) (emptyContext (B := B)) i) (X i))

theorem bottom_denote {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : RawFamily σ N) (i : Fin D.sortCount) :
    (bottom σ i).denote N.base (fun j => j.elim0)
      (joinEnv N.base (fun j => j.elim0) X) = ∅ := by
  ext x
  change ((∃ value, x = value) ∧ ¬ ∃ value, x = value) ↔ False
  simp

theorem disjunction_mem {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : RawFamily σ N) (i : Fin D.sortCount)
    (ps : List (BodyPat σ i)) (x : N.base.carrier (coordinate σ i)) :
    x ∈ (disjunction σ i ps).denote N.base (fun j => j.elim0)
      (joinEnv N.base (fun j => j.elim0) X) ↔
      ∃ p ∈ ps, x ∈ p.denote N.base (fun j => j.elim0)
        (joinEnv N.base (fun j => j.elim0) X) := by
  induction ps with
  | nil =>
      rw [disjunction, bottom_denote]
      simp
  | cons p ps ih =>
      change (x ∈ p.denote N.base (fun j => j.elim0)
        (joinEnv N.base (fun j => j.elim0) X) ∨
        x ∈ (disjunction σ i ps).denote N.base
          (fun j => j.elim0) (joinEnv N.base (fun j => j.elim0) X)) ↔ _
      constructor
      · rintro (hp | hps)
        · exact ⟨p, List.mem_cons_self, hp⟩
        · obtain ⟨q, hq, hx⟩ := ih.mp hps
          exact ⟨q, List.mem_cons_of_mem p hq, hx⟩
      · rintro ⟨q, hq, hx⟩
        rcases List.mem_cons.mp hq with he | hq
        · subst q
          exact Or.inl hx
        · exact Or.inr (ih.mpr ⟨q, hq, hx⟩)

theorem constructorPattern_mem {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : RawFamily σ N) (c : Fin D.operationCount)
    (x : N.base.carrier (coordinate σ (D.output c))) :
    x ∈ (constructorPattern σ c).denote N.base (fun j => j.elim0)
      (joinEnv N.base (fun j => j.elim0) X) ↔
      ∃ args : ∀ j, N.base.carrier (coordinate σ (D.input c j)),
        (∀ j, args j ∈ X (D.input c j)) ∧
          x ∈ N.base.operation (.function (σ.ops (Operation.mk c))) args := by
  change (∃ args : ∀ j, N.base.carrier (coordinate σ (D.input c j)),
    (∀ j, args j ∈ (recursionVariable σ (D.input c j)).denote N.base
      (fun j => j.elim0) (joinEnv N.base (fun j => j.elim0) X)) ∧
      x ∈ N.base.operation (.function (σ.ops (Operation.mk c))) args) ↔ _
  constructor
  · rintro ⟨args, hargs, hop⟩
    refine ⟨args, ?_, hop⟩
    intro j
    exact Eq.mp (congrArg (fun S => args j ∈ S)
      (recursionVariable_denote σ N X (D.input c j))) (hargs j)
  · rintro ⟨args, hargs, hop⟩
    refine ⟨args, ?_, hop⟩
    intro j
    exact Eq.mp (congrArg (fun S => args j ∈ S)
      (recursionVariable_denote σ N X (D.input c j))).symm (hargs j)

theorem embed_mono {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Monotone (embedFamily σ N) := by
  rintro X Y h i x ⟨a, ha, rfl⟩
  exact ⟨a, h i ha, rfl⟩

theorem embed_le_iff {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : Generation.Family (reduct σ N)) (Y : RawFamily σ N) :
    embedFamily σ N X ≤ Y ↔ X ≤ extractFamily σ N Y := by
  constructor
  · intro h i a ha
    exact h i ⟨a, ha, rfl⟩
  · rintro h i x ⟨a, ha, rfl⟩
    exact h i ha

theorem embed_extract_le {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : RawFamily σ N) : embedFamily σ N (extractFamily σ N X) ≤ X := by
  rintro i x ⟨a, ha, rfl⟩
  exact ha

/-- The finite native operator agrees with the independent arbitrary-signature
Generation operator on active subsets. No raw graph law on inactive tuples
is used. Original operation indices are eliminated before any ambient equality. -/
theorem operator_embed {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B)
    (X : Generation.Family (reduct σ N)) :
    rawStep σ N (embedFamily σ N X) =
      embedFamily σ N (Generation.groundStep (reduct σ N) X) := by
  funext i
  ext x
  change x ∈ (body σ i).denote N.base (fun j => j.elim0)
    (joinEnv N.base (fun j => j.elim0) (embedFamily σ N X)) ↔ _
  rw [body, disjunction_mem]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨⟨c, hc⟩, _, rfl⟩ := List.mem_map.mp hp
    cases hc
    obtain ⟨rawargs, hargs, hop⟩ := (constructorPattern_mem σ N _ c x).mp hx
    choose args hargs heq using hargs
    have he : rawargs = fun j => (args j).val := funext (fun j => (heq j).symm)
    subst rawargs
    rw [GuardedFOL.function_graph N (σ.ops (Operation.mk c)) args] at hop
    refine ⟨(reduct σ N).op (Operation.mk c) args, ?_, ?_⟩
    · exact ⟨D.arity c, D.input c, Operation.mk c, args, hargs, rfl⟩
    · exact (Set.mem_singleton_iff.mp hop).symm
  · rintro ⟨a, ⟨n, w, op, args, hargs, he⟩, rfl⟩
    subst a
    cases op with
    | mk c =>
        refine ⟨constructorPattern σ c, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨⟨c, rfl⟩, operationsAt_mem D _ ⟨c, rfl⟩, rfl⟩
        · apply (constructorPattern_mem σ N _ c _).mpr
          refine ⟨(fun j => (args j).val), (fun j => ⟨args j, hargs j, rfl⟩), ?_⟩
          rw [GuardedFOL.function_graph N (σ.ops (Operation.mk c)) args]
          rfl

/-- Both least-fixed-point bounds use the actual operator identity. Generatedness
is a derived conclusion and is never a field or a hypothesis of the model. -/
theorem raw_lfp_eq_generated {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) :
    (rawStep σ N).lfp = embedFamily σ N (Generation.generated (reduct σ N)) := by
  apply le_antisymm
  · apply (rawStep σ N).lfp_le
    rw [operator_embed, Generation.generated_unfold]
  · have hclosed : Generation.groundStep (reduct σ N)
        (extractFamily σ N (rawStep σ N).lfp) ≤
          extractFamily σ N (rawStep σ N).lfp := by
      apply (embed_le_iff σ N _ _).mp
      rw [← operator_embed]
      exact ((rawStep σ N).monotone (embed_extract_le σ N _)).trans
        (rawStep σ N).map_lfp.le
    have h := Generation.generated_le_of_closed (reduct σ N) _ hclosed
    exact (embed_mono σ N h).trans (embed_extract_le σ N _)

/-- Actual native compiled syntax denotes the image of all original sorted
public ground-term evaluations, including genuinely empty source carriers. -/
theorem generated_denote {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) (i : Fin D.sortCount) :
    (generated σ i).denote N.base (fun j => j.elim0) (fun j => j.elim0) =
      Set.range (fun t : Ground D.signature i => (evaluate (reduct σ N) t).val) := by
  have hc := congrFun ((system σ).compile_correct N.base
    (fun j => j.elim0) (fun j => j.elim0)) i
  change (generated σ i).denote N.base _ _ = (rawStep σ N).lfp i at hc
  rw [hc, raw_lfp_eq_generated, Generation.generated_eq_evaluationRange]
  ext x
  constructor
  · rintro ⟨a, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨evaluate (reduct σ N) t, ⟨t, rfl⟩, rfl⟩

private theorem active_denote {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) (i : Fin D.sortCount)
    (v : FixedPoint.ObjEnv _ N.base (emptyContext (B := B))) :
    N.base.denote v (.app (GuardedFOL.Operation.active
      (S := SignedSpectrum.folSignature B) (σ.sorts i)) (fun j => j.elim0)) =
      N.base.operation (.active (σ.sorts i)) (fun j => j.elim0) := by
  ext x
  constructor
  · rintro ⟨args, _, hx⟩
    have he : args = (fun j => j.elim0) := funext (fun j => j.elim0)
    simpa only [he] using hx
  · intro hx
    exact ⟨(fun j => j.elim0), (fun j => j.elim0), hx⟩

theorem generationClause_satisfaction {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) (i : Fin D.sortCount) :
    (generationClause σ i).Satisfies N.base ↔
      Function.Surjective (evaluate (reduct σ N) (s := i)) := by
  constructor
  · intro h a
    have hx := h (fun j => j.elim0) (fun j => j.elim0) a.val
    change a.val ∉ N.base.denote (fun j => j.elim0)
      (.app (.active (σ.sorts i)) (fun j => j.elim0)) ∨
        a.val ∈ (generated σ i).denote N.base _ _ at hx
    rw [active_denote] at hx
    rcases hx with hn | hx
    · exact (hn a.property).elim
    · have hx' := Eq.mp (congrArg (fun S => a.val ∈ S)
        (generated_denote σ N i)) hx
      obtain ⟨t, ht⟩ := hx'
      exact ⟨t, Subtype.ext ht⟩
  · intro h v η x
    have hv : v = (fun j => j.elim0) := funext (fun j => j.elim0)
    have hη : η = (fun j => j.elim0) := funext (fun j => j.elim0)
    subst v
    subst η
    change x ∉ N.base.denote (fun j => j.elim0)
      (.app (.active (σ.sorts i)) (fun j => j.elim0)) ∨
        x ∈ (generated σ i).denote N.base _ _
    rw [active_denote]
    by_cases ha : x ∈ N.base.operation (.active (σ.sorts i)) (fun j => j.elim0)
    · right
      apply Eq.mp (congrArg (fun S => x ∈ S) (generated_denote σ N i)).symm
      obtain ⟨t, ht⟩ := h ⟨x, ha⟩
      exact ⟨t, congrArg Subtype.val ht⟩
    · exact Or.inl ha

/-- Full arbitrary equation contexts remain in the original signed spectrum. -/
theorem compiled_satisfaction {D : Profile} (E : Set (Equations D))
    {B : EQ.Signature} (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Satisfies N (compiled E σ) ↔
      Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Generated
        (reduct σ N) ∧ ExactGroundKernel (theory D E) (reduct σ N) := by
  constructor
  · intro h
    constructor
    · intro i
      exact (generationClause_satisfaction σ N i).mp (h _ (Or.inl ⟨i, rfl⟩))
    · apply (SignedSpectrum.satisfies_iff_exactGroundKernel (T := theory D E) σ N).mp
      intro p hp
      exact (FixedPoint.firstOrder_satisfies N.base p).mp
        (h _ (Or.inr ⟨p, hp, rfl⟩))
  · rintro ⟨hg, hk⟩ p (hp | hp)
    · obtain ⟨i, rfl⟩ := hp
      exact (generationClause_satisfaction σ N i).mpr (hg i)
    · obtain ⟨q, hq, rfl⟩ := hp
      exact (FixedPoint.firstOrder_satisfies N.base q).mpr
        ((SignedSpectrum.satisfies_iff_exactGroundKernel (T := theory D E) σ N).mpr hk q hq)

theorem compiled_initial_iff {D : Profile} (E : Set (Equations D))
    {B : EQ.Signature} (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Satisfies N (compiled E σ) ↔
      (∃ h : ∀ e ∈ (theory D E).axioms, e.down.Holds (reduct σ N),
        Nonempty (IsInitial (⟨reduct σ N, h⟩ : Initial.Models (theory D E)))) :=
  (compiled_satisfaction E σ N).trans
    (Initial.Presented.Characterization.modelhood_initial_iff
      (T := theory D E) (reduct σ N)).symm

theorem compiled_actual_iff {D : Profile} (E : Set (Equations D))
    {B : EQ.Signature} (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Satisfies N (compiled E σ) ↔
      Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational
        (SignedSpectrum.decode N) (actual E σ) :=
  (compiled_initial_iff E σ N).trans
    ((PresentedCompiler.initialConstraint_iff_modelhood_initial
      (theory D E) (reduct σ N)).symm.trans
      (Silmaril.Logic.Institution.Structured.Constraints.satisfaction Initial.equational σ
        (SignedSpectrum.decode N) (Initial.initialConstraint (theory D E))).symm)

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler
