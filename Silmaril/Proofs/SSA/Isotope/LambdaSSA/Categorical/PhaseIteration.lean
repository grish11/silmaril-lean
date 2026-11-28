module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs

/-! # A phase counter turns rounds into a cycle

Fixpoint, naturality, codiagonal and uniformity along the injections of
phase sums reduce the loop on `n + 1` rounds to a cycle of `n + 1` phases
entered at its first phase. The map forgetting the phase is a simulation
of that cycle onto one round.
-/

public section

universe v u

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (roundsStep PhaseSystem)

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] (S : PhaseSystem C)

/-- Eliminate the later phases of a two-part system. The state runs `a`
and moves to the later phases. They run `c`, which may stay there, return
to the state, or exit. -/
theorem eliminate_both (k : Nat) {Y : C} (a : S.obj 0 ⟶ Y ⨿ S.obj k)
    (c : S.obj k ⟶ (Y ⨿ S.obj 0) ⨿ S.obj k) :
    S.inl k ≫ S.iter (S.desc k (a ≫ coprod.map (𝟙 Y) (S.inr k))
      (c ≫ coprod.desc (coprod.map (𝟙 Y) (S.inl k)) (S.inr k ≫ coprod.inr))) =
      S.iter (a ≫ coprod.desc coprod.inl (S.iter c)) ∧
    S.inr k ≫ S.iter (S.desc k (a ≫ coprod.map (𝟙 Y) (S.inr k))
      (c ≫ coprod.desc (coprod.map (𝟙 Y) (S.inl k)) (S.inr k ≫ coprod.inr))) =
      S.iter c ≫ coprod.desc (𝟙 Y) (S.inl k ≫ S.iter (S.desc k (a ≫ coprod.map (𝟙 Y) (S.inr k))
        (c ≫ coprod.desc (coprod.map (𝟙 Y) (S.inl k)) (S.inr k ≫ coprod.inr)))) := by
  let f : S.obj (k + 1) ⟶ (Y ⨿ S.obj (k + 1)) ⨿ S.obj (k + 1) :=
    S.desc k (a ≫ coprod.desc (coprod.inl ≫ coprod.inl) (S.inr k ≫ coprod.inr))
      (c ≫ coprod.desc (coprod.desc (coprod.inl ≫ coprod.inl) (S.inl k ≫ coprod.inr ≫ coprod.inl))
        (S.inr k ≫ coprod.inr))
  have fl : S.inl k ≫ f = a ≫ coprod.desc (coprod.inl ≫ coprod.inl) (S.inr k ≫ coprod.inr) :=
    S.inl_desc k _ _
  have fr : S.inr k ≫ f =
      c ≫ coprod.desc (coprod.desc (coprod.inl ≫ coprod.inl) (S.inl k ≫ coprod.inr ≫ coprod.inl))
        (S.inr k ≫ coprod.inr) :=
    S.inr_desc k _ _
  have flat : f ≫ coprod.desc (𝟙 _) coprod.inr =
      S.desc k (a ≫ coprod.map (𝟙 Y) (S.inr k))
        (c ≫ coprod.desc (coprod.map (𝟙 Y) (S.inl k)) (S.inr k ≫ coprod.inr)) := by
    apply S.ext k
    · rw [reassoc_of% fl, S.inl_desc]
      congr 1
      apply coprod.hom_ext <;> simp
    · rw [reassoc_of% fr, S.inr_desc]
      congr 1
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simp
  have second : S.inr k ≫ S.iter f = S.iter c ≫ coprod.map (𝟙 Y) (S.inl k) := by
    have comm : (c ≫ coprod.map (coprod.map (𝟙 Y) (S.inl k)) (𝟙 _)) ≫ coprod.map (𝟙 _) (S.inr k) =
        S.inr k ≫ f := by
      rw [fr, Category.assoc]
      congr 1
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simp
    rw [← S.uniform_inr k _ f comm, S.naturality]
  have first : S.inl k ≫ S.iter f =
      (a ≫ coprod.desc coprod.inl (S.iter c)) ≫ coprod.map (𝟙 Y) (S.inl k) := by
    rw [S.fixpoint f, reassoc_of% fl, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp only [coprod.inr_desc_assoc, Category.assoc, coprod.inr_desc, coprod.inr_desc]
      exact second
  have outer := S.uniform_inl k (a ≫ coprod.desc coprod.inl (S.iter c)) (S.iter f) first.symm
  have joined : S.iter (S.iter f) = S.iter (S.desc k (a ≫ coprod.map (𝟙 Y) (S.inr k))
      (c ≫ coprod.desc (coprod.map (𝟙 Y) (S.inl k)) (S.inr k ≫ coprod.inr))) := by
    rw [S.codiagonal, flat]
  refine ⟨?_, ?_⟩
  · rw [outer, joined]
  · rw [← joined]
    conv_lhs => rw [S.fixpoint (S.iter f)]
    rw [reassoc_of% second]
    congr 1
    apply coprod.hom_ext <;> simp

/-- Entered at the state, the two-part system is the state's row with the
later phases eliminated. -/
theorem eliminate_right (k : Nat) {Y : C} (a : S.obj 0 ⟶ Y ⨿ S.obj k)
    (c : S.obj k ⟶ (Y ⨿ S.obj 0) ⨿ S.obj k) :
    S.inl k ≫ S.iter (S.desc k (a ≫ coprod.map (𝟙 Y) (S.inr k))
      (c ≫ coprod.desc (coprod.map (𝟙 Y) (S.inl k)) (S.inr k ≫ coprod.inr))) =
      S.iter (a ≫ coprod.desc coprod.inl (S.iter c)) :=
  (eliminate_both S k a c).1

/-- A chain of `k + 1` phases, each running `h`, with its entry. -/
structure Chain {Y : C} (h : S.obj 0 ⟶ Y ⨿ S.obj 0) (k : Nat) where
  start : S.obj 0 ⟶ S.obj k
  step : S.obj k ⟶ (Y ⨿ S.obj 0) ⨿ S.obj k
  start_fold : start ≫ S.fold k = 𝟙 _
  start_uniform : ∀ {B : C} (f : S.obj 0 ⟶ B ⨿ S.obj 0) (g : S.obj k ⟶ B ⨿ S.obj k),
    f ≫ coprod.map (𝟙 B) start = start ≫ g → S.iter f = start ≫ S.iter g
  eliminate : start ≫ S.iter step = roundsStep h k
  folded : step ≫ coprod.desc (𝟙 _) (S.fold k ≫ coprod.inr) = S.fold k ≫ h

variable {Y : C} (h : S.obj 0 ⟶ Y ⨿ S.obj 0)

noncomputable def Chain.one : Chain S h 0 where
  start := 𝟙 _
  step := h ≫ coprod.inl
  start_fold := Category.id_comp _
  start_uniform := by
    intro B f g comm
    rw [Category.id_comp] at comm ⊢
    rw [← comm, coprod.map_id_id, Category.comp_id]
  eliminate := by
    rw [Category.id_comp, S.fixpoint, Category.assoc, coprod.inl_desc, Category.comp_id]
    rfl
  folded := by
    have fold0 : S.fold 0 = 𝟙 _ := rfl
    rw [Category.assoc, coprod.inl_desc, Category.comp_id, fold0, Category.id_comp]

/-- One more phase in front: it runs `h` and enters the old chain. -/
noncomputable def succStep {k : Nat} (ch : Chain S h k) :
    S.obj (k + 1) ⟶ (Y ⨿ S.obj 0) ⨿ S.obj (k + 1) :=
  S.desc k (h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (ch.start ≫ S.inr k ≫ coprod.inr))
    (ch.step ≫ coprod.map (𝟙 _) (S.inr k))

theorem succ_eliminate {k : Nat} (ch : Chain S h k) :
    S.inl k ≫ S.iter (succStep S h ch) = roundsStep h (k + 1) := by
  have shape : succStep S h ch =
      S.desc k ((h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (ch.start ≫ coprod.inr)) ≫
          coprod.map (𝟙 (Y ⨿ S.obj 0)) (S.inr k))
        ((ch.step ≫ coprod.map coprod.inl (𝟙 _)) ≫
          coprod.desc (coprod.map (𝟙 (Y ⨿ S.obj 0)) (S.inl k)) (S.inr k ≫ coprod.inr)) := by
    unfold succStep
    congr 1
    · rw [Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
    · rw [Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
  have inner : (h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (ch.start ≫ coprod.inr)) ≫
      coprod.desc (coprod.inl : Y ⨿ S.obj 0 ⟶ (Y ⨿ S.obj 0) ⨿ S.obj 0)
        (S.iter ch.step ≫ coprod.inl) =
      (h ≫ coprod.desc coprod.inl (roundsStep h k)) ≫
        (coprod.inl : Y ⨿ S.obj 0 ⟶ (Y ⨿ S.obj 0) ⨿ S.obj 0) := by
    rw [Category.assoc, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp only [coprod.inr_desc_assoc, Category.assoc, coprod.inr_desc]
      rw [← Category.assoc, ch.eliminate]
  rw [shape, eliminate_right, ← S.naturality, inner, S.fixpoint, Category.assoc, coprod.inl_desc,
    Category.comp_id]
  rfl

theorem succ_folded {k : Nat} (ch : Chain S h k) :
    succStep S h ch ≫ coprod.desc (𝟙 _) (S.fold (k + 1) ≫ coprod.inr) = S.fold (k + 1) ≫ h := by
  have restFold : S.inr k ≫ S.fold (k + 1) = S.fold k := S.inr_desc k _ _
  have firstFold : S.inl k ≫ S.fold (k + 1) = 𝟙 _ := S.inl_desc k _ _
  have startFold := ch.start_fold
  have first : S.inl k ≫ succStep S h ch =
      h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (ch.start ≫ S.inr k ≫ coprod.inr) :=
    S.inl_desc k _ _
  have rest : S.inr k ≫ succStep S h ch = ch.step ≫ coprod.map (𝟙 _) (S.inr k) :=
    S.inr_desc k _ _
  apply S.ext k
  · rw [reassoc_of% first, reassoc_of% firstFold]
    conv_rhs => rw [← Category.comp_id h]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp [reassoc_of% restFold, reassoc_of% startFold]
  · rw [reassoc_of% rest, reassoc_of% restFold, ← ch.folded]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp [reassoc_of% restFold]

noncomputable def Chain.succ {k : Nat} (ch : Chain S h k) : Chain S h (k + 1) where
  start := S.inl k
  step := succStep S h ch
  start_fold := S.inl_desc k _ _
  start_uniform := fun f g comm => S.uniform_inl k f g comm
  eliminate := succ_eliminate S h ch
  folded := succ_folded S h ch

noncomputable def chain : (k : Nat) → Chain S h k
  | 0 => Chain.one S h
  | k + 1 => (chain k).succ

/-- The loop on `n + 1` rounds enters a cycle of `n + 1` phases, and the
fold is a simulation of that cycle onto one round. -/
theorem exists_cycle (n : Nat) :
    ∃ (start : S.obj 0 ⟶ S.obj n) (cycle : S.obj n ⟶ Y ⨿ S.obj n),
      start ≫ S.fold n = 𝟙 _ ∧
      cycle ≫ coprod.map (𝟙 Y) (S.fold n) = S.fold n ≫ h ∧
      S.iter (roundsStep h n) = start ≫ S.iter cycle := by
  let ch := chain S h n
  let f : S.obj n ⟶ (Y ⨿ S.obj n) ⨿ S.obj n :=
    ch.step ≫ coprod.map (coprod.map (𝟙 Y) ch.start) (𝟙 _)
  have inner : S.iter f = S.iter ch.step ≫ coprod.map (𝟙 Y) ch.start := (S.naturality ch.step _).symm
  have entry : roundsStep h n ≫ coprod.map (𝟙 Y) ch.start = ch.start ≫ S.iter f := by
    rw [inner, ← Category.assoc, ch.eliminate]
  have startFold := ch.start_fold
  have cyclic : (f ≫ coprod.desc (𝟙 _) coprod.inr) ≫ coprod.map (𝟙 Y) (S.fold n) = S.fold n ≫ h := by
    rw [← ch.folded, Category.assoc, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · simp
      · simp [reassoc_of% startFold]
    · simp
  refine ⟨ch.start, f ≫ coprod.desc (𝟙 _) coprod.inr, ch.start_fold, cyclic, ?_⟩
  rw [ch.start_uniform _ (S.iter f) entry, S.codiagonal]

/-- With uniformity along the fold, the loop on any number of rounds is
the loop on one round. -/
theorem iter_roundsStep_of_fold (n : Nat)
    (fold : ∀ c : S.obj n ⟶ Y ⨿ S.obj n,
      c ≫ coprod.map (𝟙 Y) (S.fold n) = S.fold n ≫ h → S.iter c = S.fold n ≫ S.iter h) :
    S.iter (roundsStep h n) = S.iter h := by
  obtain ⟨start, cycle, startFold, square, enters⟩ := exists_cycle S h n
  rw [enters, fold cycle square, ← Category.assoc, startFold, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration
