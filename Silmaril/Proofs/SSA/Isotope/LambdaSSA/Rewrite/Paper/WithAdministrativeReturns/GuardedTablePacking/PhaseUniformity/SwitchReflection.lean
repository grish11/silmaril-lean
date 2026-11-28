module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SwitchModel

/-! # Complete runs of a switch table of polls determine its bisimulation class -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open Paper.Extension.Singleton (ofRegion ofType sumCofan)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
local notation "PEqv" => WithGuardedTablePacking.WithPhaseUniformity.Eqv

noncomputable local instance switchReflInstructions : InstructionModel J M signature.Instr := instructions model
local instance switchReflCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

/-! ## Words -/

theorem event_inj {l l' g g' t t' p p' : Bool} (h : event l g (t, p) = event l' g' (t', p')) :
    l = l' ∧ g = g' ∧ t = t' ∧ p = p' := by
  simpa [event] using h

theorem word_cons {e e' : Event} {v v' : Word} (h : FreeMonoid.of e * v = FreeMonoid.of e' * v') :
    e = e' ∧ v = v' := by
  have l : e :: FreeMonoid.toList v = e' :: FreeMonoid.toList v' := congrArg FreeMonoid.toList h
  have tail := congrArg FreeMonoid.ofList (List.cons.inj l).2
  exact ⟨(List.cons.inj l).1,
    (FreeMonoid.ofList_toList v).symm.trans (tail.trans (FreeMonoid.ofList_toList v'))⟩

theorem word_single {e e' : Event} {v : Word} (h : FreeMonoid.of e = FreeMonoid.of e' * v) :
    e = e' ∧ v = 1 := by
  have c := word_cons (v := 1) ((mul_one _).trans h)
  exact ⟨c.1, c.2.symm⟩

theorem one_ne_cons {e : Event} {v : Word} (h : (1 : Word) = FreeMonoid.of e * v) : False := by
  have l : ([] : List Event) = e :: FreeMonoid.toList v := congrArg FreeMonoid.toList h
  cases l

theorem ne_not (b : Bool) : b ≠ !b := by cases b <;> decide

/-! ## Reading one round from the complete runs -/

section Rounds

variable {K K' : Nat} (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Bool → Fin (K + 1))
  (poll' : Fin (K' + 1) → Poll) (next' : Fin (K' + 1) → Bool → Fin (K' + 1))

theorem switch_obs_ne_one (i : Fin (K + 1)) (g : Bool) {r : Except Bool (value Bit)}
    (h : (r, (1 : Word)) ∈ (Switch.ofPolls poll next).observations i g) : False := by
  rcases (switch_unfold poll next i g r 1).1 h with ⟨-, e⟩ | ⟨v, -, e⟩ | ⟨pl, v, -, e⟩
  · exact one_ne_cons (e.trans (mul_one _).symm)
  · exact one_ne_cons e
  · exact one_ne_cons e

/-- The run with one request shows the label and which reply returns. -/
theorem switch_obs_poll (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool)
    (h : (Switch.ofPolls poll next).observations i g = (Switch.ofPolls poll' next').observations i' g) :
    poll i = poll' i' := by
  have mem : (Except.ok (bit true), FreeMonoid.of (event (poll i).label g ((poll i).returnRight, true))) ∈
      (Switch.ofPolls poll next).observations i g :=
    (switch_unfold poll next i g _ _).2 (.inl ⟨rfl, rfl⟩)
  rw [h] at mem
  rcases (switch_unfold poll' next' i' g _ _).1 mem with ⟨-, e⟩ | ⟨v, hv, e⟩ | ⟨pl, v, hv, e⟩
  · obtain ⟨hl, -, hr, -⟩ := event_inj (FreeMonoid.of_injective e)
    exact poll_ext hl hr
  · obtain ⟨-, rfl⟩ := word_single e
    exact (switch_obs_ne_one poll' next' _ _ hv).elim
  · obtain ⟨-, rfl⟩ := word_single e
    exact (switch_obs_ne_one poll' next' _ _ hv).elim

/-- Cancelling the first event: the runs through a successor are the runs
of that successor. -/
theorem switch_obs_sub (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool) (hp : poll i = poll' i')
    (h : (Switch.ofPolls poll next).observations i g ⊆ (Switch.ofPolls poll' next').observations i' g) :
    (Switch.ofPolls poll next).observations (next i false) false ⊆
        (Switch.ofPolls poll' next').observations (next' i' false) false ∧
      ∀ pl, (Switch.ofPolls poll next).observations (next i true) pl ⊆
        (Switch.ofPolls poll' next').observations (next' i' true) pl := by
  refine ⟨?_, fun pl => ?_⟩
  · rintro ⟨r, v⟩ hv
    have mem := h ((switch_unfold poll next i g r _).2 (.inr (.inl ⟨v, hv, rfl⟩)))
    rw [hp] at mem
    rcases (switch_unfold poll' next' i' g r _).1 mem with ⟨-, e⟩ | ⟨v', hv', e⟩ | ⟨pl, v', -, e⟩
    · have c := word_cons (e.trans (mul_one _).symm)
      exact absurd (event_inj c.1).2.2.2 (by decide)
    · obtain ⟨-, rfl⟩ := word_cons e
      exact hv'
    · have c := word_cons e
      exact absurd (event_inj c.1).2.2.1 (ne_not _)
  · rintro ⟨r, v⟩ hv
    have mem := h ((switch_unfold poll next i g r _).2 (.inr (.inr ⟨pl, v, hv, rfl⟩)))
    rw [hp] at mem
    rcases (switch_unfold poll' next' i' g r _).1 mem with ⟨-, e⟩ | ⟨v', -, e⟩ | ⟨pl', v', hv', e⟩
    · have c := word_cons (e.trans (mul_one _).symm)
      exact absurd (event_inj c.1).2.2.1.symm (ne_not _)
    · have c := word_cons e
      exact absurd (event_inj c.1).2.2.1.symm (ne_not _)
    · obtain ⟨c, rfl⟩ := word_cons e
      have same : pl = pl' := (event_inj c).2.2.2
      subst same
      exact hv'

/-- Equal complete runs give the same poll and equal complete runs at
both successors. -/
theorem switch_obs_step (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool)
    (h : (Switch.ofPolls poll next).observations i g = (Switch.ofPolls poll' next').observations i' g) :
    poll i = poll' i' ∧ ∀ b, ∃ g', (Switch.ofPolls poll next).observations (next i b) g' =
      (Switch.ofPolls poll' next').observations (next' i' b) g' := by
  have hp := switch_obs_poll poll next poll' next' i i' g h
  have fwd := switch_obs_sub poll next poll' next' i i' g hp h.subset
  have bwd := switch_obs_sub poll' next' poll next i' i g hp.symm h.symm.subset
  refine ⟨hp, fun b => ?_⟩
  cases b
  · exact ⟨false, Set.Subset.antisymm fwd.1 bwd.1⟩
  · exact ⟨false, Set.Subset.antisymm (fwd.2 false) (bwd.2 false)⟩

theorem switch_obs_walk : ∀ (w : List Bool) (i : Fin (K + 1)) (i' : Fin (K' + 1)),
    (∃ g, (Switch.ofPolls poll next).observations i g = (Switch.ofPolls poll' next').observations i' g) →
    poll ((Switch.ofPolls poll next).walk i w) = poll' ((Switch.ofPolls poll' next').walk i' w)
  | [], i, i', ⟨g, h⟩ => (switch_obs_step poll next poll' next' i i' g h).1
  | b :: w, i, i', ⟨g, h⟩ =>
    switch_obs_walk w _ _ ((switch_obs_step poll next poll' next' i i' g h).2 b)

theorem switch_eqv_of_polls (i : Fin (K + 1)) (i' : Fin (K' + 1))
    (h : ∀ w, poll ((Switch.ofPolls poll next).walk i w) = poll' ((Switch.ofPolls poll' next').walk i' w)) :
    PEqv false [State] ((Switch.ofPolls poll next).entered i) ((Switch.ofPolls poll' next').entered i') [Bit] :=
  Tables.switch_bisim_eqv _ _ i i' (fun w => congrArg Poll.program (h w))

/-- Equal complete runs give a bisimulation: the relation of having equal
complete runs for some query. -/
theorem switch_bisim_of_obs (i : Fin (K + 1)) (i' : Fin (K' + 1))
    (h : (Switch.ofPolls poll next).observations i false = (Switch.ofPolls poll' next').observations i' false) :
    ∃ R : Fin (K + 1) → Fin (K' + 1) → Prop, (∀ x y, R x y → poll x = poll' y) ∧
      (∀ x y, R x y → ∀ b, R (next x b) (next' y b)) ∧ R i i' :=
  ⟨fun x y => ∃ g, (Switch.ofPolls poll next).observations x g = (Switch.ofPolls poll' next').observations y g,
    fun x y ⟨g, h⟩ => (switch_obs_step poll next poll' next' x y g h).1,
    fun x y ⟨g, h⟩ b => (switch_obs_step poll next poll' next' x y g h).2 b, ⟨false, h⟩⟩

theorem switch_polls_of_bisim (R : Fin (K + 1) → Fin (K' + 1) → Prop) (hp : ∀ x y, R x y → poll x = poll' y)
    (hn : ∀ x y, R x y → ∀ b, R (next x b) (next' y b)) (i : Fin (K + 1)) (i' : Fin (K' + 1)) (r : R i i')
    (w : List Bool) :
    poll ((Switch.ofPolls poll next).walk i w) = poll' ((Switch.ofPolls poll' next').walk i' w) :=
  hp _ _ (Tables.walk_rel (Switch.ofPolls poll next) (Switch.ofPolls poll' next') R hn w i i' r)

end Rounds

theorem switch_obs_of_valid {K K' : Nat} {t : Switch K} {t' : Switch K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)}
    (h : WithGuardedTablePacking.Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.observations i g = t'.observations i' g := by
  have eq := h J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold Switch.observations denoteSingletonRegion
  rw [eq]

theorem switch_obs_of_eqv {K K' : Nat} {t : Switch K} {t' : Switch K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)} (e : PEqv false [State] (t.entered i) (t'.entered i') [Bit]) (g : Bool) :
    t.observations i g = t'.observations i' g :=
  switch_obs_of_valid (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) g

/-! ## The three-state table and the six-state table -/

/-- The joint walks of the two entries. -/
abbrev triWide (x : Fin 3) (y : Fin 6) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = 2 ∧ y = 2) ∨ (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 4) ∨ (x = 0 ∧ y = 5)

theorem triWide_next (x : Fin 3) (y : Fin 6) (r : triWide x y) (b : Bool) :
    triWide (triNext x b) (wideNext y b) := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases b <;> decide

theorem triWide_poll (a b c : Poll) (x : Fin 3) (y : Fin 6) (r : triWide x y) :
    triPolls a b c x = widePolls a b c b y := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem tri_wide_polls (a b c : Poll) (w : List Bool) :
    triPolls a b c ((Switch.ofPolls (triPolls a b c) triNext).walk 0 w) =
      widePolls a b c b ((Switch.ofPolls (widePolls a b c b) wideNext).walk 0 w) :=
  triWide_poll a b c _ _
    (Tables.walk_rel (Switch.ofPolls (triPolls a b c) triNext) (Switch.ofPolls (widePolls a b c b) wideNext)
      triWide triWide_next w 0 0 (.inl ⟨rfl, rfl⟩))

/-- With another poll at state four, the polls still agree on every word
of length at most three except `false, false, false`. -/
theorem wide_only (a b c d : Poll) : ∀ w : List Bool, w.length ≤ 3 → w ≠ [false, false, false] →
    triPolls a b c ((Switch.ofPolls (triPolls a b c) triNext).walk 0 w) =
      widePolls a b c d ((Switch.ofPolls (widePolls a b c d) wideNext).walk 0 w)
  | [], _, _ => rfl
  | [x], _, _ => by cases x <;> rfl
  | [x, y], _, _ => by cases x <;> cases y <;> rfl
  | [x, y, z], _, ne => by
    cases x <;> cases y <;> cases z <;> first | rfl | exact absurd rfl ne
  | _ :: _ :: _ :: _ :: _, len, _ => by
    simp only [List.length_cons] at len
    omega

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
