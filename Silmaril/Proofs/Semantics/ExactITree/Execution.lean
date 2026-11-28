module

public import Silmaril.Semantics.ExactITree.Defs
import Silmaril.Proofs.Semantics.ExactITree.Lowering

public section

namespace Silmaril.Elgot.ITree.Exact.Proofs

open CategoryTheory

universe u v

variable {S T : Signature.{u}} {P : Profile.{v}} {A : Type v}
variable (f : S ⟶ T) (K : Kernel P T) (env : P.Env)

private theorem reduct_reply {R : Type u} (e : S.Event R) (reply : R)
    (before after : P.Store) (batch : List P.Output) :
    Kernel.reduct f K env before e (.reply reply after batch) ↔
      ∃ r, K env before (f.exchange e).event (.reply r after batch) ∧
        (f.exchange e).project r = reply := by
  constructor
  · rintro ⟨c, hc, eq⟩
    cases c with
    | reply r store output =>
      cases eq
      exact ⟨r, hc, rfl⟩
    | stop => cases eq
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, hr, rfl⟩

private theorem reduct_stop {R : Type u} (e : S.Event R) (reason : P.Stop)
    (before : P.Store) (after : Option P.Store) (batch : List P.Output) :
    Kernel.reduct f K env before e (.stop reason after batch) ↔
      K env before (f.exchange e).event (.stop reason after batch) := by
  constructor
  · rintro ⟨c, hc, eq⟩
    cases c with
    | reply => cases eq
    | stop =>
      cases eq
      exact hc
  · intro h
    exact ⟨_, h, rfl⟩

private theorem reduct_enabled {R : Type u} (e : S.Event R) (w : P.Store) :
    (∃ answer, Kernel.reduct f K env w e answer) ↔ (∃ c, K env w (f.exchange e).event c) := by
  constructor
  · rintro ⟨_, c, h, _⟩
    exact ⟨c, h⟩
  · rintro ⟨c, h⟩
    exact ⟨_, c, h, rfl⟩

/-- The target successors are exactly the image of the reduct successors,
including when multiple target replies project to the same source reply. -/
theorem step_lower (s : Config P S A) (batch : List P.Output) (t : Config P T A) :
    Step K env (s.lower f) batch t ↔
      ∃ next, Step (Kernel.reduct f K) env s batch next ∧ next.lower f = t := by
  rcases s with ⟨tree, store⟩
  rcases cases_visible tree with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
  · simp [Step, Config.lower, eq_comm]
  · simp [Step, Config.lower]
  · simp only [Step, Config.lower, lower_vis, root_vis, reduct_reply]
    constructor
    · rintro ⟨r, hr, ht⟩
      exact ⟨(k ((f.exchange e).project r), t.2), ⟨_, ⟨r, hr, rfl⟩, rfl⟩, Prod.ext ht.symm rfl⟩
    · rintro ⟨⟨t', w⟩, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, rfl⟩
      exact ⟨r, hr, rfl⟩

theorem finish_lower (s : Config P S A) (batch : List P.Output) (last : End P A) :
    Finish K env (s.lower f) batch last ↔ Finish (Kernel.reduct f K) env s batch last := by
  rcases s with ⟨tree, store⟩
  rcases cases_visible tree with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩ <;>
    simp [Finish, Config.lower, reduct_enabled, reduct_stop]

private theorem path_lift {start t : Config P T A} {log : List P.Output}
    (h : Path K env start log t) (s : Config P S A) (hs : s.lower f = start) :
    ∃ next, Path (Kernel.reduct f K) env s log next ∧ next.lower f = t := by
  induction h generalizing s with
  | nil t => exact ⟨s, .nil _, hs⟩
  | cons step _ ih =>
    rw [← hs] at step
    obtain ⟨m, hm, heq⟩ := (step_lower f K env _ _ _).mp step
    obtain ⟨next, hnext, rfl⟩ := ih m heq
    exact ⟨next, .cons hm hnext, rfl⟩

theorem path_lower (s : Config P S A) (log : List P.Output) (t : Config P T A) :
    Path K env (s.lower f) log t ↔
      ∃ next, Path (Kernel.reduct f K) env s log next ∧ next.lower f = t := by
  refine ⟨fun h => path_lift f K env h s rfl, ?_⟩
  rintro ⟨next, h, rfl⟩
  induction h with
  | nil => exact .nil _
  | cons step _ ih => exact .cons ((step_lower f K env _ _ _).mpr ⟨_, step, rfl⟩) ih

theorem infinite_lower (s : Config P S A) (batches : Nat → List P.Output) :
    Infinite K env (s.lower f) batches ↔ Infinite (Kernel.reduct f K) env s batches := by
  constructor
  · rintro ⟨states, h0, hstep⟩
    let C (n : Nat) := { c : Config P S A // c.lower f = states n }
    have next (n : Nat) (c : C n) :
        ∃ d : C (n + 1), Step (Kernel.reduct f K) env c.val (batches n) d.val := by
      have step := hstep n
      rw [← c.property] at step
      obtain ⟨d, hd, heq⟩ := (step_lower f K env _ _ _).mp step
      exact ⟨⟨d, heq⟩, hd⟩
    let lift : (n : Nat) → C n :=
      Nat.rec (motive := C) ⟨s, h0.symm⟩ (fun n c => Classical.choose (next n c))
    exact ⟨fun n => (lift n).val, rfl, fun n => Classical.choose_spec (next n (lift n))⟩
  · rintro ⟨states, rfl, hstep⟩
    exact ⟨fun n => (states n).lower f, rfl,
      fun n => (step_lower f K env _ _ _).mpr ⟨_, hstep n, rfl⟩⟩

theorem observes_lower (s : Config P S A) (obs : Observation P A) :
    Observes K env (s.lower f) obs ↔ Observes (Kernel.reduct f K) env s obs := by
  cases obs with
  | «prefix» log =>
    constructor
    · rintro ⟨word, t, ht, hprefix⟩
      obtain ⟨next, hnext, rfl⟩ := (path_lower f K env ..).mp ht
      simp only [finish_lower] at hprefix
      exact ⟨word, next, hnext, hprefix⟩
    · rintro ⟨word, next, hnext, hprefix⟩
      refine ⟨word, next.lower f, (path_lower f K env ..).mpr ⟨next, hnext, rfl⟩, ?_⟩
      simpa only [finish_lower] using hprefix
  | finished log last =>
    constructor
    · rintro ⟨word, t, batch, ht, finished, rfl⟩
      obtain ⟨next, hnext, rfl⟩ := (path_lower f K env ..).mp ht
      exact ⟨word, next, batch, hnext, (finish_lower f K env ..).mp finished, rfl⟩
    · rintro ⟨word, next, batch, hnext, finished, rfl⟩
      exact ⟨word, next.lower f, batch, (path_lower f K env ..).mpr ⟨next, hnext, rfl⟩,
        (finish_lower f K env ..).mpr finished, rfl⟩
  | infinite log =>
    simp only [Observes, infinite_lower]

end Silmaril.Elgot.ITree.Exact.Proofs
