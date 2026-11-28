module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Search
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (behaviour_ext)

universe u v w x

variable {κ : Type v} {A B : Ty κ} {α : Type w} {σ : Type x}

variable {R L : List (Ty κ)}

private theorem ordinary_singleton {n : Nat} {o p : Outcome n α σ} :
    Behaviour.Ordinary (WithTop.some {o}) p ↔ p = o :=
  ⟨fun h => Set.mem_singleton_iff.mp h.2, fun h => ⟨WithTop.coe_ne_top, Set.mem_singleton_iff.mpr h⟩⟩

private theorem not_external_branch (o : Outcome L.length α σ)
    (j : Fin R.length) (a : Value α) (s : σ) :
    Feedback.external R L o ≠ .ret (Feedback.internal R L j) a s := by
  cases o with
  | ret i b t =>
    intro eq
    have label := congrArg Fin.val (Outcome.ret.inj eq).1
    change R.length + i.val = j.val at label
    have := j.isLt
    omega
  | fault | diverge => intro eq; cases eq

private theorem external_injective :
    Function.Injective (Feedback.external (α := α) (σ := σ) R L) := by
  intro o p eq
  cases o <;> cases p <;>
    simp only [Feedback.external, Outcome.ret.injEq, Outcome.fault.injEq, reduceCtorEq] at eq ⊢
  case ret.ret i a s j b t =>
    have indices := congrArg Fin.val eq.1
    change R.length + i.val = R.length + j.val at indices
    exact ⟨Fin.ext (Nat.add_left_cancel indices), eq.2⟩
  case fault.fault => exact eq

theorem branch_only {f : Feedback.Run R L α σ} {p q : Feedback.Point R.length α σ}
    {j : Fin R.length} {a : Value α} {s : σ}
    (run : f p = WithTop.some {Outcome.ret (Feedback.internal R L j) a s}) :
    Feedback.Step f p q ↔ q = .block j a s := by
  constructor
  · intro edge
    cases edge with
    | @branch i b t obs =>
      rw [run] at obs
      obtain ⟨label, rfl, rfl⟩ := Outcome.ret.inj (ordinary_singleton.mp obs)
      have val := congrArg Fin.val label
      exact congrArg (fun k => Feedback.Point.block k b t) (Fin.ext val)
  · rintro rfl
    apply Feedback.Step.branch
    rw [run]
    exact ordinary_singleton.mpr rfl

theorem close_branch {f : Feedback.Run R L α σ} {p : Feedback.Point R.length α σ}
    {i : Fin R.length} {a : Value α} {s : σ}
    (run : f p = WithTop.some {Outcome.ret (Feedback.internal R L i) a s}) :
    Feedback.close f p = Feedback.close f (.block i a s) := by
  have top : Feedback.close f p = ⊤ ↔ Feedback.close f (.block i a s) = ⊤ := by
    rw [Feedback.close_top_unfold (p := p)]
    constructor
    · rintro (atStart | ⟨q, edge, top⟩)
      · exact (WithTop.coe_ne_top (run ▸ atStart)).elim
      · exact (branch_only run).mp edge ▸ top
    · exact fun top => .inr ⟨_, (branch_only run).mpr rfl, top⟩
  refine behaviour_ext top fun o => ?_
  by_cases safe : Feedback.close f p = ⊤
  · simp [safe, top.mp safe, Behaviour.Ordinary]
  rw [Feedback.close_ordinary_unfold safe]
  constructor
  · rintro (external | ⟨q, edge, out⟩)
    · rw [run] at external
      exact (not_external_branch o i a s (ordinary_singleton.mp external)).elim
    · exact (branch_only run).mp edge ▸ out
  · exact fun out => .inr ⟨_, (branch_only run).mpr rfl, out⟩

theorem no_step_of_terminal {f : Feedback.Run R L α σ} {p q : Feedback.Point R.length α σ}
    {o : Outcome L.length α σ} (run : f p = WithTop.some {Feedback.external R L o}) :
    ¬ Feedback.Step f p q := by
  intro edge
  cases edge with
  | @branch i b s obs =>
    rw [run] at obs
    exact not_external_branch o i b s (ordinary_singleton.mp obs).symm

theorem close_terminal {f : Feedback.Run R L α σ} {p : Feedback.Point R.length α σ}
    {o : Outcome L.length α σ} (run : f p = WithTop.some {Feedback.external R L o}) :
    Feedback.close f p = WithTop.some {o} := by
  have noStep (q) : ¬ Feedback.Step f p q := no_step_of_terminal run
  have safe : ¬ Feedback.ReachesUB f p := by
    rintro ⟨q, path, top⟩
    obtain rfl := (Relation.reflTransGen_iff_eq noStep).mp path
    exact WithTop.coe_ne_top (run ▸ top)
  rw [Feedback.close_of_noUB safe]
  apply congrArg WithTop.some
  ext u
  change (Feedback.Finite f p u ∨ u = .diverge ∧ Feedback.Infinite f p) ↔ u = o
  constructor
  · rintro (⟨q, path, obs⟩ | ⟨_, path, start, edges⟩)
    · obtain rfl := (Relation.reflTransGen_iff_eq noStep).mp path
      rw [run] at obs
      exact external_injective (ordinary_singleton.mp obs)
    · exact (noStep _ (start ▸ edges 0)).elim
  · intro eq
    subst u
    exact .inl ⟨p, .refl, run.symm ▸ ordinary_singleton.mpr rfl⟩

theorem close_infinite_of_singleton {f : Feedback.Run R L α σ}
    (path : Nat → Feedback.Point R.length α σ)
    (localStep : ∀ n, ∃ i a s, path (n + 1) = .block i a s ∧
      f (path n) = WithTop.some {Outcome.ret (Feedback.internal R L i) a s}) :
    Feedback.close f (path 0) = WithTop.some {Outcome.diverge} := by
  have unique (n : Nat) (q : Feedback.Point R.length α σ) :
      Feedback.Step f (path n) q ↔ q = path (n + 1) := by
    obtain ⟨i, a, s, next, run⟩ := localStep n
    rw [next, branch_only run]
  have reached {q} (h : Feedback.Reaches f (path 0) q) : ∃ n, q = path n := by
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ step ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, (unique n _).mp step⟩
  have safe : ¬ Feedback.ReachesUB f (path 0) := by
    rintro ⟨q, steps, top⟩
    obtain ⟨n, rfl⟩ := reached steps
    obtain ⟨_, _, _, _, run⟩ := localStep n
    exact WithTop.coe_ne_top (run ▸ top)
  rw [Feedback.close_of_noUB safe]
  apply congrArg WithTop.some
  ext o
  change (Feedback.Finite f (path 0) o ∨ o = .diverge ∧ Feedback.Infinite f (path 0)) ↔ o = .diverge
  constructor
  · rintro (⟨q, steps, obs⟩ | h)
    · obtain ⟨n, rfl⟩ := reached steps
      obtain ⟨i, a, s, _, run⟩ := localStep n
      rw [run] at obs
      exact (not_external_branch o i a s (ordinary_singleton.mp obs)).elim
    · exact h.1
  · intro h
    exact .inr ⟨h, path, rfl, fun n => (unique n _).mpr rfl⟩

section Positional

variable {points results states : Nat}
variable (C : PositionalCarrier R L α σ points results states)
variable {f : Feedback.Run R L α σ} {rows : Fin points → Row points results states}

private theorem close_stop (p : Fin points) (result : Result results states)
    (run : f (invocationPoint C.invocation p) = Row.routed C (.stop result)) :
    Feedback.close f (invocationPoint C.invocation p) = result.routed C := by
  cases result with
  | ret b t => exact close_terminal (o := .ret (C.result b).1 (C.result b).2 (C.final t)) run
  | fault t => exact close_terminal (o := .fault (C.final t)) run
  | diverge => exact close_terminal (o := .diverge) run
  | ub => exact Feedback.close_eq_top_iff.mpr ⟨_, .refl, run⟩

private theorem classify_found (bound : Nat) (p : Fin points) (result : Result results states)
    (agrees : ∀ q, f (invocationPoint C.invocation q) = (rows q).routed C)
    (found : search rows bound p = some result) :
    Feedback.close f (invocationPoint C.invocation p) = result.routed C := by
  induction bound generalizing p with
  | zero => cases found
  | succ bound ih =>
    cases row : rows p with
    | stop output =>
      have eq : output = result := by simpa [search, row] using found
      subst output
      exact close_stop C p result (row ▸ agrees p)
    | «repeat» q =>
      have tail : search rows bound q = some result := by simpa [search, row] using found
      have here := agrees p
      rw [row] at here
      exact (close_branch (i := (C.invocation q).1) here).trans (ih q tail)

private theorem classify_cycle (p : Fin points)
    (agrees : ∀ q, f (invocationPoint C.invocation q) = (rows q).routed C)
    (empty : search rows points p = none) :
    Feedback.close f (invocationPoint C.invocation p) = Result.routed C .diverge := by
  let path := fun k => invocationPoint C.invocation (orbit rows p k)
  have atPath (k) : f (path k) = Row.routed C (.repeat (orbit rows p (k + 1))) := by
    exact (agrees _).trans (congrArg (Row.routed C) (repeats_of_exhausted rows p empty k))
  have onlyNext (k) (q) : Feedback.Step f (path k) q ↔ q = path (k + 1) :=
    branch_only (j := (C.invocation (orbit rows p (k + 1))).1) (atPath k)
  have reachable {q} (reach : Feedback.Reaches f (invocationPoint C.invocation p) q) : ∃ k, q = path k := by
    induction reach with
    | refl => exact ⟨0, congrArg (invocationPoint C.invocation) (orbit_zero rows p).symm⟩
    | tail _ edge ih =>
      obtain ⟨k, rfl⟩ := ih
      exact ⟨k + 1, (onlyNext k _).mp edge⟩
  have safe : ¬ Feedback.ReachesUB f (invocationPoint C.invocation p) := by
    rintro ⟨q, reach, top⟩
    obtain ⟨k, rfl⟩ := reachable reach
    exact WithTop.coe_ne_top (atPath k ▸ top)
  have infinite : Feedback.Infinite f (invocationPoint C.invocation p) :=
    ⟨path, congrArg (invocationPoint C.invocation) (orbit_zero rows p), fun k => (onlyNext k _).mpr rfl⟩
  rw [Feedback.close_of_noUB safe]
  apply congrArg WithTop.some
  ext o
  change (Feedback.Finite f (invocationPoint C.invocation p) o ∨
    o = .diverge ∧ Feedback.Infinite f (invocationPoint C.invocation p)) ↔ o = .diverge
  constructor
  · rintro (⟨q, reach, finish⟩ | ⟨eq, _⟩)
    · obtain ⟨k, rfl⟩ := reachable reach
      rw [atPath k] at finish
      exact (not_external_branch o (C.invocation (orbit rows p (k + 1))).1 _ _
        (ordinary_singleton.mp finish)).elim
    · exact eq
  · exact fun eq => .inr ⟨eq, infinite⟩

theorem classify_routed (rows : Fin points → Row points results states) (p : Fin points)
    (agrees : ∀ q, f (invocationPoint C.invocation q) = (rows q).routed C) :
    Feedback.close f (invocationPoint C.invocation p) = (execute rows p).routed C := by
  cases found : search rows points p with
  | none => simpa [execute, found] using classify_cycle C p agrees found
  | some result => simpa [execute, found] using classify_found C points p result agrees found

end Positional

section CertifiedTable

variable {Φ : Type u} [HasTy Φ (Ty κ)] {X : Ty κ}
variable {M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))}
variable {captures points results states : Nat}
variable (C : Carrier M X A B captures points results states)

theorem classify_positional {f : Feedback.Run R [B] M.raw.α M.raw.σ}
    (invocation : Fin points → Fin R.length × Value M.raw.α × M.raw.σ)
    (rows : Fin points → Row points results states) (p : Fin points)
    (agrees : ∀ q, f (invocationPoint invocation q) = (rows q).positional C invocation) :
    Feedback.close f (invocationPoint invocation p) = (execute rows p).behaviour C := by
  have classified := classify_routed (C.positional invocation) rows p agrees
  cases eq : execute rows p <;> rw [eq] at classified <;> exact classified

private def singletonInvocation (p : Fin points) : Fin 1 × Value M.raw.α × M.raw.σ :=
  (0, (C.invocation p).1.val, (C.invocation p).2)

private theorem label_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have bound : i.val = 0 ∨ i.val = 1 := by omega
  exact bound.imp (fun h => Fin.ext h) (fun h => Fin.ext h)

set_option backward.isDefEq.respectTransparency false in
private theorem preimage_row (row : Row points results states) :
    (row.behaviour C).map (Set.preimage tagIterationOutcome) = row.positional C (R := [A]) (singletonInvocation C) := by
  cases row with
  | «repeat» p =>
    apply congrArg WithTop.some
    ext o
    cases o with
    | ret i b t =>
      have label : Feedback.internal [A] [B] 0 = (0 : Fin 2) := rfl
      rcases label_cases i with rfl | rfl <;> simp [tagIterationOutcome, Carrier.positional, singletonInvocation, label]
    | fault | diverge => simp [tagIterationOutcome]
  | stop result =>
    cases result with
    | ub => rfl
    | ret b t =>
      apply congrArg WithTop.some
      ext o
      cases o with
      | ret i a s =>
        rcases label_cases i with rfl | rfl <;> simp [tagIterationOutcome, Carrier.positional, Feedback.external]
      | fault | diverge => simp [tagIterationOutcome, Carrier.positional, Feedback.external]
    | fault | diverge =>
      apply congrArg WithTop.some
      ext o
      cases o <;> simp [tagIterationOutcome, Carrier.positional]

set_option backward.isDefEq.respectTransparency false in
theorem classify_sum
    (step : single A ⟶ (single (.coprod B A) : Interface M.raw.α M.raw.σ M.atomType))
    (rows : Fin points → Row points results states)
    (certificate : ∀ q, step.run 0 (C.invocation q).1 (C.invocation q).2 = (rows q).behaviour C)
    (p : Fin points) :
    (iterateSum step).run 0 (C.invocation p).1 (C.invocation p).2 =
      (execute rows p).behaviour C := by
  let graph := iterationGraph step (C.invocation p).1
  change Feedback.close graph (.entry (C.invocation p).2) = _
  have entry : graph (.entry (C.invocation p).2) =
      WithTop.some {Outcome.ret (Feedback.internal [A] [B] 0) (C.invocation p).1.val (C.invocation p).2} := rfl
  rw [close_branch entry]
  apply classify_positional (R := [A]) C (singletonInvocation C) rows p
  intro q
  change (step.total 0 (C.invocation q).1.val (C.invocation q).2).map _ = _
  rw [Arrow.total_typed step 0 (C.invocation q).1 (C.invocation q).2, certificate q]
  exact preimage_row C _

theorem classify (r : Region Φ [A, X] [.coprod B A]) (table : Table captures points results states)
    (certificate : Certified C r table) (c : Fin captures) (p : Fin points) :
    (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 =
      (execute (table c) p).behaviour C :=
  classify_sum C (interpretSingleton (M.extend (C.capture c).property) r) (table c) (certificate c) p

end CertifiedTable

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
