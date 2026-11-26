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

private abbrev Point (A : Ty κ) (α : Type w) (σ : Type x) := Feedback.Point [A].length α σ
private abbrev branchResult (A B : Ty κ) (b : Value α) (t : σ) : Behaviour ([A] ++ [B]).length α σ :=
  WithTop.some {Outcome.ret (Feedback.internal [A] [B] 0) b t}

private abbrev terminalResult (A B : Ty κ) (o : Outcome [B].length α σ) : Behaviour ([A] ++ [B]).length α σ :=
  WithTop.some {Feedback.external [A] [B] o}

private theorem ordinary_singleton {n : Nat} {o p : Outcome n α σ} :
    Behaviour.Ordinary (WithTop.some {o}) p ↔ p = o :=
  ⟨fun h => Set.mem_singleton_iff.mp h.2, fun h => ⟨WithTop.coe_ne_top, Set.mem_singleton_iff.mpr h⟩⟩

private theorem not_external_branch (o : Outcome [B].length α σ) (a : Value α) (s : σ) :
    Feedback.external [A] [B] o ≠ .ret (Feedback.internal [A] [B] 0) a s := by
  cases o with
  | ret i b t =>
    intro eq
    have label := congrArg Fin.val (Outcome.ret.inj eq).1
    change 1 + i.val = 0 at label
    omega
  | fault | diverge => intro eq; cases eq

private theorem external_injective :
    Function.Injective (Feedback.external (α := α) (σ := σ) [A] [B]) := by
  intro o p eq
  cases o <;> cases p <;>
    simp only [Feedback.external, Outcome.ret.injEq, Outcome.fault.injEq, reduceCtorEq] at eq ⊢
  case ret.ret i a s j b t =>
    exact ⟨(Fin.eq_zero i).trans (Fin.eq_zero j).symm, eq.2⟩
  case fault.fault => exact eq

private theorem branch_only {f : Feedback.Run [A] [B] α σ} {p q : Point A α σ} {a : Value α} {s : σ}
    (run : f p = branchResult A B a s) :
    Feedback.Step f p q ↔ q = .block 0 a s := by
  constructor
  · intro edge
    cases edge with
    | @branch i b t obs =>
      rw [run] at obs
      obtain ⟨_, rfl, rfl⟩ := Outcome.ret.inj (ordinary_singleton.mp obs)
      rw [Fin.eq_zero i]
  · rintro rfl
    apply Feedback.Step.branch
    rw [run]
    exact ordinary_singleton.mpr rfl

private theorem close_branch {f : Feedback.Run [A] [B] α σ} {p : Point A α σ} {a : Value α} {s : σ}
    (run : f p = branchResult A B a s) :
    Feedback.close f p = Feedback.close f (.block 0 a s) := by
  have top : Feedback.close f p = ⊤ ↔ Feedback.close f (.block 0 a s) = ⊤ := by
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
      exact (not_external_branch (A := A) o a s (ordinary_singleton.mp external)).elim
    · exact (branch_only run).mp edge ▸ out
  · exact fun out => .inr ⟨_, (branch_only run).mpr rfl, out⟩

private theorem close_terminal {f : Feedback.Run [A] [B] α σ} {p : Point A α σ} {o : Outcome [B].length α σ}
    (run : f p = terminalResult A B o) : Feedback.close f p = WithTop.some {o} := by
  have noStep (q) : ¬ Feedback.Step f p q := by
    intro edge
    cases edge with
    | @branch i b s obs =>
      rw [Fin.eq_zero i, run] at obs
      exact not_external_branch (A := A) o b s (ordinary_singleton.mp obs).symm
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

section CertifiedTable

variable {Φ : Type u} [HasTy Φ (Ty κ)] {X : Ty κ}
variable {M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))}
variable {captures points results states : Nat}
variable (C : Carrier M X A B captures points results states)

private def node (p : Fin points) : Point A M.raw.α M.raw.σ :=
  .block 0 (C.invocation p).1.val (C.invocation p).2

private def graphRow : Row points results states → Behaviour ([A] ++ [B]).length M.raw.α M.raw.σ
  | .repeat q => branchResult A B (C.invocation q).1.val (C.invocation q).2
  | .stop (.ret b t) => terminalResult A B (.ret 0 (C.result b).val (C.final t))
  | .stop (.fault t) => terminalResult A B (.fault (C.final t))
  | .stop .diverge => terminalResult A B .diverge
  | .stop .ub => ⊤

variable {f : Feedback.Run [A] [B] M.raw.α M.raw.σ} {rows : Fin points → Row points results states}

private theorem close_stop (p : Fin points) (result : Result results states)
    (run : f (node C p) = graphRow C (.stop result)) :
    Feedback.close f (node C p) = result.behaviour C := by
  cases result with
  | ret | fault | diverge => exact close_terminal run
  | ub => exact Feedback.close_eq_top_iff.mpr ⟨_, .refl, run⟩

private theorem classify_found (bound : Nat) (p : Fin points) (result : Result results states)
    (agrees : ∀ q, f (node C q) = graphRow C (rows q)) (found : search rows bound p = some result) :
    Feedback.close f (node C p) = result.behaviour C := by
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
      exact (close_branch here).trans (ih q tail)

private theorem classify_cycle (p : Fin points) (agrees : ∀ q, f (node C q) = graphRow C (rows q))
    (empty : search rows points p = none) :
    Feedback.close f (node C p) = Result.behaviour C .diverge := by
  let path := fun k => node C (orbit rows p k)
  have atPath (k) : f (path k) = branchResult A B (C.invocation (orbit rows p (k + 1))).1.val
      (C.invocation (orbit rows p (k + 1))).2 := by
    exact (agrees _).trans (congrArg (graphRow C) (repeats_of_exhausted rows p empty k))
  have reachable {q} (reach : Feedback.Reaches f (node C p) q) : ∃ k, q = path k := by
    induction reach with
    | refl => exact ⟨0, congrArg (node C) (orbit_zero rows p).symm⟩
    | tail _ edge ih =>
      obtain ⟨k, rfl⟩ := ih
      exact ⟨k + 1, (branch_only (atPath k)).mp edge⟩
  have safe : ¬ Feedback.ReachesUB f (node C p) := by
    rintro ⟨q, reach, top⟩
    obtain ⟨k, rfl⟩ := reachable reach
    exact WithTop.coe_ne_top (atPath k ▸ top)
  have infinite : Feedback.Infinite f (node C p) :=
    ⟨path, congrArg (node C) (orbit_zero rows p), fun k => (branch_only (atPath k)).mpr rfl⟩
  rw [Feedback.close_of_noUB safe]
  apply congrArg WithTop.some
  ext o
  change (Feedback.Finite f (node C p) o ∨ o = .diverge ∧ Feedback.Infinite f (node C p)) ↔ o = .diverge
  constructor
  · rintro (⟨q, reach, finish⟩ | ⟨eq, _⟩)
    · obtain ⟨k, rfl⟩ := reachable reach
      rw [atPath k] at finish
      exact (not_external_branch (A := A) o _ _ (ordinary_singleton.mp finish)).elim
    · exact eq
  · exact fun eq => .inr ⟨eq, infinite⟩

private theorem label_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have bound : i.val = 0 ∨ i.val = 1 := by omega
  exact bound.imp (fun h => Fin.ext h) (fun h => Fin.ext h)

set_option backward.isDefEq.respectTransparency false in
private theorem preimage_row (row : Row points results states) :
    (row.behaviour C).map (Set.preimage tagIterationOutcome) = graphRow C row := by
  cases row with
  | «repeat» p =>
    apply congrArg WithTop.some
    ext o
    cases o with
    | ret i b t =>
      have label : Feedback.internal [A] [B] 0 = (0 : Fin 2) := rfl
      rcases label_cases i with rfl | rfl <;> simp [tagIterationOutcome, label]
    | fault | diverge => simp [tagIterationOutcome]
  | stop result =>
    cases result with
    | ub => rfl
    | ret b t =>
      apply congrArg WithTop.some
      ext o
      cases o with
      | ret i a s =>
        rcases label_cases i with rfl | rfl <;> simp [tagIterationOutcome, Feedback.external]
      | fault | diverge => simp [tagIterationOutcome, Feedback.external]
    | fault | diverge =>
      apply congrArg WithTop.some
      ext o
      cases o <;> simp [tagIterationOutcome, Feedback.external]

set_option backward.isDefEq.respectTransparency false in
theorem classify (r : Region Φ [A, X] [.coprod B A]) (table : Table captures points results states)
    (certificate : Certified C r table) (c : Fin captures) (p : Fin points) :
    (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 =
      (execute (table c) p).behaviour C := by
  rw [iterateCaptured_run]
  let step := interpretSingleton (M.extend (C.capture c).property) r
  let graph := iterationGraph step (C.invocation p).1
  change Feedback.close graph (.entry (C.invocation p).2) = _
  have entry : graph (.entry (C.invocation p).2) =
      branchResult A B (C.invocation p).1.val (C.invocation p).2 := rfl
  rw [close_branch entry]
  change Feedback.close graph (node C p) = _
  have agrees (q) : graph (node C q) = graphRow C (table c q) := by
    change (step.total 0 (C.invocation q).1.val (C.invocation q).2).map _ = _
    rw [Arrow.total_typed step 0 (C.invocation q).1 (C.invocation q).2]
    change (Shape.denote r ((M.extend (C.capture c).property).extend (C.invocation q).1.property)
      (C.invocation q).2).map _ = _
    rw [certificate c q]
    exact preimage_row C _
  cases found : search (table c) points p with
  | none => simpa [execute, found] using classify_cycle C p agrees found
  | some result => simpa [execute, found] using classify_found C points p result agrees found

end CertifiedTable

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
