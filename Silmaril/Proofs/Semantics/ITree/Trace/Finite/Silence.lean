module

public import Silmaril.Semantics.ITree.Trace.Finite.Silence.Defs
import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.Semantics.ITree.Trace.Silence.Thms

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Finite

universe u

variable {Q : Type} {R S : Type u}

private theorem stop_reason [DecidableEq S] (step : S → Step Q R S)
    (noStop : ∀ state, step state ≠ .inl .stop) (remaining : Finset S) (state : S)
    (stopped : headFrom step remaining state = .stop) :
    ∃ last, Relation.ReflTransGen (SilentEdge step) state last ∧
      (last ∉ remaining ∨ Relation.TransGen (SilentEdge step) last last) := by
  induction remaining using Finset.strongInductionOn generalizing state with
  | _ remaining ih =>
    rw [headFrom.eq_def] at stopped
    by_cases fresh : state ∈ remaining
    · simp only [dite_eq_left fresh] at stopped
      cases checked : step state with
      | inl head =>
        have same : head = .stop := by simpa only [checked] using stopped
        exact (noStop state (same ▸ checked)).elim
      | inr next =>
        have tail : headFrom step (remaining.erase state) next = .stop := by
          simpa only [checked] using stopped
        obtain ⟨last, path, absent | cycle⟩ := ih _ (Finset.erase_ssubset fresh) next tail
        · by_cases remains : last ∈ remaining
          · have seen : last = state := by
              by_contra unequal
              exact absent (Finset.mem_erase.mpr ⟨unequal, remains⟩)
            subst last
            exact ⟨state, .refl, Or.inr (Relation.TransGen.head' checked path)⟩
          · exact ⟨last, Relation.ReflTransGen.head checked path, Or.inl remains⟩
        · exact ⟨last, Relation.ReflTransGen.head checked path, Or.inr cycle⟩
    · exact ⟨state, .refl, Or.inl fresh⟩

theorem stop_has_cycle [DecidableEq S] (step : S → Step Q R S) (states : Finset S)
    (complete : ∀ state, state ∈ states) (noStop : ∀ state, step state ≠ .inl .stop) (state : S)
    (stopped : headFrom step states state = .stop) :
    ∃ last, Relation.ReflTransGen (SilentEdge step) state last ∧
      Relation.TransGen (SilentEdge step) last last := by
  obtain ⟨last, path, cause⟩ := stop_reason step noStop states state stopped
  exact ⟨last, path, cause.resolve_left (fun absent => absent (complete last))⟩

private theorem ask_eq_iff (left right : Q) :
    Event.ask (Reply := fun _ => Bool) left = Event.ask (Reply := fun _ => Bool) right ↔ left = right :=
  ⟨congrArg (fun (event : Event Q (fun _ => Bool) Bool) => match event with | .ask key => key),
    congrArg (Event.ask (Reply := fun _ => Bool))⟩

private theorem silent_cons {tree : Tree (Event Q) R} {run : S → Tree (Event Q) R}
    {head : Head Q R S} (observed : out tree = head.render run)
    (key : Q) (reply : Bool) (tail : ExchangePath (Event Q)) :
    SilentAfter tree (.cons (.ask key) reply tail) ↔
      ∃ next, head = .request key next ∧ SilentAfter (run (next reply)) tail := by
  cases head <;> simp [SilentAfter, observed, Head.render, Visible.vis.injEq, ask_eq_iff, Function.comp_def]

theorem silent_after_exact [DecidableEq S] [DecidableEq Q]
    (step : S → Step Q R S) (states : Finset S) (complete : ∀ s, s ∈ states)
    (state : S) (path : ExchangePath (Event Q)) :
    silentAfter? step states state path = true ↔ SilentAfter (evaluate step state) path := by
  induction path generalizing state with
  | nil =>
    have observed := Silmaril.Elgot.ITree.Finite.out_evaluate step states complete state
    cases normalized : headFrom step states state <;>
      simp [silentAfter?, normalized, SilentAfter, observed, Head.render]
  | cons event reply tail ih =>
    cases event with
    | ask key =>
      rw [silent_cons (Silmaril.Elgot.ITree.Finite.out_evaluate step states complete state)]
      cases normalized : headFrom step states state with
      | stop | result _ => simp [silentAfter?, normalized]
      | request actual next =>
        by_cases same : actual = key <;> simp [silentAfter?, normalized, same, ih]

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
