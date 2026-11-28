module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot.ITree.Finite

universe u
variable {Q : Type} {Reply : Q → Type} {R S : Type u} [DecidableEq S]

theorem prune_spec (keep : Finset S → S → Bool)
    (candidates : Finset S) :
    prune keep candidates ⊆ candidates ∧
    (∀ s ∈ prune keep candidates, keep (prune keep candidates) s = true) ∧
    ∀ (good : S → Prop), (∀ s, good s → s ∈ candidates) →
      (∀ r, (∀ s, good s → s ∈ r) → ∀ s, good s → keep r s = true) →
      ∀ s, good s → s ∈ prune keep candidates := by
  induction candidates using Finset.strongInductionOn with
  | _ candidates ih =>
    rw [prune.eq_def]
    dsimp only
    split
    · rename_i fixed
      refine ⟨fun _ h => h, ?_, fun _ contained _ => contained⟩
      intro s member
      have present : s ∈ candidates.filter (fun x => keep candidates x = true) := fixed.symm ▸ member
      exact (Finset.mem_filter.mp present).2
    · rename_i changed
      have strict := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset (fun s => keep candidates s = true) candidates, changed⟩
      obtain ⟨contained, stable, maximal⟩ := ih _ strict
      refine ⟨contained.trans (Finset.filter_subset _ _), stable, ?_⟩
      intro good inside preserved
      apply maximal good _ preserved
      intro s hs
      exact Finset.mem_filter.mpr ⟨inside s hs, preserved candidates inside s hs⟩

/-- A finite silent walk to a root with an observation. -/
inductive Reaches (step : S → Step Q R S Reply) : S → Head Q R S Reply → Prop where
  | head {state head} : step state = .inl head → head ≠ .stop → Reaches step state head
  | silent {state next head} : step state = .inr next → Reaches step next head → Reaches step state head

private def LinksBack (step : S → Step Q R S Reply) (remaining : Finset S) (start : S) : Prop :=
  ∀ old, old ∉ remaining → ∃ next, step old = .inr next ∧ (next = start ∨ next ∉ remaining)

private theorem visit {step : S → Step Q R S Reply} {remaining : Finset S} {start next : S}
    (links : LinksBack step remaining start) (edge : step start = .inr next) :
    LinksBack step (remaining.erase start) next := by
  intro old absent
  by_cases same : old = start
  · exact ⟨next, same ▸ edge, Or.inl rfl⟩
  · have previously : old ∉ remaining := fun present => absent (Finset.mem_erase.mpr ⟨same, present⟩)
    obtain ⟨target, found, atStart | known⟩ := links old previously
    · exact ⟨target, found, Or.inr (fun h => (Finset.mem_erase.mp h).1 atStart)⟩
    · exact ⟨target, found, Or.inr (fun h => known (Finset.mem_erase.mp h).2)⟩

omit [DecidableEq S] in
private theorem no_head {step : S → Step Q R S Reply} {remaining : Finset S}
    (closed : ∀ old ∉ remaining, ∃ next ∉ remaining, step old = .inr next)
    {start : S} {head : Head Q R S Reply} (run : Reaches step start head) (absent : start ∉ remaining) : False := by
  induction run with
  | head edge _ =>
    obtain ⟨_, _, jump⟩ := closed _ absent
    rw [edge] at jump
    contradiction
  | silent edge _ ih =>
    obtain ⟨_, outside, jump⟩ := closed _ absent
    rw [edge, Sum.inr.injEq] at jump
    exact ih (jump ▸ outside)

private theorem scan_spec (step : S → Step Q R S Reply) (remaining : Finset S) (start : S)
    (links : LinksBack step remaining start) (head : Head Q R S Reply) :
    Reaches step start head ↔ headFrom step remaining start = head ∧ head ≠ .stop := by
  induction remaining using Finset.strongInductionOn generalizing start with
  | _ remaining ih =>
    rw [headFrom.eq_def]
    by_cases fresh : start ∈ remaining
    · simp only [dite_eq_left fresh]
      cases edge : step start with
      | inl node =>
        constructor
        · intro run
          cases run with
          | head same seen => rw [edge, Sum.inl.injEq] at same; exact ⟨same, seen⟩
          | silent same _ => rw [edge] at same; contradiction
        · rintro ⟨rfl, seen⟩
          exact .head edge seen
      | inr next =>
        rw [← ih _ (Finset.erase_ssubset fresh) next (visit links edge)]
        constructor
        · intro run
          cases run with
          | head same _ => rw [edge] at same; contradiction
          | silent same run =>
            rw [edge, Sum.inr.injEq] at same
            exact same ▸ run
        · exact Reaches.silent edge
    · simp only [dite_eq_right fresh]
      have closed : ∀ old ∉ remaining, ∃ next ∉ remaining, step old = .inr next := by
        intro old seen
        obtain ⟨next, edge, rfl | absent⟩ := links old seen
        · exact ⟨_, fresh, edge⟩
        · exact ⟨next, absent, edge⟩
      exact ⟨fun run => (no_head closed run fresh).elim, fun ⟨equal, seen⟩ => (seen equal.symm).elim⟩

theorem headFrom_spec (step : S → Step Q R S Reply) (states : Finset S)
    (complete : ∀ s, s ∈ states) (s : S) (head : Head Q R S Reply) :
    Reaches step s head ↔ headFrom step states s = head ∧ head ≠ .stop :=
  scan_spec step states s (fun old absent => (absent (complete old)).elim) head

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
