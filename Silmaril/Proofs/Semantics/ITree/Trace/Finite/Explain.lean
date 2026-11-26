module

public import Silmaril.Semantics.ITree.Trace.Finite.Explain.Defs
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Compare
import Silmaril.Semantics.ITree.Trace.Finite.Thms

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Finite

universe u v

private theorem pruneExplain_spec {P : Type u} {W : Type v} [DecidableEq P]
    (keep : Finset P → P → Bool) (reason : (P → Option W) → P → Option W)
    (valid : P → W → Prop)
    (kept : ∀ candidates previous, (∀ p, previous p = none ↔ p ∈ candidates) →
      ∀ p, reason previous p = none ↔ keep candidates p = true)
    (sound : ∀ previous, (∀ p w, previous p = some w → valid p w) →
      ∀ p w, reason previous p = some w → valid p w)
    (candidates : Finset P) (previous : P → Option W)
    (known : ∀ p, previous p = none ↔ p ∈ candidates)
    (prior : ∀ p w, previous p = some w → valid p w) :
    (∀ p, pruneExplain keep reason candidates previous p = none ↔ p ∈ prune keep candidates) ∧
    ∀ p w, pruneExplain keep reason candidates previous p = some w → valid p w := by
  induction candidates using Finset.strongInductionOn generalizing previous with
  | _ candidates ih =>
    rw [pruneExplain.eq_def, prune.eq_def]
    dsimp only
    split
    · exact ⟨known, prior⟩
    · rename_i different
      have strict := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, different⟩
      apply ih _ strict _ ?_ ?_
      · intro p
        by_cases old : p ∈ candidates
        · by_cases new : p ∈ candidates.filter (fun x => keep candidates x = true)
          · simp [old, new, known]
          · have failed : keep candidates p ≠ true := fun pass => new (Finset.mem_filter.mpr ⟨old, pass⟩)
            simp [old, new, kept candidates previous known, failed]
        · have new : p ∉ candidates.filter (fun x => keep candidates x = true) :=
            fun h => old (Finset.mem_filter.mp h).1
          simp [old, new, known]
      · intro p w found
        split at found
        · exact sound previous prior p w found
        · exact prior p w found

variable {Q : Type} {Reply : Q → Type} {R S T : Type u}

variable
  [DecidableEq S] [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]

private theorem explainHead_none (replies : ∀ key, List (Reply key))
    (complete : ∀ key (r : Reply key), r ∈ replies key)
    (pairs : Finset (S × T)) (previous : S × T → Option (Trace (Event Q Reply) R))
    (known : ∀ p, previous p = none ↔ p ∈ pairs)
    (left : Head Q R S Reply) (right : Head Q R T Reply) :
    explainHead replies previous left right = none ↔ compatible pairs left right = true := by
  cases left <;> cases right <;> simp only [explainHead, compatible, reduceCtorEq, iff_self]
  · rename_i left right
    by_cases same : left = right <;> simp [same]
  · rename_i l nextL r nextR
    by_cases same : l = r
    · subst r
      simp only [dite_true, List.findSome?_eq_none_iff, Option.map_eq_none_iff, known, decide_eq_true_eq]
      exact ⟨fun found reply => found reply (complete l reply), fun pass reply _ => pass reply⟩
    · simp [same]

omit [DecidableEq S] [DecidableEq T] [∀ key, Fintype (Reply key)] in
private theorem explainHead_sound (replies : ∀ key, List (Reply key))
    {runL : S → Tree (Event Q Reply) R} {runR : T → Tree (Event Q Reply) R}
    (previous : S × T → Option (Trace (Event Q Reply) R))
    (prior : ∀ s t trace, previous (s, t) = some trace → HasTrace (runL s) trace ∧ ¬ HasTrace (runR t) trace)
    {treeL treeR : Tree (Event Q Reply) R} {left : Head Q R S Reply} {right : Head Q R T Reply}
    (observedL : out treeL = left.render runL) (observedR : out treeR = right.render runR)
    {trace : Trace (Event Q Reply) R} (found : explainHead replies previous left right = some trace) :
    HasTrace treeL trace ∧ ¬ HasTrace treeR trace := by
  have result (value : R) (hl : left = .result value) (hr : right ≠ .result value) :
      HasTrace treeL (.result value) ∧ ¬ HasTrace treeR (.result value) :=
    ⟨(result_trace observedL value).mpr hl, fun seen => hr ((result_trace observedR value).mp seen)⟩
  have request (key : Q) (hl : ∃ next, left = .request key next) (hr : ¬ ∃ next, right = .request key next) :
      HasTrace treeL (.request (.ask key)) ∧ ¬ HasTrace treeR (.request (.ask key)) :=
    ⟨(request_trace observedL key).mpr hl, fun seen => hr ((request_trace observedR key).mp seen)⟩
  cases left with
  | stop => simp [explainHead] at found
  | result value =>
    cases right with
    | result other =>
      by_cases same : value = other
      · simp [explainHead, same] at found
      · have eq : .result value = trace := by simpa [explainHead, same] using found
        subst trace
        exact result value rfl (by simpa [eq_comm] using same)
    | stop | request _ _ =>
      have eq : .result value = trace := Option.some.inj found
      subst trace
      exact result value rfl (by simp)
  | request key nextL =>
    cases right with
    | stop | result _ =>
      have eq : .request (.ask key) = trace := Option.some.inj found
      subst trace
      exact request key ⟨nextL, rfl⟩ (by simp)
    | request actual nextR =>
      by_cases same : key = actual
      · subst actual
        simp only [explainHead, dite_true] at found
        obtain ⟨reply, _, hit⟩ := List.exists_of_findSome?_eq_some found
        obtain ⟨tail, stored, rfl⟩ := Option.map_eq_some_iff.mp hit
        obtain ⟨has, lacks⟩ := prior _ _ tail stored
        exact ⟨(exchange_at nextL observedL reply tail).mpr has,
          fun seen => lacks ((exchange_at nextR observedR reply tail).mp seen)⟩
      · have eq : .request (.ask key) = trace := by simpa [explainHead, same] using found
        subst trace
        exact request key ⟨nextL, rfl⟩ (by simp [Head.request.injEq, eq_comm, same])

theorem explain_spec (replies : ∀ key, List (Reply key))
    (complete : ∀ key (reply : Reply key), reply ∈ replies key)
    (statesL : Finset S) (statesR : Finset T) (completeL : ∀ s, s ∈ statesL)
    (completeR : ∀ t, t ∈ statesR) (left : S → Step Q R S Reply) (right : T → Step Q R T Reply)
    (s : S) (t : T) :
    (explain replies statesL statesR left right s t = none ↔ compare statesL statesR left right s t = true) ∧
    ∀ trace, explain replies statesL statesR left right s t = some trace →
      HasTrace (evaluate left s) trace ∧ ¬ HasTrace (evaluate right t) trace := by
  let keep (pairs : Finset (S × T)) (p : S × T) :=
    compatible pairs (headFrom left statesL p.1) (headFrom right statesR p.2)
  let reason previous (p : S × T) :=
    explainHead replies previous (headFrom left statesL p.1) (headFrom right statesR p.2)
  let valid (p : S × T) trace := HasTrace (evaluate left p.1) trace ∧ ¬ HasTrace (evaluate right p.2) trace
  have spec := pruneExplain_spec keep reason valid
    (fun candidates previous known p => explainHead_none replies complete candidates previous known _ _)
    (fun previous prior p trace found => explainHead_sound replies previous (fun s t => prior (s, t))
      (out_evaluate left statesL completeL p.1) (out_evaluate right statesR completeR p.2) found)
    (statesL ×ˢ statesR) (fun _ => none)
    (fun p => iff_of_true rfl (Finset.mem_product.mpr ⟨completeL p.1, completeR p.2⟩))
    (fun _ _ h => by cases h)
  exact ⟨(spec.1 (s, t)).trans (by simp [Finite.compare, keep]), spec.2 (s, t)⟩

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
