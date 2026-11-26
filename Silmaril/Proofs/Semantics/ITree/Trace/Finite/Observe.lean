module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs
import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Explore

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Finite

universe u
variable {Q : Type} {R S : Type u} (step : S → Step Q R S)

private theorem normalize_transition (s : S) :
    normalizeStep (transition step) (transition step s) =
      match step s with
      | .inr next => Part.some (.inr (transition step next))
      | .inl head => Sum.inl <$> head.render (evaluate step) := by
  cases found : step s with
  | inr next => simp [transition, found, normalizeStep, Part.bind_some]
  | inl head =>
    cases head <;> simp [transition, found, normalizeStep, Head.render, Part.bind_some,
      Part.bind_none, Part.map_none, resume, evaluate, Function.comp_def]
    funext reply
    exact pure_bind _ _

private theorem reaches_runs {s : S} {head : Head Q R S}
    (run : Reaches step s head) {node : Visible (Event Q) R (Tree (Event Q) R)}
    (found : node ∈ head.render (evaluate step)) :
    Elgot.Part.Runs (normalizeStep (transition step)) (transition step s) node := by
  induction run with
  | head edge _ =>
    apply Elgot.Part.Runs.done
    rw [normalize_transition, edge]
    change Sum.inl node ∈ Part.map Sum.inl (Head.render (evaluate step) _)
    rw [Part.mem_map_iff]
    exact ⟨node, found, rfl⟩
  | silent edge _ ih =>
    apply Elgot.Part.Runs.more _ (ih found)
    rw [normalize_transition, edge]
    exact Part.mem_some _

private theorem runs_reaches {s : S} {node : Visible (Event Q) R (Tree (Event Q) R)}
    (run : Elgot.Part.Runs (normalizeStep (transition step)) (transition step s) node) :
    ∃ head, Reaches step s head ∧ node ∈ head.render (evaluate step) := by
  generalize equal : transition step s = tree at run
  induction run generalizing s with
  | @done t value present =>
    rw [← equal, normalize_transition] at present
    cases edge : step s with
    | inr next => simp [edge] at present
    | inl head =>
      rw [edge] at present
      simp only [Part.map_eq_map, Part.mem_map_iff] at present
      obtain ⟨visible, has, same⟩ := present
      have nonempty : head ≠ .stop := by
        rintro rfl
        exact Part.notMem_none _ has
      exact ⟨head, .head edge nonempty, Sum.inl.inj same ▸ has⟩
  | @more t next value present _ ih =>
    rw [← equal, normalize_transition] at present
    cases edge : step s with
    | inl head => simp [edge, Part.map_eq_map, Part.mem_map_iff] at present
    | inr target =>
      have same : transition step target = next := by simpa [edge, eq_comm] using present
      obtain ⟨head, reached, has⟩ := ih same
      exact ⟨head, .silent edge reached, has⟩

theorem out_evaluate [DecidableEq S] (states : Finset S) (complete : ∀ s, s ∈ states) (s : S) :
    out (evaluate step s) = (headFrom step states s).render (evaluate step) := by
  rw [evaluate, out_iterate]
  apply Part.ext
  intro node
  rw [Elgot.Part.mem_iter_iff]
  constructor
  · intro run
    obtain ⟨head, reached, has⟩ := runs_reaches step run
    rw [(headFrom_spec step states complete s head).mp reached |>.1]
    exact has
  · intro has
    apply reaches_runs step _ has
    refine (headFrom_spec step states complete s _).mpr ⟨rfl, ?_⟩
    intro stopped
    rw [stopped] at has
    exact Part.notMem_none _ has

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
