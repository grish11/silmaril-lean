module

public import Silmaril.Semantics.Region.Queries.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Queries.Proofs
universe u v w x
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x}
variable {T : TransitionSystem S L Ev Stop} {U : L → Prop}

theorem exit_outside {s t : S} {es : List Ev} (h : FirstExit T U s es t) : ¬ U (T.pc t) := by
  induction h with
  | leave _ _ outside => exact outside
  | step _ _ _ ih => exact ih

theorem inside_end {s t : S} {es : List Ev} (path : Inside T U s es t) : U (T.pc t) := by
  induction path with
  | refl h => exact h
  | step _ _ _ ih => exact ih

theorem inside_snoc {s t f : S} {es tail : List Ev} (path : Inside T U s es t)
    (edge : T.step t tail f) (inside : U (T.pc f)) : Inside T U s (es ++ tail) f := by
  induction path with
  | refl h => simpa using Inside.step h edge (Inside.refl inside)
  | step hu edge₀ rest ih => simpa only [List.append_assoc] using Inside.step hu edge₀ (ih edge)

theorem exit_of_finishes {s : S} (inside : U (T.pc s)) (finish : Finishes T U s)
    (halts : noHalts T U s) : ∃ es t, FirstExit T U s es t := by
  have go : ∀ t, Acc (fun y x => U (T.pc x) ∧ U (T.pc y) ∧ ∃ es, T.step x es y) t →
      ∀ pre, Inside T U s pre t → ∃ es f, FirstExit T U t es f := by
    intro t acc
    induction acc with
    | intro t next ih =>
      intro pre path
      have ht := inside_end path
      rcases finish.2 pre t path with ⟨k, hk⟩ | ⟨tail, f, edge⟩
      · exact (halts pre t path k hk).elim
      · by_cases hf : U (T.pc f)
        · obtain ⟨rest, last, exits⟩ := ih f ⟨ht, hf, tail, edge⟩ (pre ++ tail) (inside_snoc path edge hf)
          exact ⟨tail ++ rest, last, .step ht edge exits⟩
        · exact ⟨tail, f, .leave ht edge hf⟩
  exact go s finish.1 [] (.refl inside)

theorem must_may {target : S → L → Prop} {s : S} (h : mustWP T U target s) : mayWP T U target s := by
  obtain ⟨es, t, exits⟩ := exit_of_finishes h.1 h.2.2.1 h.2.2.2
  exact ⟨es, t, exits, h.2.1 es t exits⟩

end Silmaril.Semantics.Region.Queries.Proofs
