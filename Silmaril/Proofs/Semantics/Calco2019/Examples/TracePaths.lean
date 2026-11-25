module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Paths.Defs

public section

universe u v w

namespace Silmaril.Calco2019.Examples.Printing.PathProofs

variable {A : Type u} {X : Type v} {Y : Type w}

private theorem fold_cons_lt (word : List A) (stream : ℕ → A) (k : ℕ)
    (hk : k < word.length) : word.foldr cons stream k = word[k] := by
  induction word generalizing k with
  | nil => simp at hk
  | cons a word ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)

private theorem fold_cons_ge (word : List A) (stream : ℕ → A) (k : ℕ)
    (hk : word.length ≤ k) : word.foldr cons stream k = stream (k - word.length) := by
  induction word generalizing k with
  | nil => simp
  | cons a word ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      simpa only [List.foldr_cons, cons, List.length_cons, Nat.succ_sub_succ_eq_sub] using
        ih k (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hk)

theorem chunk_unfold (word : ℕ → List A) (productive : ∀ i, 0 < (word i).length) (i : ℕ) :
    chunkStream word productive i = (word i).foldr cons (chunkStream word productive (i + 1)) := by
  funext k
  rw [chunkStream]
  split
  · rename_i hk
    exact (fold_cons_lt _ _ _ hk).symm
  · rename_i hk
    exact (fold_cons_ge _ _ _ (Nat.le_of_not_gt hk)).symm

private theorem chunk_unique (word : ℕ → List A) (productive : ∀ i, 0 < (word i).length)
    (streams : ℕ → ℕ → A) (hs : ∀ i, streams i = (word i).foldr cons (streams (i + 1))) :
    streams = chunkStream word productive := by
  funext i k
  induction k using Nat.strong_induction_on generalizing i with
  | ind k ih =>
    have hstream := congrFun (hs i) k
    rw [hstream, chunkStream]
    split
    · rename_i hk
      exact fold_cons_lt _ _ _ hk
    · rename_i hk
      rw [fold_cons_ge _ _ _ (Nat.le_of_not_gt hk)]
      exact ih _ (by have := productive i; omega) (i + 1)

variable {f : X → Set (Trace A (Y ⊕ X))}

theorem finite_sound {x : X} {t : Trace A Y} (h : FiniteTraceRun f x t) :
    t ∈ greatestTrace f x := by
  induction h with
  | @returns x word y edge =>
    rw [← greatestTrace_fix]
    exact Or.inl ⟨word, y, edge, rfl⟩
  | @streams x stream edge =>
    rw [← greatestTrace_fix]
    exact Or.inr (Or.inl ⟨stream, edge, rfl⟩)
  | @next x x' word tail edge _ ih =>
    rw [← greatestTrace_fix]
    exact Or.inr (Or.inr ⟨word, x', tail, edge, ih, rfl⟩)

theorem infinite_sound {x : X} (p : InfiniteTracePath f x) (hf : TraceGuarded f) :
    Sum.inr (p.stream hf) ∈ greatestTrace f x := by
  let s := chunkStream p.word (p.productive hf)
  let g : X → Set (Trace A Y) := fun x => {t | ∃ i, p.state i = x ∧ t = .inr (s i)}
  have hg : g ≤ traceStep f g := by
    intro x t ht
    obtain ⟨i, rfl, rfl⟩ := ht
    exact Or.inr (Or.inr ⟨p.word i, p.state (i + 1), .inr (s (i + 1)), p.edge i,
      ⟨i + 1, rfl, rfl⟩, congrArg Sum.inr (chunk_unfold _ _ _)⟩)
  exact le_greatestTrace f hg x ⟨0, p.start, rfl⟩

theorem finite_complete (hf : TraceGuarded f) {x : X} {word : List A} {y : Y}
    (h : Sum.inl (word, y) ∈ greatestTrace f x) : FiniteTraceRun f x (.inl (word, y)) := by
  generalize hlen : word.length = n
  induction n using Nat.strong_induction_on generalizing x word with
  | ind n ih =>
    rw [← greatestTrace_fix] at h
    rcases h with ⟨w, z, he, heq⟩ | ⟨s, hs, heq⟩ | ⟨w, x', tail, he, ht, heq⟩
    · cases heq
      exact .returns he
    · cases heq
    · cases tail with
      | inr s => cases heq
      | inl pair =>
        obtain ⟨suffix, z⟩ := pair
        change Sum.inl (word, y) = Sum.inl (w ++ suffix, z) at heq
        cases heq
        refine .next he (ih suffix.length ?_ ht rfl)
        have hpos := List.length_pos_iff.mpr (hf _ _ _ he)
        simp only [List.length_append] at hlen
        omega

private theorem next_of_noFinite (x : X) (t : Trace A Y)
    (hm : t ∈ greatestTrace f x) (hn : ¬ FiniteTraceRun f x t) :
    ∃ word x' tail, Sum.inl (word, Sum.inr x') ∈ f x ∧ tail ∈ greatestTrace f x' ∧
      ¬ FiniteTraceRun f x' tail ∧ t = prepend word tail := by
  rw [← greatestTrace_fix] at hm
  rcases hm with ⟨word, y, edge, rfl⟩ | ⟨stream, edge, rfl⟩ | ⟨word, x', tail, edge, hit, rfl⟩
  · exact (hn (.returns edge)).elim
  · exact (hn (.streams edge)).elim
  · exact ⟨word, x', tail, edge, hit, fun h => hn (.next edge h), rfl⟩

theorem infinite_complete (hf : TraceGuarded f) {x : X} {t : Trace A Y}
    (hm : t ∈ greatestTrace f x) (hn : ¬ FiniteTraceRun f x t) :
    ∃ p : InfiniteTracePath f x, t = Sum.inr (p.stream hf) := by
  classical
  let Node := {xt : X × Trace A Y // xt.2 ∈ greatestTrace f xt.1 ∧ ¬ FiniteTraceRun f xt.1 xt.2}
  let edge (a : Node) := next_of_noFinite a.1.1 a.1.2 a.2.1 a.2.2
  let word (a : Node) := (edge a).choose
  let advance (a : Node) : Node :=
    ⟨((edge a).choose_spec.choose, (edge a).choose_spec.choose_spec.choose),
      (edge a).choose_spec.choose_spec.choose_spec.2.1,
      (edge a).choose_spec.choose_spec.choose_spec.2.2.1⟩
  let node : ℕ → Node := fun i => (advance^[i]) ⟨(x, t), hm, hn⟩
  have node_next (i : ℕ) : node (i + 1) = advance (node i) := Function.iterate_succ_apply' _ _ _
  let p : InfiniteTracePath f x :=
    {state := fun i => (node i).1.1
     word := fun i => word (node i)
     start := rfl
     edge := fun i => by
       change Sum.inl (word (node i), Sum.inr (node (i + 1)).1.1) ∈ f (node i).1.1
       rw [node_next]
       exact (edge (node i)).choose_spec.choose_spec.choose_spec.1}
  have hstream (i : ℕ) : ∃ s : ℕ → A, (node i).1.2 = Sum.inr s := by
    cases he : (node i).1.2 with
    | inl a =>
      obtain ⟨word, y⟩ := a
      have hit := (node i).2.1
      rw [he] at hit
      exact ((node i).2.2 (he ▸ finite_complete hf hit)).elim
    | inr s => exact ⟨s, rfl⟩
  let s (i : ℕ) := (hstream i).choose
  have observe (i : ℕ) : (node i).1.2 = Sum.inr (s i) := (hstream i).choose_spec
  have unfold_s (i : ℕ) : s i = (p.word i).foldr cons (s (i + 1)) := by
    have he : (node i).1.2 = prepend (p.word i) (node (i + 1)).1.2 := by
      rw [node_next]
      exact (edge (node i)).choose_spec.choose_spec.choose_spec.2.2.2
    rw [observe, observe] at he
    exact Sum.inr.inj he
  refine ⟨p, ?_⟩
  have h := congrFun (chunk_unique p.word (p.productive hf) s unfold_s) 0
  exact (observe 0).trans (congrArg Sum.inr h)

theorem greatest_nonempty (hf : TraceGuarded f) (hbody : ∀ x, (f x).Nonempty) (x : X) :
    (greatestTrace f x).Nonempty := by
  classical
  by_cases ht : ∃ t, FiniteTraceRun f x t
  · obtain ⟨t, h⟩ := ht
    exact ⟨t, finite_sound h⟩
  · let Node := {x : X // ¬ ∃ t, FiniteTraceRun f x t}
    have next (a : Node) : ∃ (word : List A) (b : Node), Sum.inl (word, Sum.inr b.1) ∈ f a.1 := by
      obtain ⟨t, hit⟩ := hbody a.1
      cases t with
      | inr s => exact (a.2 ⟨_, .streams hit⟩).elim
      | inl pair =>
        obtain ⟨word, y | x'⟩ := pair
        · exact (a.2 ⟨_, .returns hit⟩).elim
        · exact ⟨word, ⟨x', fun ⟨_, h⟩ => a.2 ⟨_, .next hit h⟩⟩, hit⟩
    let advance (a : Node) : Node := (next a).choose_spec.choose
    let node : ℕ → Node := fun i => (advance^[i]) ⟨x, ht⟩
    have node_next (i : ℕ) : node (i + 1) = advance (node i) := Function.iterate_succ_apply' _ _ _
    let p : InfiniteTracePath f x :=
      {state := fun i => (node i).1
       word := fun i => (next (node i)).choose
       start := rfl
       edge := fun i => by
         change Sum.inl ((next (node i)).choose, Sum.inr (node (i + 1)).1) ∈ f (node i).1
         rw [node_next]
         exact (next (node i)).choose_spec.choose_spec}
    exact ⟨_, infinite_sound p hf⟩

theorem greatest_iff (hf : TraceGuarded f) (x : X) (t : Trace A Y) :
    t ∈ greatestTrace f x ↔ FiniteTraceRun f x t ∨
      ∃ p : InfiniteTracePath f x, t = Sum.inr (p.stream hf) := by
  constructor
  · intro hm
    by_cases hn : FiniteTraceRun f x t
    · exact Or.inl hn
    · exact Or.inr (infinite_complete hf hm hn)
  · rintro (h | ⟨p, rfl⟩)
    · exact finite_sound h
    · exact infinite_sound p hf

private theorem letter_finite (a : A) {x : Unit} {t : Trace A Unit}
    (h : FiniteTraceRun (traceLoop a) x t) : t ∈ finiteSolution a x := by
  induction h with
  | @returns x word y edge =>
    cases y
    have hw : word = [] := by simpa [traceLoop] using edge
    subst word
    exact ⟨0, rfl⟩
  | @streams x stream edge => simp [traceLoop] at edge
  | @next x x' word tail edge _ ih =>
    cases x'
    have hw : word = [a] := by simpa [traceLoop] using edge
    subst word
    obtain ⟨n, rfl⟩ := ih
    exact ⟨n + 1, rfl⟩

theorem greatest_letter_trace (a : A) : greatestTrace (traceLoop a) = productiveSolution a := by
  apply le_antisymm _ (le_greatestTrace _ (productive_fixpoint a).ge)
  intro x t ht
  rcases (greatest_iff (traceLoop_guarded a) x t).1 ht with h | ⟨p, rfl⟩
  · exact Or.inr (letter_finite a h)
  · left
    have hw (i : ℕ) : p.word i = [a] := by
      have edge := p.edge i
      have hu : p.state (i + 1) = () := Subsingleton.elim _ _
      rw [hu] at edge
      simpa [traceLoop] using edge
    have hletter (i k : ℕ) : chunkStream p.word (p.productive (traceLoop_guarded a)) i k = a := by
      induction k generalizing i with
      | zero =>
        have he := congrFun (chunk_unfold p.word (p.productive (traceLoop_guarded a)) i) 0
        rw [hw i] at he
        exact he
      | succ k ih =>
        have he := congrFun (chunk_unfold p.word (p.productive (traceLoop_guarded a)) i) (k + 1)
        rw [hw i] at he
        exact he.trans (ih (i + 1))
    exact congrArg Sum.inr (funext (hletter 0))

end Silmaril.Calco2019.Examples.Printing.PathProofs
