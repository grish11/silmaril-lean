module

public import Silmaril.Games.Abstract.StratOps.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms
public import Silmaril.Games.Abstract.FunctionIter.Defs

/-!
# Call prefixes of an iteration of a total body (proofs)

For a loop body `T : ObsTriple E S A (B ⊕ A)`, the call prefixes `satP (iterT T)` are computed
in terms of those of `T`:

* `exists_contChain_of_satP_iterT` (no hypothesis): a call prefix of `iterT T` is a finite
  chain of continuing iterations (`FullFun.ContChain`) followed by a call prefix of `T`. A call
  prefix inside the log of the chain is a call prefix of the continuing return it falls in;
  a call prefix of an infinite chain of continuing iterations falls in finitely many of them;
* `total_iterT`: iteration preserves totality (`StratOps.Total`). This is the dependent-choice
  argument: from a point where `iterT T` has no observation, `T` only returns continuing to
  points where `iterT T` has no observation either, so choosing such returns gives an infinite
  chain of continuing iterations. Its logs are eventually empty (a spin divergence of
  `iterT T` after finitely many iterations) or infinitely often nonempty (a productive stream
  of `iterT T`, `Shape.exists_streamConcat`), a contradiction either way;
* `satP_iterT_of_satP`: when `iterT T` is total, every call prefix of `T` is one of `iterT T`.
  A call prefix forced by a continuing return of `T` is extended by an observation of
  `iterT T` at the point it continues to;
* `satP_iterT_of_contChain`: call prefixes of `iterT T` after a continuing chain are call
  prefixes of `iterT T`, the log of the chain in front.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter3

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Streams and call prefixes -/

section Stream

variable {α : Type u}

theorem append_get_lt (c : List α) (ω : Nat → α) {n : Nat} (h : n < c.length) :
    (c ++ₛ ω) n = c[n] := by
  induction c generalizing n with
  | nil => simp at h
  | cons x c ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih (by simpa using h)

theorem append_get_ge (c : List α) (ω : Nat → α) (n : Nat) :
    (c ++ₛ ω) (c.length + n) = ω n := by
  induction c with
  | nil => simp [Stream'.appendStream']
  | cons x c ih =>
    rw [List.length_cons, Nat.add_right_comm]
    exact ih

theorem streamTake_append (c : List α) (ω : Nat → α) (k : Nat) :
    streamTake (c ++ₛ ω) (c.length + k) = c ++ streamTake ω k := by
  apply List.ext_getElem (by simp [streamTake])
  intro i h₁ h₂
  simp only [streamTake, List.getElem_ofFn]
  rcases Nat.lt_or_ge i c.length with h | h
  · rw [append_get_lt c ω h, List.getElem_append_left h]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [append_get_ge, List.getElem_append_right (by omega)]
    simp

theorem streamTake_of_prefix {L : List α} {ω : Nat → α} (h : Shape.StreamPrefix L ω) {k : Nat}
    (hk : k ≤ L.length) : streamTake ω k = L.take k := by
  apply List.ext_getElem (by simp [streamTake]; omega)
  intro i h₁ h₂
  simp only [streamTake, List.getElem_ofFn, List.getElem_take]
  exact h i (by simp [streamTake] at h₁; omega)

theorem streamPrefix_append (c : List α) (ω : Nat → α) : Shape.StreamPrefix c (c ++ₛ ω) :=
  fun _ h => append_get_lt c ω h

theorem flatMap_range_succ (l : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap l = l 0 ++ (List.range n).flatMap fun i => l (i + 1) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem streamPrefix_append_append {c L : List α} {ω : Nat → α}
    (h : Shape.StreamPrefix L ω) : Shape.StreamPrefix (c ++ L) (c ++ₛ ω) := by
  intro i hi
  by_cases hc : i < c.length
  · rw [append_get_lt c ω hc, List.getElem_append_left hc]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hc)
    rw [append_get_ge, List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact h j (by simp only [List.length_append] at hi; omega)

/-- A concatenated stream with one more segment in front. -/
theorem streamConcat_cons {l : Nat → List α} {ω : Nat → α}
    (h : Shape.StreamConcat (fun n => l (n + 1)) ω) : Shape.StreamConcat l (l 0 ++ₛ ω) := by
  refine ⟨fun n => ?_, fun N => ?_⟩
  · cases n with
    | zero => intro i hi; simp at hi
    | succ n => rw [flatMap_range_succ]; exact streamPrefix_append_append (h.1 n)
  · obtain ⟨n, hn⟩ := h.2 N
    exact ⟨n + 1, by rw [flatMap_range_succ, List.length_append]; omega⟩

end Stream

theorem callPre_append_right {c c₁ : List (Call E)} {m : E.Op} (h : CallPre c m c₁)
    (c₂ : List (Call E)) : CallPre c m (c₁ ++ c₂) := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨n, c' ++ c₂, by simp⟩

theorem callPre_append_left {c c₂ : List (Call E)} {m : E.Op} (c₁ : List (Call E))
    (h : CallPre c m c₂) : CallPre (c₁ ++ c) m (c₁ ++ c₂) := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨n, c', by simp⟩

theorem callPre_append {c c₁ c₂ : List (Call E)} {m : E.Op} (h : CallPre c m (c₁ ++ c₂)) :
    CallPre c m c₁ ∨ ∃ c₃, c = c₁ ++ c₃ ∧ CallPre c₃ m c₂ := by
  obtain ⟨n, c', h⟩ := h
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, rfl⟩ | ⟨c'', rfl, h'⟩
  · exact .inr ⟨a', rfl, n, c', rfl⟩
  · cases c'' with
    | nil =>
      simp only [List.nil_append] at h'
      exact .inr ⟨[], by simp, n, c', h'.symm⟩
    | cons y c'' =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 h'
      exact .inl ⟨n, c'', rfl⟩

theorem not_callPre_nil {c : List (Call E)} {m : E.Op} : ¬ CallPre c m [] := by
  rintro ⟨n, c', h⟩
  simp at h

/-- The position `k` of a stream with a prefix `L` longer than `k` is a call prefix of `L`. -/
theorem callPre_of_streamPrefix {L : List (Call E)} {ω : Nat → Call E}
    (h : Shape.StreamPrefix L ω) {k : Nat} (hk : k < L.length) :
    CallPre (streamTake ω k) (ω k).1 L := by
  rw [streamTake_of_prefix h hk.le, h k hk]
  exact ⟨L[k].2, L.drop (k + 1), by rw [List.getElem_cons_drop, List.take_append_drop]⟩

theorem beh_satP {X : ObsTriple E S A B} {s : S} {a : A} {d c : List (Call E)} {e : End S B}
    {m : E.Op} (h : (d, e) ∈ X.1 s a) (hc : CallPre c m d) : (c, m) ∈ satP X s a :=
  .inr (.inr (.inl ⟨d, e, h, hc⟩))

/-! ## Iteration -/

section Iter

variable {T : ObsTriple E S A (B ⊕ A)}

theorem contChain_trans {s a c₁ s' a' c₂ s'' a''} (h₁ : FullFun.ContChain T.1 s a c₁ s' a')
    (h₂ : FullFun.ContChain T.1 s' a' c₂ s'' a'') :
    FullFun.ContChain T.1 s a (c₁ ++ c₂) s'' a'' := by
  induction h₁ with
  | refl => simpa using h₂
  | step h _ ih => rw [List.append_assoc]; exact .step h (ih h₂)

theorem contChain_single {s a c s' a'} (h : (c, End.ret (.inr a') s') ∈ T.1 s a) :
    FullFun.ContChain T.1 s a c s' a' := by
  simpa using FullFun.ContChain.step h .refl

/-- The first `n` returns of an infinite chain of continuing iterations. -/
theorem contChain_of_seq {σ : ℕ → S × A} {l : ℕ → List (Call E)}
    (hσ : ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ T.1 (σ n).1 (σ n).2) :
    ∀ n, FullFun.ContChain T.1 (σ 0).1 (σ 0).2 ((List.range n).flatMap l) (σ n).1 (σ n).2
  | 0 => by simpa using (FullFun.ContChain.refl : FullFun.ContChain T.1 (σ 0).1 (σ 0).2 [] _ _)
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append]
    simpa using contChain_trans (contChain_of_seq hσ n) (contChain_single (hσ n))

/-! ### Call prefixes of an iteration -/

theorem exists_of_contChain_callPre {s a c₁ s' a'} (h : FullFun.ContChain T.1 s a c₁ s' a')
    {c : List (Call E)} {m : E.Op} (hc : CallPre c m c₁) :
    ∃ c₁ s' a' c₂, FullFun.ContChain T.1 s a c₁ s' a' ∧ (c₂, m) ∈ satP T s' a' ∧
      c = c₁ ++ c₂ := by
  induction h generalizing c with
  | refl => exact (not_callPre_nil hc).elim
  | step h₁ _ ih =>
    rcases callPre_append hc with hc' | ⟨c₃, rfl, hc'⟩
    · exact ⟨[], _, _, c, .refl, beh_satP h₁ hc', rfl⟩
    · obtain ⟨c₁', s'', a'', c₂, hch, hm, rfl⟩ := ih hc'
      exact ⟨_, s'', a'', c₂, .step h₁ hch, hm, by rw [List.append_assoc]⟩

theorem exists_of_iterBeh_callPre {s a} {y : CallBeh E S B} (h : AFun.IterBeh T.1 s a y)
    {c : List (Call E)} {m : E.Op} (hc : CallPre c m y.1) :
    ∃ c₁ s' a' c₂, FullFun.ContChain T.1 s a c₁ s' a' ∧ (c₂, m) ∈ satP T s' a' ∧
      c = c₁ ++ c₂ := by
  induction h generalizing c with
  | exit h => exact ⟨[], _, _, c, .refl, beh_satP h hc, rfl⟩
  | trap h => exact ⟨[], _, _, c, .refl, beh_satP h hc, rfl⟩
  | div h => exact ⟨[], _, _, c, .refl, beh_satP h hc, rfl⟩
  | step h₁ _ ih =>
    rcases callPre_append hc with hc' | ⟨c₃, rfl, hc'⟩
    · exact ⟨[], _, _, c, .refl, beh_satP h₁ hc', rfl⟩
    · obtain ⟨c₁', s'', a'', c₂, hch, hm, rfl⟩ := ih hc'
      exact ⟨_, s'', a'', c₂, .step h₁ hch, hm, by rw [List.append_assoc]⟩
  | spin _ _ _ => exact (not_callPre_nil hc).elim

/-- **Call prefixes of an iteration**, one inclusion, with no hypothesis: a finite chain of
continuing iterations, then a call prefix of the body. -/
theorem exists_contChain_of_satP_iterT {s : S} {a : A} {c : List (Call E)} {m : E.Op}
    (h : (c, m) ∈ satP (iterT T) s a) :
    ∃ c₁ s' a' c₂, FullFun.ContChain T.1 s a c₁ s' a' ∧ (c₂, m) ∈ satP T s' a' ∧
      c = c₁ ++ c₂ := by
  rcases h with ⟨c₁, s', a', c₂, m', hch, hp, he⟩ |
      ⟨d, m', ⟨c₁, s', a', c₂, m'', hch, hp, he⟩, hc⟩ | ⟨d, e, hb, hc⟩ |
      ⟨ω, hω, k, hk, hm⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨c₁, s', a', c₂, hch, .inl hp, rfl⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases callPre_append hc with hc' | ⟨c₃, rfl, hc'⟩
    · exact exists_of_contChain_callPre hch hc'
    · exact ⟨c₁, s', a', c₃, hch, .inr (.inl ⟨_, _, hp, hc'⟩), rfl⟩
  · exact exists_of_iterBeh_callPre hb hc
  · simp only at hk hm
    subst hk hm
    rcases hω with ⟨c₁, s', a', ω', hch, hω', rfl⟩ | ⟨σ, l, h0, hσ, hl⟩
    · rcases Nat.lt_or_ge k c₁.length with hk | hk
      · exact exists_of_contChain_callPre hch
          (callPre_of_streamPrefix (streamPrefix_append c₁ ω') hk)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        refine ⟨c₁, s', a', streamTake ω' j, hch, ?_, streamTake_append c₁ ω' j⟩
        rw [append_get_ge]
        exact .inr (.inr (.inr ⟨ω', hω', j, rfl, rfl⟩))
    · obtain ⟨N, hN⟩ := hl.2 (k + 1)
      have hch := contChain_of_seq hσ N
      rw [h0] at hch
      exact exists_of_contChain_callPre hch (callPre_of_streamPrefix (hl.1 N) (by omega))

/-! ### Extending observations by a continuing return in front -/

theorem pending_iterT_cons {s a d s' a'} (h : (d, End.ret (.inr a') s') ∈ T.1 s a)
    {p : List (Call E) × E.Op} (hp : p ∈ (iterT T).2.1 s' a') :
    (d ++ p.1, p.2) ∈ (iterT T).2.1 s a := by
  obtain ⟨c, s'', a'', c', m, hch, hm, rfl⟩ := hp
  exact ⟨d ++ c, s'', a'', c', m, .step h hch, hm, by simp⟩

theorem inf_iterT_cons {s a d s' a'} (h : (d, End.ret (.inr a') s') ∈ T.1 s a)
    {ω : ℕ → Call E} (hω : ω ∈ (iterT T).2.2 s' a') :
    d ++ₛ ω ∈ (iterT T).2.2 s a := by
  rcases hω with ⟨c, s'', a'', ω', hch, hω', rfl⟩ | ⟨σ, l, h0, hσ, hl⟩
  · exact .inl ⟨d ++ c, s'', a'', ω', .step h hch, hω',
      (Stream'.append_append_stream d c ω').symm⟩
  · refine .inr ⟨fun n => n.casesOn (s, a) σ, fun n => n.casesOn d l, rfl, fun n => ?_,
      streamConcat_cons (l := fun n => n.casesOn d l) hl⟩
    cases n with
    | zero =>
      show (d, End.ret (.inr (σ 0).2) (σ 0).1) ∈ T.1 s a
      rw [h0]
      exact h
    | succ n => exact hσ n

theorem satP_iterT_cons {s a d s' a'} (h : (d, End.ret (.inr a') s') ∈ T.1 s a)
    {c : List (Call E)} {m : E.Op} (hx : (c, m) ∈ satP (iterT T) s' a') :
    (d ++ c, m) ∈ satP (iterT T) s a := by
  rcases hx with hp | ⟨d', m', hp, hc⟩ | ⟨d', e, hb, hc⟩ | ⟨ω, hω, k, hk, hm⟩
  · exact .inl (pending_iterT_cons h hp)
  · exact .inr (.inl ⟨d ++ d', m', pending_iterT_cons h hp, callPre_append_left d hc⟩)
  · exact .inr (.inr (.inl ⟨d ++ d', e, AFun.IterBeh.step h hb, callPre_append_left d hc⟩))
  · simp only at hk hm
    subst hk hm
    refine .inr (.inr (.inr ⟨d ++ₛ ω, inf_iterT_cons h hω, d.length + k, ?_, ?_⟩))
    · exact streamTake_append d ω k
    · rw [append_get_ge]

/-- **Call prefixes after a continuing chain**, the log of the chain in front. -/
theorem satP_iterT_of_contChain {s a c₁ s' a'} (h : FullFun.ContChain T.1 s a c₁ s' a')
    {c : List (Call E)} {m : E.Op} (hx : (c, m) ∈ satP (iterT T) s' a') :
    (c₁ ++ c, m) ∈ satP (iterT T) s a := by
  induction h with
  | refl => simpa using hx
  | step h₁ _ ih => rw [List.append_assoc]; exact satP_iterT_cons h₁ (ih hx)

/-! ### Totality -/

/-- **Iteration preserves totality**, by dependent choice of continuing returns. -/
theorem total_iterT (hT : Total T) : Total (iterT T) := by
  classical
  let Obs : S × A → Prop := fun p => ((iterT T).1 p.1 p.2).Nonempty ∨
    ((iterT T).2.1 p.1 p.2).Nonempty ∨ ((iterT T).2.2 p.1 p.2).Nonempty
  have key : ∀ p : S × A, ¬ Obs p →
      ∃ q : S × A, ∃ d, (d, End.ret (.inr q.2) q.1) ∈ T.1 p.1 p.2 ∧ ¬ Obs q := by
    rintro ⟨s, a⟩ hp
    rcases hT s a with ⟨⟨d, e⟩, hb⟩ | ⟨p, hp'⟩ | ⟨ω, hω⟩
    · rcases e with ⟨b | a', s'⟩ | _ | _
      · exact (hp (.inl ⟨_, AFun.IterBeh.exit hb⟩)).elim
      · refine ⟨(s', a'), d, hb, fun hq => hp ?_⟩
        rcases hq with ⟨⟨d', e'⟩, hy⟩ | ⟨p, hp⟩ | ⟨ω, hω⟩
        · exact .inl ⟨_, AFun.IterBeh.step hb hy⟩
        · exact .inr (.inl ⟨_, pending_iterT_cons hb hp⟩)
        · exact .inr (.inr ⟨_, inf_iterT_cons hb hω⟩)
      · exact (hp (.inl ⟨_, AFun.IterBeh.trap hb⟩)).elim
      · exact (hp (.inl ⟨_, AFun.IterBeh.div hb⟩)).elim
    · exact (hp (.inr (.inl ⟨_, ⟨[], s, a, p.1, p.2, .refl, hp', rfl⟩⟩))).elim
    · exact (hp (.inr (.inr ⟨ω, .inl ⟨[], s, a, ω, .refl, hω, rfl⟩⟩))).elim
  have key' : ∀ p : S × A, ∃ q : S × A, ∃ d : List (Call E),
      ¬ Obs p → (d, End.ret (.inr q.2) q.1) ∈ T.1 p.1 p.2 ∧ ¬ Obs q := fun p =>
    if hp : Obs p then ⟨p, [], fun h => (h hp).elim⟩
    else
      let ⟨q, d, h⟩ := key p hp
      ⟨q, d, fun _ => h⟩
  choose g l hg using key'
  intro s a
  by_contra h0
  let σ : ℕ → S × A := fun n => g^[n] (s, a)
  have hσ : ∀ n, σ (n + 1) = g (σ n) := fun n => Function.iterate_succ_apply' g n (s, a)
  have hbad : ∀ n, ¬ Obs (σ n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => rw [hσ]; exact (hg (σ n) ih).2
  have hstep : ∀ n, (l (σ n), End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈
      T.1 (σ n).1 (σ n).2 := by
    intro n
    rw [hσ]
    exact (hg (σ n) (hbad n)).1
  by_cases hfin : ∃ N, ∀ n, N ≤ n → l (σ n) = []
  · obtain ⟨N, hN⟩ := hfin
    refine hbad N
      (.inl ⟨([], End.div), AFun.IterBeh.spin (fun n => σ (N + n)) rfl fun n => ?_⟩)
    have := hstep (N + n)
    rw [hN (N + n) (by omega)] at this
    exact this
  · push Not at hfin
    obtain ⟨ω, hω⟩ := Shape.exists_streamConcat _
      (Shape.unbounded_of_frequently (fun n => l (σ n)) hfin)
    exact hbad 0 (.inr (.inr ⟨ω, .inr ⟨σ, fun n => l (σ n), rfl, hstep, hω⟩⟩))

/-- With a total iteration, **every call prefix of the body is one of the iteration**. -/
theorem satP_iterT_of_satP (hT : Total (iterT T)) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} (h : (c, m) ∈ satP T s a) : (c, m) ∈ satP (iterT T) s a := by
  rcases h with hp | ⟨d, m', hp, hc⟩ | ⟨d, e, hb, hc⟩ | ⟨ω, hω, k, hk, hm⟩
  · exact .inl ⟨[], s, a, c, m, .refl, hp, rfl⟩
  · exact .inr (.inl ⟨d, m', ⟨[], s, a, d, m', .refl, hp, rfl⟩, hc⟩)
  · rcases e with ⟨b | a', s'⟩ | _ | _
    · exact beh_satP (AFun.IterBeh.exit hb) hc
    · rcases hT s' a' with ⟨⟨d', e'⟩, hb'⟩ | ⟨p, hp⟩ | ⟨ω, hω⟩
      · exact beh_satP (AFun.IterBeh.step hb hb') (callPre_append_right hc d')
      · exact .inr (.inl ⟨d ++ p.1, p.2, pending_iterT_cons hb hp, callPre_append_right hc _⟩)
      · obtain ⟨n, c', rfl⟩ := hc
        have hk : c.length < (c ++ ⟨m, n⟩ :: c').length := by simp
        refine .inr (.inr (.inr ⟨_, inf_iterT_cons hb hω, c.length, ?_, ?_⟩))
        · rw [streamTake_of_prefix (streamPrefix_append _ ω) hk.le]
          simp
        · rw [append_get_lt _ _ hk]
          simp
    · exact beh_satP (AFun.IterBeh.trap hb) hc
    · exact beh_satP (AFun.IterBeh.div hb) hc
  · simp only at hk hm
    subst hk hm
    exact .inr (.inr (.inr ⟨ω, .inl ⟨[], s, a, ω, .refl, hω, rfl⟩, k, rfl, rfl⟩))

/-- **Call prefixes of an iteration of a total body**: a finite chain of continuing
iterations, then a call prefix of the body. -/
theorem mem_satP_iterT_of_total (hT : Total T) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} :
    (c, m) ∈ satP (iterT T) s a ↔
      ∃ c₁ s' a' c₂, FullFun.ContChain T.1 s a c₁ s' a' ∧ (c₂, m) ∈ satP T s' a' ∧
        c = c₁ ++ c₂ := by
  refine ⟨exists_contChain_of_satP_iterT, ?_⟩
  rintro ⟨c₁, s', a', c₂, hch, hm, rfl⟩
  exact satP_iterT_of_contChain hch (satP_iterT_of_satP (total_iterT hT) hm)

end Iter

end Silmaril.Proofs.Games.Abstract.SessionIter3
