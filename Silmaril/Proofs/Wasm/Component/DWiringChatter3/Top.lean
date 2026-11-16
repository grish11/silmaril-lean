module

public import Silmaril.Proofs.Wasm.Component.DWiringChatter3.Comp
public import Silmaril.Wasm.Component.DWiringChatter2.Thms
public import Silmaril.Games.Handler.Thms

/-!
# Runs of the node above the environment, routed

`extTop e N` is copycat beside `N` below `splitH e`. Its plays and infinite
plays are read off the routed pairing play `c.map (splitRoute e)`:

* `mem_extTop_iff`: `c` is a play of `extTop e N` iff it is legal and its
  routing is a play of the pairing. An outer question not yet forwarded by
  `splitH e` is accepted by the pairing anyway, which is receptive.
* `inf_extTop_iff`: `C` is an infinite play of `extTop e N` iff it is an
  infinite trace of such plays and `N`'s half of the routed trace, when it is
  infinite, is an infinite play of `N`. Forwards, the routed trace is contained
  in, hence equal to, the infinite play of the pairing seen through `splitH e`
  (`route_prefix_of_lt`). Backwards, `splitH e` serves the routed plays by
  increasing plays (`hplay`), which gives the chains of `ThroughAbove`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter3

open Silmaril.Games Silmaril.Wasm.Component

universe u v

variable {e : Nat} {N : DStrategy sigU sigU}

/-! ## `splitH e` serving a routed play, increasingly -/

/-- The moves of `splitH e` serving one move of the visible play: an outer
question is received and forwarded at once; an answer is received and passed on
at once; moves at `D`'s interface do not involve it. -/
def hplay (e : Nat) : Move sigU sigU → List (Move (sigU ⊕ₛ sigU) sigU)
  | .inl _ => []
  | .inr (.ask q) => [.inr (.ask q), .inl (.ask (splitQ e q))]
  | .inr (.ans q r) =>
    if q.1 < e then [.inl (.ans (.inl q) r), .inr (.ans q r)]
    else [.inl (.ans (.inr (q.1 - e, q.2)) r), .inr (.ans q r)]

theorem zip_hplay (c : List (Move sigU sigU)) :
    Zip (c.map (splitRoute e)) (c.flatMap (hplay e)) c := by
  induction c with
  | nil => exact .nil
  | cons o c ih =>
    rcases o with l | (q | ⟨q, r⟩)
    · exact .left _ ih
    · exact .right _ (.sync _ ih)
    · by_cases hq : q.1 < e
      · simp only [List.map_cons, List.flatMap_cons, splitRoute, hplay, hq, ↓reduceIte,
          List.cons_append, List.nil_append]
        exact .sync _ (.right _ ih)
      · simp only [List.map_cons, List.flatMap_cons, splitRoute, hplay, hq, ↓reduceIte,
          List.cons_append, List.nil_append]
        exact .sync _ (.right _ ih)

theorem splitQ_of_lt {q : sigU.Op} (hq : q.1 < e) : splitQ e q = .inl q := by
  simp [splitQ, hq]

theorem splitQ_of_not_lt {q : sigU.Op} (hq : ¬ q.1 < e) : splitQ e q = .inr (q.1 - e, q.2) := by
  simp [splitQ, hq]

theorem splitH_of_lt {q : sigU.Op} (hq : q.1 < e) :
    splitH e q = .call (.inl q) (fun n => .pure n) := by
  simp [splitH, hq]

theorem splitH_of_not_lt {q : sigU.Op} (hq : ¬ q.1 < e) :
    splitH e q = .call (.inr (q.1 - e, q.2)) (fun n => .pure n) := by
  simp [splitH, hq]

/-- `splitH e` waiting for the pairing's answer to the routed question. -/
def wst (e : Nat) (q : sigU.Op) : (splitH e).toReduction.State :=
  if q.1 < e then .wait q (.inl q) (fun n => .pure n)
  else .wait q (.inr (q.1 - e, q.2)) (fun n => .pure n)

theorem wst_of_lt {q : sigU.Op} (hq : q.1 < e) :
    wst e q = .wait q (.inl q) (fun n => .pure n) := by
  simp [wst, hq]

theorem wst_of_not_lt {q : sigU.Op} (hq : ¬ q.1 < e) :
    wst e q = .wait q (.inr (q.1 - e, q.2)) (fun n => .pure n) := by
  simp [wst, hq]

/-- The state of `splitH e` above a position of the play it serves. -/
def sst (e : Nat) : Pos sigU sigU → (splitH e).toReduction.State
  | .idle => .idle
  | .run q => wst e q
  | .wait q _ => wst e q

theorem run_hplay {x y : Pos sigU sigU} {c : List (Move sigU sigU)} (h : Path x c y) :
    ∃ y', (splitH e).toReduction.toLTS.Run (sst e x) (c.flatMap (hplay e)) y' := by
  induction h with
  | nil => exact ⟨_, .nil _⟩
  | @cons x z y o c hs _ ih =>
    obtain ⟨y', hr⟩ := ih
    cases hs with
    | ask q =>
      by_cases hq : q.1 < e
      · rw [sst, wst_of_lt hq] at hr
        simp only [List.flatMap_cons, hplay, splitQ_of_lt hq, List.cons_append, List.nil_append]
        exact ⟨_, LTS.Run.vis (Reduction.Step.ask q)
          (LTS.Run.vis (Reduction.Step.call (splitH_of_lt hq)) hr)⟩
      · rw [sst, wst_of_not_lt hq] at hr
        simp only [List.flatMap_cons, hplay, splitQ_of_not_lt hq, List.cons_append,
          List.nil_append]
        exact ⟨_, LTS.Run.vis (Reduction.Step.ask q)
          (LTS.Run.vis (Reduction.Step.call (splitH_of_not_lt hq)) hr)⟩
    | call q m => exact ⟨y', hr⟩
    | reply q m n => exact ⟨y', hr⟩
    | ret q r =>
      by_cases hq : q.1 < e
      · simp only [List.flatMap_cons, hplay, hq, ↓reduceIte, List.cons_append, List.nil_append]
        refine ⟨y', ?_⟩
        rw [sst, wst_of_lt hq]
        exact LTS.Run.vis (Reduction.Step.resume (R := (splitH e).toReduction) q (.inl q)
          (fun n => .pure n) r) (LTS.Run.vis (Reduction.Step.ret rfl) hr)
      · simp only [List.flatMap_cons, hplay, hq, ↓reduceIte, List.cons_append, List.nil_append]
        refine ⟨y', ?_⟩
        rw [sst, wst_of_not_lt hq]
        exact LTS.Run.vis (Reduction.Step.resume (R := (splitH e).toReduction) q
          (.inr (q.1 - e, q.2)) (fun n => .pure n) r) (LTS.Run.vis (Reduction.Step.ret rfl) hr)

theorem mem_hplay {c : List (Move sigU sigU)} (h : Legal c) :
    c.flatMap (hplay e) ∈ Strategy.ofHandler (splitH e) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨y', hr⟩ := run_hplay (e := e) hy
  exact Strategy.mem_ofHandler.2 ⟨y', hr⟩

/-! ## Finite plays -/

theorem not_legal_ask_ask {E F : Sig.{u}} {c : List (Move E F)} {q q' : F.Op} :
    ¬ Legal (c ++ [.inr (.ask q'), .inr (.ask q)]) := by
  rintro ⟨y, h⟩
  obtain ⟨x, -, h₂⟩ := Path.of_append h
  cases h₂ with
  | cons s₁ h₃ =>
    cases s₁
    cases h₃ with
    | cons s₂ _ => cases s₂

theorem mem_extTop {c : List (Move sigU sigU)} :
    c ∈ (DStrategy.extTop e N).toStrategy ↔
      ∃ a ∈ (Strategy.id sigU).pair N.toStrategy, ∃ w ∈ Strategy.ofHandler (splitH e),
        Zip a w c := Iff.rfl

/-- **Plays of `extTop e N`, routed.** -/
theorem mem_extTop_iff {c : List (Move sigU sigU)} :
    c ∈ (DStrategy.extTop e N).toStrategy ↔
      Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy := by
  constructor
  · intro hc
    have hl := (DStrategy.extTop e N).toStrategy.legal hc
    obtain ⟨a, ha, w, hw, hz⟩ := mem_extTop.1 hc
    refine ⟨hl, ?_⟩
    rcases splitRoute_prefix_of_zip hz hw (Strategy.mem_pair.1 ha).1 with h | ⟨c', q, rfl⟩
    · exact Strategy.of_prefix _ ha h
    · obtain ⟨a', w', ha', hw', hz'⟩ := hz.of_prefix (List.prefix_append c' _)
      have hc' : c'.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy := by
        rcases splitRoute_prefix_of_zip hz' (Strategy.of_prefix _ hw hw')
            (Strategy.mem_pair.1 (Strategy.of_prefix _ ha ha')).1 with h | ⟨c'', q', rfl⟩
        · exact Strategy.of_prefix _ (Strategy.of_prefix _ ha ha') h
        · exact absurd (by simpa using hl) not_legal_ask_ask
      obtain ⟨y, hy⟩ := legal_splitRoute (e := e) hl
      rw [List.map_append, List.map_singleton] at hy ⊢
      obtain ⟨x, hx, hst⟩ := Path.concat_iff.1 hy
      exact Strategy.receptive _ hc' hx hst trivial
  · rintro ⟨hl, hr⟩
    obtain ⟨w, hw, hz⟩ := exists_zip_splitRoute (e := e) hl
    exact mem_extTop.2 ⟨_, hr, w, hw, hz⟩

/-! ## Infinite plays -/

/-- **The pairing play under a strictly shorter prefix.** If a legal pairing
play `a` interacts with a play of `splitH e` with legal visible part `c₁`, then
the routing of every strictly shorter prefix of `c₁` is a prefix of `a`. -/
theorem route_prefix_of_lt {a : List (Move sigU (sigU ⊕ₛ sigU))}
    {w : List (Move (sigU ⊕ₛ sigU) sigU)} {c c₁ : List (Move sigU sigU)} (hz : Zip a w c₁)
    (hw : w ∈ Strategy.ofHandler (splitH e)) (ha : Legal a) (hl : Legal c₁) (hc : c <+: c₁)
    (hlt : c.length < c₁.length) : c.map (splitRoute e) <+: a := by
  rcases splitRoute_prefix_of_zip hz hw ha with h | ⟨d, q, rfl⟩
  · exact (hc.map _).trans h
  · rcases List.prefix_concat_iff.1 hc with rfl | hcd
    · simp at hlt
    · obtain ⟨a', w', ha', hw', hz'⟩ := hz.of_prefix (List.prefix_append d _)
      rcases splitRoute_prefix_of_zip hz' ((Strategy.ofHandler (splitH e)).of_prefix hw hw')
          (ha.of_prefix ha') with h | ⟨d', q', rfl⟩
      · exact (hcd.map _).trans (h.trans ha')
      · exact absurd (by simpa using hl) not_legal_ask_ask

section Image

variable {α : Type u} {β : Type v}

theorem isInfPlay_image {C : Set (List α)} (h : IsInfPlay C) (f : α → β) :
    IsInfPlay (List.map f '' C) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t _ ⟨c, hc, rfl⟩ ht
    refine ⟨c.take t.length, h.of_prefix hc (List.take_prefix _ _), ?_⟩
    rw [List.map_take, ← List.prefix_iff_eq_take.1 ht]
  · rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    rcases h.total hc hc' with h' | h'
    · exact .inl (h'.map f)
    · exact .inr (h'.map f)
  · intro k
    obtain ⟨c, hc, hk⟩ := h.unbounded k
    exact ⟨_, ⟨c, hc, rfl⟩, by simpa using hk⟩

theorem eq_of_subset {A B : Set (List α)} (hA : IsInfPlay A) (hB : IsInfPlay B) (h : A ⊆ B) :
    A = B := by
  refine h.antisymm fun k hk => ?_
  obtain ⟨x, hx, hl⟩ := hA.unbounded k.length
  exact hA.of_prefix hx (hB.prefix_of_length_le hk (h hx) hl)

end Image

/-- **Infinite plays of `extTop e N`, routed.** -/
theorem inf_extTop_iff {C : Set (List (Move sigU sigU))} :
    C ∈ (DStrategy.extTop e N).inf ↔ IsInfPlay C ∧
      (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
      (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
        Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) := by
  constructor
  · intro hC
    have hCi := (DStrategy.extTop e N).inf_isInf hC
    have hCl : ∀ c ∈ C, Legal c := fun c hc =>
      (DStrategy.extTop e N).toStrategy.legal ((DStrategy.extTop e N).inf_sub hC hc)
    rw [DStrategy.inf_extTop] at hC
    obtain ⟨K, ⟨hKi, hKs, hKN⟩, sch, wch, pch, hzc, hsK, hwh, -, -, -, -, hJlim⟩ := hC
    have hsub : List.map (splitRoute e) '' C ⊆ K := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨c₁, hc₁, hl₁⟩ := hCi.unbounded (c.length + 1)
      have hcc := hCi.prefix_of_length_le hc hc₁ (by omega)
      have hc₁' := hc₁
      rw [hJlim] at hc₁'
      obtain ⟨n, hn⟩ := hc₁'
      obtain ⟨a', w', ha', hw', hz'⟩ := (hzc n).of_prefix hn
      have ha'K : a' ∈ K := hKi.of_prefix (hsK n) ha'
      exact hKi.of_prefix ha'K (route_prefix_of_lt hz' (Strategy.of_prefix _ (hwh n) hw')
        (Strategy.mem_pair.1 (hKs ha'K)).1 (hCl c₁ hc₁) hcc (by omega))
    have hRK := eq_of_subset (isInfPlay_image hCi _) hKi hsub
    refine ⟨hCi, fun c hc => ⟨hCl c hc, hKs (hsub ⟨c, hc, rfl⟩)⟩, ?_⟩
    rw [hRK]
    exact hKN
  · rintro ⟨hCi, hmem, hN⟩
    rw [DStrategy.inf_extTop]
    refine ⟨_, ⟨isInfPlay_image hCi _, fun _ ⟨c, hc, h⟩ => h ▸ (hmem c hc).2, hN⟩,
      fun n => (hCi.seq n).map (splitRoute e), fun n => (hCi.seq n).flatMap (hplay e), hCi.seq,
      fun n => zip_hplay _, fun n => ⟨_, hCi.seq_mem n, rfl⟩,
      fun n => mem_hplay (hmem _ (hCi.seq_mem n)).1, fun n => (hCi.seq_mono n).map _,
      fun n => ?_, hCi.seq_mono, hCi.seq_unbounded, hCi.lim_seq.symm⟩
    obtain ⟨d, hd⟩ := hCi.seq_mono n
    show List.flatMap _ _ <+: List.flatMap _ _
    rw [← hd, List.flatMap_append]
    exact List.prefix_append _ _

/-! ## Runs -/

theorem not_isInfPlay_infR_prefixes (c₀ : List (Move sigU sigU)) :
    ¬ IsInfPlay (Split.infR (List.map (splitRoute e) '' prefixes c₀)) := by
  intro h
  obtain ⟨t, ⟨_, ⟨c, hc, rfl⟩, ht⟩, hl⟩ :=
    h.unbounded ((Split.halves false (c₀.map (splitRoute e))).2.length + 1)
  have := (ht.trans (Split.halves_prefix (List.IsPrefix.map (splitRoute e) hc) false).2).length_le
  omega

/-- **Runs of `extTop e N`, routed.** -/
theorem isRun_extTop_iff {C : Set (List (Move sigU sigU))} :
    IsRun (DStrategy.extTop e N) C ↔ (IsInfPlay C ∨ ∃ c₀, C = prefixes c₀) ∧
      (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
      (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
        Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) := by
  constructor
  · rintro (h | ⟨c₀, hc₀, rfl⟩)
    · obtain ⟨hCi, hmem, hN⟩ := inf_extTop_iff.1 h
      exact ⟨.inl hCi, hmem, hN⟩
    · exact ⟨.inr ⟨c₀, rfl⟩, fun c hc => mem_extTop_iff.1 (Strategy.of_prefix _ hc₀ hc),
        fun h => absurd h (not_isInfPlay_infR_prefixes c₀)⟩
  · rintro ⟨hCi | ⟨c₀, rfl⟩, hmem, hN⟩
    · exact .inl (inf_extTop_iff.2 ⟨hCi, hmem, hN⟩)
    · exact .inr ⟨c₀, mem_extTop_iff.2 (hmem c₀ (List.prefix_refl _)), rfl⟩

end Silmaril.Proofs.Wasm.Component.DWiringChatter3
