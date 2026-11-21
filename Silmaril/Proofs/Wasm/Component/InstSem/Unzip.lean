module

public import Silmaril.Proofs.Wasm.Component.InstSem.Run

/-!
# Plays made of complete rounds, taken apart

The converse of `Rounds` and `Run`: a play of a composite, a handler, a pairing or copycat that
consists of complete rounds comes from complete rounds of its parts.

* `rounds_of_path`: a play from `idle` back to `idle` is a list of complete rounds;
* `zip_split`: an interaction whose visible trace is a concatenation splits accordingly;
* `zip_rounds_inv`: **an interaction whose visible trace is complete rounds** `rs` is made of
  complete rounds `ts` of the upper strategy, each served by consecutive complete rounds of the
  lower one (`ZipR`): the converse of `zip_round`;
* `runs_of_ofHandler_rounds`: complete rounds of a handler run its programs (the converse of
  `mem_ofHandler_rounds`);
* `mem_pair_rounds_inv`, `id_rounds_inv`: complete rounds of a pairing are rounds of its two
  sides; complete rounds of copycat forward each question once.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games

variable {E F G : Sig.{0}}

/-! ## Complete rounds from paths -/

theorem round_of_path_run {q : F.Op} : ∀ (x : List (Move E F)), Path (.run q) x .idle →
    ∃ (cs : List (Call E)) (a : F.Ar q) (rest : List (Move E F)),
      x = (callEvs cs).map .inl ++ .inr (.ans q a) :: rest ∧ Path .idle rest .idle
  | [], h => by cases h
  | o :: x, .cons hs hp => by
    cases hs with
    | call _ m =>
      match x, hp with
      | [], h => cases h
      | o' :: x', .cons hs' hp' =>
        cases hs' with
        | reply _ _ n =>
          obtain ⟨cs, a, rest, rfl, hr⟩ := round_of_path_run x' hp'
          exact ⟨⟨m, n⟩ :: cs, a, rest, rfl, hr⟩
    | ret _ a => exact ⟨[], a, x, rfl, hp⟩

/-- **A play from `idle` back to `idle` is a list of complete rounds.** -/
theorem rounds_of_path : ∀ (x : List (Move E F)), Path .idle x .idle →
    ∃ xs : List (Round E F), x = roundsMoves xs
  | [], _ => ⟨[], rfl⟩
  | o :: x, .cons hs hp => by
    cases hs with
    | ask q =>
      obtain ⟨cs, a, rest, hx, hr⟩ := round_of_path_run x hp
      have : rest.length < x.length + 1 := by
        rw [hx]; simp only [List.length_append, List.length_cons]; omega
      obtain ⟨xs, rfl⟩ := rounds_of_path rest hr
      exact ⟨⟨q, cs, a⟩ :: xs, by
        rw [hx]; simp only [roundsMoves, Round.moves, List.cons_append, List.append_assoc,
          List.nil_append]⟩
termination_by x => x.length

/-! ## Projections -/

theorem callEvs_inj : ∀ {cs ds : List (Call E)}, callEvs cs = callEvs ds → cs = ds
  | [], [], _ => rfl
  | [], ⟨_, _⟩ :: _, h => by simp [callEvs] at h
  | ⟨_, _⟩ :: _, [], h => by simp [callEvs] at h
  | ⟨m, n⟩ :: cs, ⟨m', n'⟩ :: ds, h => by
    simp only [callEvs, List.cons.injEq, Ev.ask.injEq, Ev.ans.injEq] at h
    obtain ⟨rfl, ⟨-, hn⟩, h⟩ := h
    cases hn
    rw [callEvs_inj h]

theorem lower_callEvs_inl : ∀ cs : List (Call E),
    lower ((callEvs cs).map (Sum.inl (β := Ev F))) = callEvs cs
  | [] => rfl
  | ⟨_, _⟩ :: cs => by
    simp only [callEvs, List.map_cons, lower, List.filterMap_cons, Sum.getLeft?_inl]
    exact congrArg _ (congrArg _ (lower_callEvs_inl cs))

theorem upper_callEvs_inl : ∀ cs : List (Call E),
    upper ((callEvs cs).map (Sum.inl (β := Ev F))) = []
  | [] => rfl
  | ⟨_, _⟩ :: cs => by
    simp only [callEvs, List.map_cons, upper, List.filterMap_cons, Sum.getRight?_inl]
    exact upper_callEvs_inl cs

theorem lower_round (r : Round E F) : lower r.moves = callEvs r.cs := by
  simp only [Round.moves, lower, List.filterMap_cons, Sum.getLeft?_inr, List.filterMap_append,
    List.filterMap_nil]
  have := lower_callEvs_inl (F := F) r.cs
  simp only [lower] at this
  rw [this, List.append_nil]

theorem upper_round (r : Round E F) : upper r.moves = callEvs [r.call] := by
  simp only [Round.moves, upper, List.filterMap_cons, Sum.getRight?_inr, List.filterMap_append,
    List.filterMap_nil]
  have := upper_callEvs_inl (F := F) r.cs
  simp only [upper] at this
  rw [this]
  rfl

theorem lower_rounds : ∀ rs : List (Round E F), lower (roundsMoves rs) = callEvs (allCalls rs)
  | [] => rfl
  | r :: rs => by
    simp only [roundsMoves, allCalls, callEvs_append]
    rw [← lower_rounds rs, ← lower_round]
    simp only [lower, List.filterMap_append]

theorem upper_rounds : ∀ rs : List (Round E F),
    upper (roundsMoves rs) = callEvs (rs.map Round.call)
  | [] => rfl
  | r :: rs => by
    simp only [roundsMoves, List.map_cons]
    rw [show r.call :: rs.map Round.call = [r.call] ++ rs.map Round.call from rfl,
      callEvs_append, ← upper_rounds rs, ← upper_round]
    simp only [upper, List.filterMap_append]

section ZipProj

variable {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}

theorem Zip.lower_eq (h : Zip s t p) : lower p = lower s := by
  induction h with
  | nil => rfl
  | left a _ ih => simp only [lower, List.filterMap_cons, Sum.getLeft?_inl] at ih ⊢; rw [ih]
  | right c _ ih => simpa only [lower, List.filterMap_cons, Sum.getLeft?_inr] using ih
  | sync b _ ih => simpa only [lower, List.filterMap_cons, Sum.getLeft?_inr] using ih

theorem Zip.upper_eq (h : Zip s t p) : upper p = upper t := by
  induction h with
  | nil => rfl
  | left a _ ih => simpa only [upper, List.filterMap_cons, Sum.getRight?_inl] using ih
  | right c _ ih => simp only [upper, List.filterMap_cons, Sum.getRight?_inr] at ih ⊢; rw [ih]
  | sync b _ ih => simpa only [upper, List.filterMap_cons, Sum.getRight?_inl] using ih

theorem Zip.mid_eq (h : Zip s t p) : lower t = upper s := by
  induction h with
  | nil => rfl
  | left a _ ih => simpa only [upper, List.filterMap_cons, Sum.getRight?_inl] using ih
  | right c _ ih => simpa only [lower, List.filterMap_cons, Sum.getLeft?_inr] using ih
  | sync b _ ih =>
    simp only [lower, upper, List.filterMap_cons, Sum.getLeft?_inl, Sum.getRight?_inr] at ih ⊢
    rw [ih]

end ZipProj

/-! ## Splitting interactions -/

/-- **An interaction whose visible trace is a concatenation splits accordingly.** -/
theorem zip_split {α β γ : Type} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p₁ p₂ : List (α ⊕ γ)} (h : Zip s t (p₁ ++ p₂)) :
    ∃ s₁ s₂ t₁ t₂, s = s₁ ++ s₂ ∧ t = t₁ ++ t₂ ∧ Zip s₁ t₁ p₁ ∧ Zip s₂ t₂ p₂ := by
  generalize hp : p₁ ++ p₂ = p at h
  induction h generalizing p₁ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hp
    exact ⟨[], [], [], [], rfl, rfl, .nil, .nil⟩
  | @left s t p a h ih =>
    rcases p₁ with _ | ⟨x, p₁⟩
    · subst hp
      exact ⟨[], _, [], _, rfl, rfl, .nil, .left a h⟩
    · simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hp
      exact ⟨_, s₂, t₁, t₂, rfl, rfl, .left _ h₁, h₂⟩
  | @right s t p c h ih =>
    rcases p₁ with _ | ⟨x, p₁⟩
    · subst hp
      exact ⟨[], _, [], _, rfl, rfl, .nil, .right c h⟩
    · simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hp
      exact ⟨s₁, s₂, _, t₂, rfl, rfl, .right _ h₁, h₂⟩
  | @sync s t p b h ih =>
    obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hp
    exact ⟨_, s₂, _, t₂, rfl, rfl, .sync b h₁, h₂⟩

theorem zip_nil_inv {s : List (Move E F)} {t : List (Move F G)} {b : Pos F G}
    (h : Zip s t []) (ht : Path .idle t b) : s = [] ∧ t = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | sync _ _ => cases ht with | cons hs _ => cases hs

/-- `ZipR rs ss ts`: the rounds `rs` of a composite are the rounds `ts` of the upper strategy,
each served by consecutive rounds `ss` of the lower one. -/
inductive ZipR : List (Round E G) → List (Round E F) → List (Round F G) → Prop
  | nil : ZipR [] [] []
  | cons (r : Round E G) (xs : List (Round E F)) {rs : List (Round E G)}
      {ss : List (Round E F)} {ts : List (Round F G)} (hc : r.cs = allCalls xs) :
      ZipR rs ss ts → ZipR (r :: rs) (xs ++ ss) (⟨r.q, xs.map Round.call, r.a⟩ :: ts)

/-- **An interaction whose visible trace is complete rounds** is made of complete rounds of the
upper strategy, each served by consecutive complete rounds of the lower one. -/
theorem zip_rounds_inv : ∀ (rs : List (Round E G)) {s : List (Move E F)}
    {t : List (Move F G)} {a : Pos E F} {b : Pos F G},
    Path .idle s a → Path .idle t b → Zip s t (roundsMoves rs) →
    ∃ ss ts, s = roundsMoves ss ∧ t = roundsMoves ts ∧ ZipR rs ss ts
  | [], s, t, a, b, _, ht, h => by
    obtain ⟨rfl, rfl⟩ := zip_nil_inv h ht
    exact ⟨[], [], rfl, rfl, .nil⟩
  | r :: rs, s, t, a, b, hs, ht, h => by
    obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := zip_split (p₁ := r.moves) h
    obtain ⟨y, hs₁, hs₂⟩ := Path.of_append hs
    obtain ⟨z, ht₁, ht₂⟩ := Path.of_append ht
    obtain ⟨c, hc, hcomp⟩ := Strategy.zip_path h₁ Strategy.ZipCompat.idle hs₁ ht₁
    have hc' : c = .idle := hc.det (path_round r)
    subst hc'
    cases hcomp
    obtain ⟨xs, rfl⟩ := rounds_of_path _ hs₁
    obtain ⟨us, rfl⟩ := rounds_of_path _ ht₁
    have hU := Zip.upper_eq h₁
    have hM := Zip.mid_eq h₁
    have hL := Zip.lower_eq h₁
    rw [upper_round, upper_rounds] at hU
    rw [lower_rounds, upper_rounds] at hM
    rw [lower_round, lower_rounds] at hL
    have hU' := callEvs_inj hU
    have hM' := callEvs_inj hM
    have hL' := callEvs_inj hL
    obtain ⟨ss, ts, rfl, rfl, hz⟩ := zip_rounds_inv rs hs₂ ht₂ h₂
    rcases us with _ | ⟨u, _ | ⟨u', us⟩⟩
    · cases hU'
    · obtain ⟨uq, ucs, ua⟩ := u
      obtain ⟨rq, rcs, ra⟩ := r
      simp only [List.map_cons, List.map_nil, Round.call, List.cons.injEq, Sigma.mk.injEq,
        and_true] at hU'
      obtain ⟨rfl, hua⟩ := hU'
      cases hua
      simp only [allCalls, List.append_nil] at hM'
      subst hM'
      refine ⟨xs ++ ss, ⟨rq, xs.map Round.call, ra⟩ :: ts, ?_, ?_, .cons _ xs hL' hz⟩
      · rw [roundsMoves_append]
      · simp only [roundsMoves, List.append_nil]
    · simp at hU'

/-! ## Handlers -/

theorem runs_of_round_run {h : Handler E F} {q : F.Op} : ∀ (cs : List (Call E))
    {P : Prog E (F.Ar q)} {a : F.Ar q} {rest : List (Move E F)}
    {y : h.toReduction.toLTS.State},
    h.toReduction.toLTS.Run (.run q P) ((callEvs cs).map .inl ++ .inr (.ans q a) :: rest) y →
    Prog.Runs P cs a ∧ h.toReduction.toLTS.Run .idle rest y
  | [], P, a, rest, y, hr => by
    obtain ⟨y', hs, hr'⟩ := handler_run_cons hr
    cases hs with
    | ret hd => cases hd; exact ⟨.pure _, hr'⟩
  | ⟨m, n⟩ :: cs, P, a, rest, y, hr => by
    obtain ⟨y', hs, hr₁⟩ := handler_run_cons hr
    cases hs with
    | call hc =>
      cases hc
      obtain ⟨y'', hs', hr'⟩ := handler_run_cons hr₁
      cases hs' with
      | resume _ _ _ _ =>
        obtain ⟨h₁, h₂⟩ := runs_of_round_run cs hr'
        exact ⟨.call h₁, h₂⟩

theorem runs_of_handler_run_rounds {h : Handler E F} : ∀ (rs : List (Round E F))
    {y : h.toReduction.toLTS.State}, h.toReduction.toLTS.Run .idle (roundsMoves rs) y →
    ∀ r ∈ rs, Prog.Runs (h r.q) r.cs r.a
  | [], _, _ => fun _ hr => nomatch hr
  | ⟨q, cs, a⟩ :: rs, y, hr => by
    simp only [roundsMoves, Round.moves, List.cons_append, List.append_assoc] at hr
    obtain ⟨q', hq, hr⟩ := handler_run_idle_cons hr
    cases hq
    obtain ⟨h₁, h₂⟩ := runs_of_round_run cs hr
    intro r hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact h₁
    · exact runs_of_handler_run_rounds rs h₂ r hr'

/-- **Complete rounds of a handler run its programs.** -/
theorem runs_of_ofHandler_rounds {h : Handler E F} {rs : List (Round E F)}
    (hm : roundsMoves rs ∈ Strategy.ofHandler h) : ∀ r ∈ rs, Prog.Runs (h r.q) r.cs r.a := by
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hm
  exact runs_of_handler_run_rounds rs hy

/-! ## Pairing and copycat -/

section Pair

variable {F₁ F₂ : Sig.{0}}

/-- The side of a round of a pairing. -/
def unsided : Round E (F₁ ⊕ₛ F₂) → Round E F₁ ⊕ Round E F₂
  | ⟨.inl q, cs, a⟩ => .inl ⟨q, cs, a⟩
  | ⟨.inr q, cs, a⟩ => .inr ⟨q, cs, a⟩

theorem sided_unsided : ∀ r : Round E (F₁ ⊕ₛ F₂), sided (unsided r) = r
  | ⟨.inl _, _, _⟩ => rfl
  | ⟨.inr _, _, _⟩ => rfl

/-- **Complete rounds of a pairing are rounds of its two sides.** -/
theorem mem_pair_rounds_inv {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {rs : List (Round E (F₁ ⊕ₛ F₂))} (h : roundsMoves rs ∈ σ₁.pair σ₂) :
    roundsMoves (lefts (rs.map unsided)) ∈ σ₁ ∧ roundsMoves (rights (rs.map unsided)) ∈ σ₂ := by
  have he : rs = (rs.map unsided).map sided := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id rs]
    exact List.map_congr_left fun r _ => (sided_unsided r).symm
  obtain ⟨-, h₁, h₂⟩ := h
  rw [he, halves_rounds] at h₁ h₂
  exact ⟨h₁, h₂⟩

end Pair

/-- **Complete rounds of copycat forward each question once.** -/
theorem id_rounds_inv {rs : List (Round E E)} (h : roundsMoves rs ∈ Strategy.id E) :
    ∀ r ∈ rs, r.cs = [⟨r.q, r.a⟩] := by
  rw [← Strategy.ofHandler_id] at h
  intro r hr
  obtain ⟨q, cs, a⟩ := r
  have h' : Prog.Runs (Prog.call q Prog.pure) cs a := runs_of_ofHandler_rounds h _ hr
  cases h' with
  | call h' => cases h'; rfl

end Silmaril.Proofs.Wasm.Component.InstSem
