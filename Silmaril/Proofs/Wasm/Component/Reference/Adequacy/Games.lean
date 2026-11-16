module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiGames

/-!
# Inverting plays of rounds through compositions, handlers and pairings

The converse of `Silmaril.Proofs.Wasm.Component.Reference.MultiGames`: there, rounds of the
parts give rounds of a composite; here, a composite play made of rounds comes from rounds of
its parts.

* `NoInl p`: the play `p` has no lower move. A strategy whose plays have no lower move is a
  *server*: its plays are complete rounds `twos l`, possibly followed by one pending question
  (`shape_of_noInl`). This holds whenever the lower signature has no operation
  (`noInl_of_isEmpty`), and it is preserved by composition on top (`noInl_comp`).
* `OneShot h`: the handler `h` answers each question at once or by one call whose answer it
  maps (`.call f fun r => .pure (k r)`). For such handlers a composite play of complete rounds
  `twos up` over a server below comes from rounds `twos low` of the server, with
  `HRounds h up low` (`hrounds_of_comp`).
* `twos_of_comp_noInl`: under a strategy without lower moves, the strategy below does not move,
  so complete rounds of the composite are rounds of the upper strategy.
* Pairing: `twos_of_pair_inr` (rounds of the right component), and `noInl_pair_split`: a
  pairing below a handler that sends every question to the right component, whose right
  component has no lower moves, has no lower moves.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference (Round twos HRounds)

universe u

variable {E F G : Sig.{u}}

/-! ## Plays without lower moves -/

/-- The play has no lower move. -/
def NoInl (p : List (Move E F)) : Prop := ∀ e, Sum.inl e ∉ p

theorem NoInl.nil : NoInl ([] : List (Move E F)) := fun _ h => nomatch h

theorem NoInl.cons_inr {g : Ev F} {p : List (Move E F)} (h : NoInl p) :
    NoInl (Sum.inr g :: p) := by
  intro e he
  rcases List.mem_cons.mp he with he | he
  · cases he
  · exact h e he

theorem NoInl.tail {m : Move E F} {p : List (Move E F)} (h : NoInl (m :: p)) : NoInl p :=
  fun e he => h e (List.mem_cons_of_mem _ he)

theorem NoInl.append {p q : List (Move E F)} (hp : NoInl p) (hq : NoInl q) : NoInl (p ++ q) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hp e he
  · exact hq e he

theorem noInl_twos : ∀ (l : List (Round F)), NoInl (twos (E := E) l)
  | [] => .nil
  | ⟨_, _⟩ :: l => (noInl_twos l).cons_inr.cons_inr

/-- Without lower operations, no play has a lower move. -/
theorem noInl_of_isEmpty [IsEmpty E.Op] (p : List (Move E F)) : NoInl p := by
  intro e _
  cases e with
  | ask m => exact isEmptyElim m
  | ans m _ => exact isEmptyElim m

theorem twos_ne_nil {q : F.Op} {a : F.Ar q} {l : List (Round F)} :
    twos (E := E) (⟨q, a⟩ :: l) ≠ [] := by
  simp [twos]

/-- **Plays without lower moves are complete rounds, possibly followed by a question.** -/
theorem shape_of_noInl : ∀ (p : List (Move E F)) {y : Pos E F}, Path .idle p y → NoInl p →
    (y = .idle ∧ ∃ l, p = twos l) ∨ (∃ q l, y = .run q ∧ p = twos l ++ [.inr (.ask q)])
  | [], y, h, _ => by
    cases h
    exact .inl ⟨rfl, [], rfl⟩
  | [m], y, h, _ => by
    cases h with
    | cons hs hp =>
      cases hs with
      | ask q =>
        cases hp
        exact .inr ⟨q, [], rfl, rfl⟩
  | m₁ :: m₂ :: p, y, h, hn => by
    cases h with
    | cons hs hp =>
      cases hs with
      | ask q =>
        cases hp with
        | cons hs' hp' =>
          cases hs' with
          | call _ e => exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) (hn (.ask e))
          | ret _ r =>
            rcases shape_of_noInl p hp' hn.tail.tail with ⟨rfl, l, rfl⟩ | ⟨q', l, rfl, rfl⟩
            · exact .inl ⟨rfl, ⟨q, r⟩ :: l, rfl⟩
            · exact .inr ⟨q', ⟨q, r⟩ :: l, rfl, rfl⟩

/-- `shape_of_noInl` for a legal play. -/
theorem shape_of_legal {p : List (Move E F)} (hp : Legal p) (hn : NoInl p) :
    (∃ l, p = twos l) ∨ (∃ q l, p = twos l ++ [.inr (.ask q)]) := by
  obtain ⟨y, hy⟩ := hp
  rcases shape_of_noInl p hy hn with ⟨-, l, rfl⟩ | ⟨q, l, -, rfl⟩
  · exact .inl ⟨l, rfl⟩
  · exact .inr ⟨q, l, rfl⟩

theorem twos_inj_nil {l : List (Round F)} (h : twos (E := E) l = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons x l => exact absurd h (by obtain ⟨_, _⟩ := x; exact twos_ne_nil)

/-! ## Interactions -/

theorem zip_inl_mem {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p : List (α ⊕ γ)} (h : Zip s t p) {a : α} (ha : Sum.inl a ∈ p) : Sum.inl a ∈ s := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | left a' _ ih =>
    rcases List.mem_cons.mp ha with ha | ha
    · cases ha; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih ha)
  | right c _ ih =>
    rcases List.mem_cons.mp ha with ha | ha
    · cases ha
    · exact ih ha
  | sync b _ ih => exact List.mem_cons_of_mem _ (ih ha)

theorem zip_inr_left_mem {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p : List (α ⊕ γ)} (h : Zip s t p) {b : β} (hb : Sum.inr b ∈ s) : Sum.inl b ∈ t := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | left a _ ih =>
    rcases List.mem_cons.mp hb with hb | hb
    · cases hb
    · exact ih hb
  | right c _ ih => exact List.mem_cons_of_mem _ (ih hb)
  | sync b' _ ih =>
    rcases List.mem_cons.mp hb with hb | hb
    · cases hb; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hb)

/-- **Composition keeps the absence of lower moves of the lower strategy.** -/
theorem noInl_comp {σ : Strategy E F} {τ : Strategy F G} (hσ : ∀ s ∈ σ, NoInl s) :
    ∀ p ∈ σ.comp τ, NoInl p := by
  rintro p ⟨s, hs, t, -, hz⟩ e he
  exact hσ s hs e (zip_inl_mem hz he)

theorem zip_cons_inr_right {s : List (Move E F)} {c : Ev G} {t : List (Move F G)}
    {p : List (Move E G)} (h : Zip s (Sum.inr c :: t) p) (hs : NoInl s) :
    ∃ p', p = Sum.inr c :: p' ∧ Zip s t p' := by
  cases h with
  | left a _ => exact absurd List.mem_cons_self (hs a)
  | right _ h' => exact ⟨_, rfl, h'⟩

theorem zip_cons_inl_right {s : List (Move E F)} {b : Ev F} {t : List (Move F G)}
    {p : List (Move E G)} (h : Zip s (Sum.inl b :: t) p) (hs : NoInl s) :
    ∃ s', s = Sum.inr b :: s' ∧ Zip s' t p := by
  cases h with
  | left a _ => exact absurd List.mem_cons_self (hs a)
  | sync _ h' => exact ⟨_, rfl, h'⟩

theorem zip_nil_right' {s : List (Move E F)} {p : List (Move E G)}
    (h : Zip s ([] : List (Move F G)) p) (hs : NoInl s) : s = [] ∧ p = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | left a _ => exact absurd List.mem_cons_self (hs a)

/-- **Under a strategy without lower moves, the strategy below does not move.** -/
theorem twos_of_comp_noInl {σ : Strategy E F} {τ : Strategy F G} (hτ : ∀ t ∈ τ, NoInl t)
    {l : List (Round G)} (h : twos l ∈ σ.comp τ) : twos l ∈ τ := by
  obtain ⟨s, -, t, ht, hz⟩ := h
  have key : ∀ (l : List (Round G)) (s : List (Move E F)) (t : List (Move F G)),
      NoInl t → Zip s t (twos l) → t = twos l := by
    intro l
    induction l with
    | nil =>
      intro s t hn hz
      cases hz with
      | nil => rfl
      | sync b _ => exact absurd List.mem_cons_self (hn b)
    | cons x l ih =>
      obtain ⟨q, a⟩ := x
      intro s t hn hz
      have hz' : Zip s t (Sum.inr (.ask q) :: Sum.inr (.ans q a) :: twos l) := hz
      cases hz' with
      | sync b _ => exact absurd List.mem_cons_self (hn b)
      | right _ hz₁ =>
        cases hz₁ with
        | sync b _ => exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) (hn b)
        | right _ hz₂ =>
          rw [ih _ _ hn.tail.tail hz₂]
          rfl
  rw [← key l s t (hτ t ht) hz]
  exact ht

/-! ## One-shot handlers -/

/-- The handler answers every question at once, or by one call whose answer it maps. -/
def OneShot (h : Handler F G) : Prop :=
  ∀ q, (∃ a, h q = .pure a) ∨ ∃ f, ∃ k : F.Ar f → G.Ar q, h q = .call f fun r => .pure (k r)

section Runs

variable {h : Handler F G}

theorem run_cons_inv {x y : h.toReduction.toLTS.State} {m : Move F G} {t : List (Move F G)}
    (hr : h.toReduction.toLTS.Run x (m :: t) y) :
    ∃ x', h.toReduction.Step x (some m) x' ∧ h.toReduction.toLTS.Run x' t y := by
  generalize hl : m :: t = l at hr
  induction hr with
  | nil => cases hl
  | tau hs _ _ =>
    cases hs with
    | tau hc => exact hc.elim
  | vis hs hr' _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    exact ⟨_, hs, hr'⟩

theorem run_idle_cons {m : Move F G} {t : List (Move F G)} {y : h.toReduction.State}
    (hr : h.toReduction.toLTS.Run .idle (m :: t) y) :
    ∃ q, m = Sum.inr (.ask q) ∧ h.toReduction.toLTS.Run (.run q (h q)) t y := by
  obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
  cases hs with
  | ask q => exact ⟨q, rfl, hr'⟩

theorem run_pure_cons {q : G.Op} {a : G.Ar q} {m : Move F G} {t : List (Move F G)}
    {y : h.toReduction.State}
    (hr : h.toReduction.toLTS.Run (.run q (.pure a)) (m :: t) y) :
    m = Sum.inr (.ans q a) ∧ h.toReduction.toLTS.Run .idle t y := by
  obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
  cases hs with
  | call hc => cases hc
  | ret hc =>
    cases hc
    exact ⟨rfl, hr'⟩

theorem run_call_cons {q : G.Op} {f : F.Op} {k : F.Ar f → Prog F (G.Ar q)} {m : Move F G}
    {t : List (Move F G)} {y : h.toReduction.State}
    (hr : h.toReduction.toLTS.Run (.run q (.call f k)) (m :: t) y) :
    m = Sum.inl (.ask f) ∧ h.toReduction.toLTS.Run (.wait q f k) t y := by
  obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
  cases hs with
  | call hc =>
    cases hc
    exact ⟨rfl, hr'⟩
  | ret hc => cases hc

theorem run_wait_cons {q : G.Op} {f : F.Op} {k : F.Ar f → Prog F (G.Ar q)} {m : Move F G}
    {t : List (Move F G)} {y : h.toReduction.State}
    (hr : h.toReduction.toLTS.Run (.wait q f k) (m :: t) y) :
    ∃ n, m = Sum.inl (.ans f n) ∧ h.toReduction.toLTS.Run (.run q (k n)) t y := by
  obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
  cases hs with
  | resume _ _ _ n => exact ⟨n, rfl, hr'⟩

end Runs

/-- **Complete rounds through a one-shot handler** come from complete rounds below. -/
theorem hrounds_of_zip {h : Handler F G} (hh : OneShot h) :
    ∀ (L : List (Round G)) (l : List (Round F)) (t : List (Move F G))
      (y : h.toReduction.State),
      h.toReduction.toLTS.Run .idle t y → Zip (twos (E := E) l) t (twos L) → HRounds h L l := by
  intro L
  induction L with
  | nil =>
    intro l t y hr hz
    cases t with
    | nil =>
      obtain ⟨hl, -⟩ := zip_nil_right' hz (noInl_twos l)
      rw [twos_inj_nil hl]
      exact .nil
    | cons m t =>
      obtain ⟨q, rfl, -⟩ := run_idle_cons hr
      obtain ⟨p', hp, -⟩ := zip_cons_inr_right hz (noInl_twos l)
      exact absurd hp (by simp [twos])
  | cons x L ih =>
    obtain ⟨g, a⟩ := x
    intro l t y hr hz
    have hz₀ : Zip (twos (E := E) l) t
        (Sum.inr (.ask g) :: Sum.inr (.ans g a) :: twos L) := hz
    cases t with
    | nil =>
      obtain ⟨-, hp⟩ := zip_nil_right' hz₀ (noInl_twos l)
      cases hp
    | cons m t =>
      obtain ⟨q, rfl, hr₁⟩ := run_idle_cons hr
      obtain ⟨p', hp, hz₁⟩ := zip_cons_inr_right hz₀ (noInl_twos l)
      obtain ⟨rfl, rfl⟩ : q = g ∧ p' = Sum.inr (.ans g a) :: twos L := by
        simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at hp
        exact ⟨hp.1.symm, hp.2.symm⟩
      rcases hh q with ⟨a₀, hq⟩ | ⟨f, kk, hq⟩
      · rw [hq] at hr₁
        cases t with
        | nil =>
          obtain ⟨-, hp⟩ := zip_nil_right' hz₁ (noInl_twos l)
          cases hp
        | cons m t =>
          obtain ⟨rfl, hr₂⟩ := run_pure_cons hr₁
          obtain ⟨p'', hp, hz₂⟩ := zip_cons_inr_right hz₁ (noInl_twos l)
          simp only [List.cons.injEq, Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact .pure hq (ih l t y hr₂ hz₂)
      · rw [hq] at hr₁
        cases t with
        | nil =>
          obtain ⟨-, hp⟩ := zip_nil_right' hz₁ (noInl_twos l)
          cases hp
        | cons m t =>
          obtain ⟨rfl, hr₂⟩ := run_call_cons hr₁
          obtain ⟨s', hs', hz₂⟩ := zip_cons_inl_right hz₁ (noInl_twos l)
          cases l with
          | nil => cases hs'
          | cons x l₀ =>
            obtain ⟨f', n⟩ := x
            have hs'' : Sum.inr (.ask f') :: Sum.inr (.ans f' n) :: twos (E := E) l₀ =
                Sum.inr (.ask f) :: s' := hs'
            simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at hs''
            obtain ⟨rfl, rfl⟩ := hs''
            cases t with
            | nil =>
              obtain ⟨hs, -⟩ := zip_nil_right' hz₂ (noInl_twos l₀).cons_inr
              cases hs
            | cons m t =>
              obtain ⟨n', rfl, hr₃⟩ := run_wait_cons hr₂
              obtain ⟨s'', hs₃, hz₃⟩ := zip_cons_inl_right hz₂ (noInl_twos l₀).cons_inr
              simp only [List.cons.injEq, Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at hs₃
              obtain ⟨rfl, rfl⟩ := hs₃
              cases t with
              | nil =>
                obtain ⟨-, hp⟩ := zip_nil_right' hz₃ (noInl_twos l₀)
                cases hp
              | cons m t =>
                obtain ⟨rfl, hr₄⟩ := run_pure_cons hr₃
                obtain ⟨p'', hp, hz₄⟩ := zip_cons_inr_right hz₃ (noInl_twos l₀)
                simp only [List.cons.injEq, Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq,
                  true_and] at hp
                obtain ⟨rfl, rfl⟩ := hp
                exact .call hq rfl (ih l₀ t y hr₄ hz₄)

/-- Positions compatible with an idle composite position are idle. -/
theorem zipCompat_idle {a : Pos E F} {b : Pos F G} (h : Strategy.ZipCompat a b .idle) :
    a = .idle ∧ b = .idle := by
  cases h
  exact ⟨rfl, rfl⟩

/-- **A one-shot handler on top of a strategy whose interacting plays have no lower moves**:
complete rounds of the composite come from complete rounds below. -/
theorem hrounds_of_comp_of {σ : Strategy E F} {h : Handler F G} (hh : OneShot h)
    (hσ : ∀ s ∈ σ, ∀ t ∈ Strategy.ofHandler h, ∀ {p : List (Move E G)}, Zip s t p → NoInl s)
    {L : List (Round G)} (hL : twos L ∈ σ.comp (Strategy.ofHandler h)) :
    ∃ l, HRounds h L l ∧ twos l ∈ σ := by
  obtain ⟨s, hs, t, ht, hz⟩ := hL
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
  obtain ⟨a', ha'⟩ := σ.legal hs
  obtain ⟨b', hb'⟩ := (Strategy.ofHandler h).legal ht
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle ha' hb'
  have hc'' : c' = .idle := Path.det hc' (Silmaril.Proofs.Wasm.Component.Reference.path_twos L)
  subst hc''
  obtain ⟨rfl, -⟩ := zipCompat_idle hcomp
  rcases shape_of_noInl s ha' (hσ s hs t ht hz) with ⟨-, l, rfl⟩ | ⟨q, l, he, -⟩
  · exact ⟨l, hrounds_of_zip hh L l t y hy hz, hs⟩
  · cases he

/-- **A one-shot handler on top of a server**: complete rounds of the composite come from
complete rounds of the server. -/
theorem hrounds_of_comp {σ : Strategy E F} {h : Handler F G} (hh : OneShot h)
    (hσ : ∀ s ∈ σ, NoInl s) {L : List (Round G)} (hL : twos L ∈ σ.comp (Strategy.ofHandler h)) :
    ∃ l, HRounds h L l ∧ twos l ∈ σ :=
  hrounds_of_comp_of hh (fun s hs _ _ _ _ => hσ s hs) hL

/-! ## Pairing -/

/-- **Rounds of the right component of a pairing.** -/
theorem twos_of_pair_inr {F₁ F₂ : Sig.{u}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (Round F₂)}
    (h : twos (l.map (Silmaril.Proofs.Wasm.Component.Reference.Round.inr (F₁ := F₁))) ∈
      σ₁.pair σ₂) : twos l ∈ σ₂ := by
  obtain ⟨-, -, h₂⟩ := h
  rw [Silmaril.Proofs.Wasm.Component.Reference.halves_twos_inr] at h₂
  exact h₂

/-- Without questions to the left component, lower moves go to the right half. -/
theorem inl_mem_halves_true {F₁ F₂ : Sig.{u}} :
    ∀ (s : List (Move E (F₁ ⊕ₛ F₂))), (∀ q, Sum.inr (.ask (Sum.inl q)) ∉ s) →
      ∀ e, Sum.inl e ∈ s → Sum.inl e ∈ (Split.halves true s).2
  | [], _, _, he => nomatch he
  | Sum.inl e' :: s, hq, e, he => by
    simp only [Split.halves]
    rcases List.mem_cons.mp he with he | he
    · cases he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (inl_mem_halves_true s (fun q hm => hq q (List.mem_cons_of_mem _ hm)) e he)
  | Sum.inr (.ask (Sum.inl q)) :: s, hq, _, _ => absurd List.mem_cons_self (hq q)
  | Sum.inr (.ask (Sum.inr q)) :: s, hq, e, he => by
    simp only [Split.halves]
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact List.mem_cons_of_mem _
        (inl_mem_halves_true s (fun q hm => hq q (List.mem_cons_of_mem _ hm)) e he)
  | Sum.inr (.ans (Sum.inl q) r) :: s, hq, e, he => by
    simp only [Split.halves]
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact inl_mem_halves_true s (fun q hm => hq q (List.mem_cons_of_mem _ hm)) e he
  | Sum.inr (.ans (Sum.inr q) r) :: s, hq, e, he => by
    simp only [Split.halves]
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact List.mem_cons_of_mem _
        (inl_mem_halves_true s (fun q hm => hq q (List.mem_cons_of_mem _ hm)) e he)

/-- A play of a pairing without questions to the left component has its lower moves in the
right half. -/
theorem noInl_of_pair {F₁ F₂ : Sig.{u}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    (h₂ : ∀ s ∈ σ₂, NoInl s) {s : List (Move E (F₁ ⊕ₛ F₂))} (hs : s ∈ σ₁.pair σ₂)
    (hq : ∀ q, Sum.inr (.ask (Sum.inl q)) ∉ s) : NoInl s := by
  obtain ⟨⟨y, hy⟩, -, hs₂⟩ := hs
  intro e he
  cases s with
  | nil => exact nomatch he
  | cons m s =>
    cases hy with
    | cons hst _ =>
      cases hst with
      | ask q₀ =>
        cases q₀ with
        | inl q => exact hq q List.mem_cons_self
        | inr q =>
          have hq' : ∀ q, Sum.inr (.ask (Sum.inl q)) ∉ s :=
            fun q hm => hq q (List.mem_cons_of_mem _ hm)
          rcases List.mem_cons.mp he with he | he
          · cases he
          · have hm := inl_mem_halves_true s hq' e he
            have hs₂' : Sum.inr (Ev.ask q) :: (Split.halves true s).2 ∈ σ₂ := by
              simpa only [Split.halves] using hs₂
            exact h₂ _ hs₂' e (List.mem_cons_of_mem _ hm)

/-- The states a one-shot handler reaches: running its program or an answer, or waiting
with a pure continuation. -/
def RunInv (h : Handler F G) : h.toReduction.State → Prop
  | .idle => True
  | .run q c => c = h q ∨ ∃ a, c = .pure a
  | .wait q f k => ∃ kk : F.Ar f → G.Ar q, k = fun r => .pure (kk r)

/-- The lower questions of a one-shot handler are the calls of its programs. -/
theorem run_ask_mem {h : Handler F G} (hh : OneShot h) :
    ∀ (t : List (Move F G)) (x y : h.toReduction.State), RunInv h x →
      h.toReduction.toLTS.Run x t y →
      ∀ f, Sum.inl (.ask f) ∈ t → ∃ q k, h q = .call f k
  | [], _, _, _, _, _, hf => nomatch hf
  | m :: t, x, y, hx, hr, f, hf => by
    obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
    cases hs with
    | ask q =>
      rcases List.mem_cons.mp hf with hf | hf
      · cases hf
      · exact run_ask_mem hh t _ y (show RunInv h (.run q (h q)) from .inl rfl) hr' f hf
    | @call q c m' k hc =>
      have hc' : c = .call m' k := hc
      have hx' : c = h q ∨ ∃ a, c = .pure a := hx
      rcases List.mem_cons.mp hf with hf | hf
      · simp only [Sum.inl.injEq, Ev.ask.injEq] at hf
        subst hf
        rcases hx' with hx' | ⟨a, hx'⟩
        · exact ⟨q, k, hx' ▸ hc'⟩
        · rw [hx'] at hc'; cases hc'
      · refine run_ask_mem hh t _ y ?_ hr' f hf
        show ∃ kk : F.Ar m' → G.Ar q, k = fun r => .pure (kk r)
        rcases hx' with hx' | ⟨a, hx'⟩
        · rcases hh q with ⟨a₀, hq⟩ | ⟨f₀, kk, hq⟩
          · rw [hx', hq] at hc'; cases hc'
          · rw [hx', hq] at hc'
            cases hc'
            exact ⟨kk, rfl⟩
        · rw [hx'] at hc'; cases hc'
    | resume q f' k n =>
      rcases List.mem_cons.mp hf with hf | hf
      · cases hf
      · refine run_ask_mem hh t _ y ?_ hr' f hf
        obtain ⟨kk, rfl⟩ := (hx : ∃ kk : F.Ar f' → G.Ar q, k = fun r => .pure (kk r))
        exact .inr ⟨kk n, rfl⟩
    | ret hc =>
      rcases List.mem_cons.mp hf with hf | hf
      · cases hf
      · exact run_ask_mem hh t _ y (show RunInv h .idle from trivial) hr' f hf

/-- **A pairing below a handler that only calls the right component**, whose right component
has no lower moves, has no lower moves. -/
theorem noInl_pair_comp {F₁ F₂ : Sig.{u}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {h : Handler (F₁ ⊕ₛ F₂) G} (hh : OneShot h)
    (hr : ∀ q f k, h q = .call f k → ∃ f₂, f = Sum.inr f₂) (h₂ : ∀ s ∈ σ₂, NoInl s) :
    ∀ p ∈ (σ₁.pair σ₂).comp (Strategy.ofHandler h), NoInl p := by
  rintro p ⟨s, hs, t, ht, hz⟩ e he
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
  have hq : ∀ q, Sum.inr (.ask (Sum.inl q)) ∉ s := by
    intro q hm
    have ht' := zip_inr_left_mem hz hm
    obtain ⟨q', k, hk⟩ := run_ask_mem hh t .idle y (show RunInv h .idle from trivial) hy _ ht'
    obtain ⟨f₂, hf⟩ := hr q' _ k hk
    cases hf
  exact noInl_of_pair h₂ hs hq e (zip_inl_mem hz he)

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
