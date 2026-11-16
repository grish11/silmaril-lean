module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Games
public import Silmaril.Games.LTS.Thms

/-!
# Inverting plays that end inside a round

The read-back of `LinkedSessionAdeq.Games` inverts complete rounds (plays from `idle` to
`idle`). A divergence is a play at a running position (`DStrategy.div_run`), so its read-back
needs plays that end inside a round: complete rounds `cl`, then a pending question `g` after the
answered lower calls `cs` (`rplay cl g cs`).

* `exists_rplay`, `exists_wplay`: a play from `idle` to `.run g` is `rplay cl g cs`; a play to
  `.wait g m` is `rplay cl g cs ++ [.inl (.ask m)]`;
* `zip_split`: an interaction whose visible part is split is split along it;
* `hc_zip_run`: a handler on top of a running strategy (`hc_inv` with a pending round): the
  strategy's play is `rplay low f cs`, the rounds `HC`, and the handler calls `f` for `g`;
* `hb_zip_run`: a one-shot handler below a strategy at `.run g` (`hb_inv` with a pending round):
  the composite play is `rplay low g cs'`, the rounds `HB`, the pending lower calls `HRounds`;
* `hc_zip_wait`, `hb_zip_wait`: the same at a waiting position, the lower call pending (for
  `hb_zip_wait`, forwarded by the handler); from the running versions by removing the last
  moves (`zip_snoc_left`, `zip_snoc_sync`);
* `serve_run`, `serve_wait`: a server without lower moves below a strategy at `.run g` (or
  waiting at `.wait g m`): `serve_inv` with a pending round;
* `halves_rplay_inr`, `halves_wplay_inr`: the right half of a pending round of the right
  component of a pairing.

All are stated on the `Zip` witnesses (and handler runs), so that they apply to the witnesses of
`DivComp.mem_div_comp` and of the `DWiring` divergence theorems.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq

variable {E F G : Sig.{0}}

/-! ## Plays ending inside a round -/

/-- Complete rounds `cl`, then the question `g`, pending after the answered lower calls `cs`. -/
def rplay (cl : List (CRound E F)) (g : F.Op) (cs : List (Round E)) : List (Move E F) :=
  cplay cl ++ .inr (.ask g) :: callMoves cs

/-- The shape of a play reaching `.run g`, by its first position. -/
def ShapeR (g : F.Op) : Pos E F → List (Move E F) → Prop
  | .idle, t => ∃ (cl : List (CRound E F)) (cs : List (Round E)), t = rplay cl g cs
  | .run q, t => (q = g ∧ ∃ cs : List (Round E), t = callMoves cs) ∨
      ∃ (cs : List (Round E)) (a : F.Ar q) (cl : List (CRound E F)) (cs' : List (Round E)),
        t = callMoves cs ++ .inr (.ans q a) :: rplay cl g cs'
  | .wait q m, t => ∃ n : E.Ar m, (q = g ∧ ∃ cs : List (Round E),
      t = .inl (.ans m n) :: callMoves cs) ∨
      ∃ (cs : List (Round E)) (a : F.Ar q) (cl : List (CRound E F)) (cs' : List (Round E)),
        t = .inl (.ans m n) :: (callMoves cs ++ .inr (.ans q a) :: rplay cl g cs')

theorem shapeR_of_path {g : F.Op} {x z : Pos E F} {t : List (Move E F)} (h : Path x t z)
    (hz : z = .run g) : ShapeR g x t := by
  induction h with
  | nil x => subst hz; exact .inl ⟨rfl, [], rfl⟩
  | cons hs _ ih =>
    have ih := ih hz
    cases hs with
    | ask q =>
      rcases ih with ⟨rfl, cs, rfl⟩ | ⟨cs, a, cl, cs', rfl⟩
      · exact ⟨[], cs, rfl⟩
      · exact ⟨⟨q, cs, a⟩ :: cl, cs', by simp [rplay, cplay]⟩
    | call q m =>
      obtain ⟨n, ⟨rfl, cs, rfl⟩ | ⟨cs, a, cl, cs', rfl⟩⟩ := ih
      · exact .inl ⟨rfl, ⟨m, n⟩ :: cs, rfl⟩
      · exact .inr ⟨⟨m, n⟩ :: cs, a, cl, cs', rfl⟩
    | reply q m n =>
      rcases ih with ⟨rfl, cs, rfl⟩ | ⟨cs, a, cl, cs', rfl⟩
      · exact ⟨n, .inl ⟨rfl, cs, rfl⟩⟩
      · exact ⟨n, .inr ⟨cs, a, cl, cs', rfl⟩⟩
    | ret q r =>
      obtain ⟨cl, cs, rfl⟩ := ih
      exact .inr ⟨[], r, cl, cs, rfl⟩

/-- **A play from idle to `.run g`** is complete rounds, then `g` pending after answered lower
calls. -/
theorem exists_rplay {g : F.Op} {t : List (Move E F)} (h : Path .idle t (.run g)) :
    ∃ (cl : List (CRound E F)) (cs : List (Round E)), t = rplay cl g cs :=
  shapeR_of_path h rfl

/-- **A play from idle to `.wait g m`** is complete rounds, then `g` pending after answered
lower calls and the pending call `m`. -/
theorem exists_wplay {g : F.Op} {m : E.Op} {t : List (Move E F)}
    (h : Path .idle t (.wait g m)) :
    ∃ (cl : List (CRound E F)) (cs : List (Round E)),
      t = rplay cl g cs ++ [.inl (.ask m)] := by
  rcases List.eq_nil_or_concat t with rfl | ⟨t', o, rfl⟩
  · cases h
  · rw [List.concat_eq_append] at h
    obtain ⟨y, h₁, h₂⟩ := Path.concat_iff.1 h
    cases h₂ with
    | call q m =>
      obtain ⟨cl, cs, rfl⟩ := exists_rplay h₁
      exact ⟨cl, cs, List.concat_eq_append ..⟩

theorem path_rplay (cl : List (CRound E F)) (g : F.Op) (cs : List (Round E)) :
    Path .idle (rplay cl g cs) (.run g) :=
  (path_cplay cl).append (.cons (.ask g) (path_calls g cs))

theorem callMoves_inj : ∀ {cs cs' : List (Round E)},
    (callMoves cs : List (Move E F)) = callMoves cs' → cs = cs'
  | [], [], _ => rfl
  | [], ⟨_, _⟩ :: _, h => by simp [callMoves] at h
  | ⟨_, _⟩ :: _, [], h => by simp [callMoves] at h
  | ⟨m, n⟩ :: cs, ⟨m', n'⟩ :: cs', h => by
    simp only [callMoves, List.cons.injEq, Sum.inl.injEq, Ev.ask.injEq] at h
    obtain ⟨rfl, h₁, h₂⟩ := h
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    rw [h₁, callMoves_inj h₂]

theorem callMoves_ne_append_inr {cs cs' : List (Round E)} {x : Ev F} {R : List (Move E F)} :
    (callMoves cs : List (Move E F)) ≠ callMoves cs' ++ .inr x :: R := by
  intro h
  exact inr_not_mem_callMoves cs (h ▸ List.mem_append_right _ List.mem_cons_self)

/-- `rplay` is injective. -/
theorem rplay_inj : ∀ {l l' : List (CRound E F)} {g g' : F.Op} {cs cs' : List (Round E)},
    rplay l g cs = rplay l' g' cs' → l = l' ∧ g = g' ∧ cs = cs'
  | [], [], _, _, _, _, h => by
    simp only [rplay, cplay, List.nil_append, List.cons.injEq, Sum.inr.injEq,
      Ev.ask.injEq] at h
    exact ⟨rfl, h.1, callMoves_inj h.2⟩
  | [], ⟨q, cs₀, a⟩ :: l', _, _, _, _, h => by
    simp only [rplay, cplay, List.nil_append, List.cons_append, List.cons.injEq,
      List.append_assoc] at h
    exact absurd h.2 callMoves_ne_append_inr
  | ⟨q, cs₀, a⟩ :: l, [], _, _, _, _, h => by
    simp only [rplay, cplay, List.nil_append, List.cons_append, List.cons.injEq,
      List.append_assoc] at h
    exact absurd h.2.symm callMoves_ne_append_inr
  | ⟨q, cs₀, a⟩ :: l, ⟨q', cs₀', a'⟩ :: l', _, _, _, _, h => by
    simp only [rplay, cplay, List.cons_append, List.cons.injEq, Sum.inr.injEq,
      Ev.ask.injEq, List.append_assoc] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, h₁, h₂⟩ := callMoves_inr_inj h
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    obtain ⟨rfl, rfl, rfl⟩ := rplay_inj (l := l) (l' := l') h₂
    rw [h₁]
    exact ⟨rfl, rfl, rfl⟩

/-! ## Splitting interactions -/

section Zip

variable {α β γ : Type}

/-- An interaction whose visible part is `p₁ ++ p₂` splits into interactions with the visible
parts `p₁` and `p₂`. -/
theorem zip_split {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p₁ p₂ : List (α ⊕ γ)}
    (h : Zip s t (p₁ ++ p₂)) :
    ∃ s₁ s₂ t₁ t₂, s = s₁ ++ s₂ ∧ t = t₁ ++ t₂ ∧ Zip s₁ t₁ p₁ ∧ Zip s₂ t₂ p₂ := by
  generalize hp : p₁ ++ p₂ = p at h
  induction h generalizing p₁ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hp
    exact ⟨[], [], [], [], rfl, rfl, .nil, .nil⟩
  | left a h ih =>
    cases p₁ with
    | nil =>
      rw [List.nil_append] at hp
      subst hp
      exact ⟨[], _, [], _, rfl, rfl, .nil, .left a h⟩
    | cons x p₁ =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hp
      exact ⟨.inl a :: s₁, s₂, t₁, t₂, rfl, rfl, .left a h₁, h₂⟩
  | right c h ih =>
    cases p₁ with
    | nil =>
      rw [List.nil_append] at hp
      subst hp
      exact ⟨[], _, [], _, rfl, rfl, .nil, .right c h⟩
    | cons x p₁ =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hp
      exact ⟨s₁, s₂, .inr c :: t₁, t₂, rfl, rfl, .right c h₁, h₂⟩
  | sync b h ih =>
    cases p₁ with
    | nil =>
      rw [List.nil_append] at hp
      subst hp
      exact ⟨[], _, [], _, rfl, rfl, .nil, .sync b h⟩
    | cons x p₁ =>
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hp
      exact ⟨.inr b :: s₁, s₂, .inl b :: t₁, t₂, rfl, rfl, .sync b h₁, h₂⟩

theorem zip_left_inl_mem {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) {a : α} (ha : Sum.inl a ∈ s) : Sum.inl a ∈ p := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | left a' _ ih =>
    rcases List.mem_cons.mp ha with h | h
    · obtain rfl := Sum.inl.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)
  | right c _ ih => exact List.mem_cons_of_mem _ (ih ha)
  | sync b _ ih =>
    rcases List.mem_cons.mp ha with h | h
    · cases h
    · exact ih h

theorem zip_nil_left_inl {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip ([] : List (α ⊕ β)) t p) {b : β} (hb : Sum.inl b ∈ t) : False := by
  generalize hs : ([] : List (α ⊕ β)) = s at h
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | left _ _ _ => cases hs
  | right c _ ih =>
    rcases List.mem_cons.mp hb with h | h
    · cases h
    · exact ih h hs
  | sync _ _ _ => cases hs

/-- **A last visible move of the left trace** can be removed. -/
theorem zip_snoc_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {a : α}
    (h : Zip (s ++ [.inl a]) t (p ++ [.inl a])) : Zip s t p := by
  generalize hs : s ++ [Sum.inl a] = S at h
  generalize hp : p ++ [Sum.inl a] = Q at h
  induction h generalizing s p with
  | nil => simp at hs
  | left a' h ih =>
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        exact h
      | cons y p =>
        simp only [List.cons_append, List.cons.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        exact absurd (zip_inl_mem h (List.mem_append_right _ List.mem_cons_self)) (by simp)
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨rfl, hs⟩ := hs
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        have hm : Sum.inl a ∈ s ++ [Sum.inl a] := List.mem_append_right _ List.mem_cons_self
        rw [hs] at hm
        exact absurd (zip_left_inl_mem h hm) (by simp)
      | cons y p =>
        simp only [List.cons_append, List.cons.injEq] at hp
        obtain ⟨rfl, hp⟩ := hp
        exact .left _ (ih hs hp)
  | right c h ih =>
    cases p with
    | nil => simp at hp
    | cons y p =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      exact .right _ (ih hs hp)
  | sync b h ih =>
    cases s with
    | nil => simp at hs
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨rfl, hs⟩ := hs
      exact .sync _ (ih hs hp)

/-- **A last hidden move of both traces** can be removed. -/
theorem zip_snoc_sync {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {b : β}
    (h : Zip (s ++ [.inr b]) (t ++ [.inl b]) p) : Zip s t p := by
  generalize hs : s ++ [Sum.inr b] = S at h
  generalize ht : t ++ [Sum.inl b] = T at h
  induction h generalizing s t with
  | nil => simp at hs
  | left a h ih =>
    cases s with
    | nil => simp at hs
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨rfl, hs⟩ := hs
      exact .left _ (ih hs ht)
  | right c h ih =>
    cases t with
    | nil => simp at ht
    | cons y t =>
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      exact .right _ (ih hs ht)
  | sync b' h ih =>
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      cases t with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at ht
        obtain ⟨-, rfl⟩ := ht
        exact h
      | cons y t =>
        simp only [List.cons_append, List.cons.injEq] at ht
        obtain ⟨-, rfl⟩ := ht
        exact (zip_nil_left_inl h (List.mem_append_right _ List.mem_cons_self)).elim
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨rfl, hs⟩ := hs
      cases t with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at ht
        obtain ⟨-, rfl⟩ := ht
        exact ((zip_nil_right_inr h).1 b
          (by rw [← hs]; exact List.mem_append_right _ List.mem_cons_self)).elim
      | cons y t =>
        simp only [List.cons_append, List.cons.injEq] at ht
        obtain ⟨rfl, ht⟩ := ht
        exact .sync _ (ih hs ht)

end Zip

/-! ## Handler positions -/

section Pos

variable {h : Handler F G}

/-- The game position of a handler state. -/
def hpos : h.toReduction.State → Pos F G
  | .idle => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

theorem path_hpos {x y : h.toReduction.toLTS.State} {t : List (Move F G)}
    (hr : h.toReduction.toLTS.Run x t y) : Path (hpos x) t (hpos y) := by
  induction hr with
  | nil => exact .nil _
  | tau hs _ _ =>
    cases hs with
    | tau hc => exact hc.elim
  | vis hs _ ih =>
    cases hs with
    | ask q => exact .cons (.ask q) ih
    | call _ => exact .cons (.call _ _) ih
    | resume q m k n => exact .cons (.reply q m n) ih
    | ret _ => exact .cons (.ret _ _) ih

theorem hpos_eq_idle {y : h.toReduction.State} (hy : hpos y = .idle) : y = .idle := by
  cases y with
  | idle => rfl
  | run q c => cases hy
  | wait q m k => cases hy

end Pos

/-- **A handler on top of a running strategy** makes the composite run. -/
theorem run_of_zip_top {h : Handler F G} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} {y : h.toReduction.toLTS.State} {f : F.Op} (hz : Zip s t p)
    (hs : Path .idle s (.run f)) (ht : h.toReduction.toLTS.Run .idle t y) :
    ∃ g, Path .idle p (.run g) := by
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle hs (path_hpos ht)
  generalize hpos y = b at hcomp
  cases hcomp with
  | call g _ => exact ⟨g, hc'⟩

/-! ## A handler on top of a running strategy -/

section Top

variable {h : Handler F G}

theorem path_idle_ne_inl {s : List (Move E F)} {y : Pos E F} (hs : Path .idle s y) :
    ∀ a s', s ≠ .inl a :: s' := by
  rintro a s' rfl
  cases hs with
  | cons hst _ => cases hst

/-- After the handler's call, the lower strategy's moves are its lower calls, until it answers;
it does not answer while the visible part is lower calls only. -/
theorem wait_calls {g : G.Op} {f' f : F.Op} {kk : F.Ar f' → G.Ar g} :
    ∀ (cs : List (Round E)) {s : List (Move E F)} {t : List (Move F G)}
      {y : h.toReduction.State},
      h.toReduction.toLTS.Run (.wait g f' fun r => .pure (kk r)) t y →
      Path (.run f') s (.run f) → Zip s t (callMoves cs) → f' = f ∧ s = callMoves cs
  | cs, [], t, y, hr, hs, hz => by
    cases hs
    cases t with
    | nil =>
      cases cs with
      | nil => exact ⟨rfl, rfl⟩
      | cons r cs =>
        obtain ⟨m, n⟩ := r
        cases hz
    | cons m t =>
      obtain ⟨n, rfl, -⟩ := run_wait_cons hr
      exact (zip_nil_inl hz).elim
  | cs, x :: s, t, y, hr, hs, hz => by
    cases hs with
    | cons hst hs' =>
      cases hst with
      | call _ m =>
        cases cs with
        | nil => cases hz
        | cons r cs =>
          obtain ⟨m', n⟩ := r
          cases hz with
          | left _ hz₁ =>
            cases s with
            | nil => cases hs'
            | cons x' s =>
              cases hs' with
              | cons hst' hs'' =>
                cases hst' with
                | reply _ _ n₀ =>
                  cases hz₁ with
                  | left _ hz₂ =>
                    obtain ⟨rfl, rfl⟩ := wait_calls cs hr hs'' hz₂
                    exact ⟨rfl, rfl⟩
      | ret _ r =>
        exfalso
        cases t with
        | nil => exact (zip_nil_right_inr hz).1 _ List.mem_cons_self
        | cons m t =>
          obtain ⟨n, rfl, hr₁⟩ := run_wait_cons hr
          obtain ⟨-, hz₁⟩ := zip_sync hz
          have hr₁' : h.toReduction.toLTS.Run (.run g (.pure (kk n))) t y := hr₁
          cases s with
          | nil => cases hs'
          | cons x' s =>
            cases hs' with
            | cons hst' _ =>
              cases hst' with
              | ask f₁ =>
                cases t with
                | nil => exact (zip_nil_right_inr hz₁).1 _ List.mem_cons_self
                | cons m t =>
                  obtain ⟨rfl, -⟩ := run_pure_cons hr₁'
                  cases cs with
                  | nil => cases hz₁
                  | cons r cs =>
                    obtain ⟨m', n'⟩ := r
                    cases hz₁

/-- The pending round through a one-shot handler on top of a running strategy. -/
theorem hc_tail (hh : OneShot h) {g : G.Op} {cs : List (Round E)} {s : List (Move E F)}
    {t : List (Move F G)} {y : h.toReduction.State} {f : F.Op} (hs : Path .idle s (.run f))
    (ht : h.toReduction.toLTS.Run .idle t y)
    (hz : Zip s t (.inr (.ask g) :: callMoves cs)) :
    ∃ k : F.Ar f → G.Ar g, h g = .call f (fun r => .pure (k r)) ∧
      s = .inr (.ask f) :: callMoves cs := by
  cases t with
  | nil => exact absurd List.mem_cons_self ((zip_nil_right_inr hz).2 _)
  | cons m t =>
    obtain ⟨q, rfl, hr₁⟩ := run_idle_cons ht
    obtain ⟨p', hp, hz₁⟩ := zip_right_of hz (path_idle_ne_inl hs)
    simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    cases s with
    | nil => cases hs
    | cons x s =>
      cases hs with
      | cons hst hs' =>
        cases hst with
        | ask f₀ =>
          rcases hh g with ⟨a₀, hg⟩ | ⟨f', kk, hg⟩
          · rw [hg] at hr₁
            exfalso
            cases t with
            | nil => exact (zip_nil_right_inr hz₁).1 _ List.mem_cons_self
            | cons m t =>
              obtain ⟨rfl, -⟩ := run_pure_cons hr₁
              cases cs with
              | nil => cases hz₁
              | cons r cs =>
                obtain ⟨m', n'⟩ := r
                cases hz₁
          · rw [hg] at hr₁
            cases t with
            | nil => exact absurd List.mem_cons_self ((zip_nil_right_inr hz₁).1 _)
            | cons m t =>
              obtain ⟨rfl, hr₂⟩ := run_call_cons hr₁
              obtain ⟨hb, hz₂⟩ := zip_sync hz₁
              obtain ⟨rfl⟩ := Ev.ask.inj hb
              obtain ⟨rfl, rfl⟩ := wait_calls cs hr₂ hs' hz₂
              exact ⟨kk, hg, rfl⟩

/-- **A one-shot handler on top of a running strategy** (`hc_inv` with a pending round): the
strategy's play is complete rounds `low` (`HC h up low`), then the question `f` that the
handler calls for `g`, pending after the same lower calls. -/
theorem hc_zip_run (hh : OneShot h) {up : List (CRound E G)} {g : G.Op} {cs : List (Round E)}
    {s : List (Move E F)} {t : List (Move F G)} {y : h.toReduction.State} {f : F.Op}
    (hs : Path .idle s (.run f)) (ht : h.toReduction.toLTS.Run .idle t y)
    (hz : Zip s t (rplay up g cs)) :
    ∃ (low : List (CRound E F)) (k : F.Ar f → G.Ar g), HC h up low ∧
      h g = .call f (fun r => .pure (k r)) ∧ s = rplay low f cs := by
  obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, hz₁, hz₂⟩ := zip_split hz
  obtain ⟨a₁, hs₁, hs₂⟩ := Path.of_append hs
  obtain ⟨y₁, ht₁, ht₂⟩ := LTS.Run.of_append ht
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz₁ Strategy.ZipCompat.idle hs₁ (path_hpos ht₁)
  have hc'' : c' = .idle := Path.det hc' (path_cplay up)
  subst hc''
  obtain ⟨rfl, hb⟩ := zipCompat_idle hcomp
  have hy₁ := hpos_eq_idle hb
  subst hy₁
  obtain ⟨low, rfl⟩ := exists_cplay hs₁
  obtain ⟨k, hk, rfl⟩ := hc_tail hh hs₂ ht₂ hz₂
  exact ⟨low, k, hc_of_zip hh up low t₁ .idle ht₁ hz₁, hk, rfl⟩

end Top

/-! ## A handler below a running strategy -/

section Below

variable {h : Handler E F}

/-- Complete rounds through a one-shot handler below, followed by anything. -/
theorem hb_of_zip_app (hh : OneShot h) :
    ∀ (up : List (CRound F G)) (X : List (Move F G)) (s : List (Move E F))
      (y : h.toReduction.State) (p : List (Move E G)),
      h.toReduction.toLTS.Run .idle s y → Zip s (cplay up ++ X) p →
      ∃ (low : List (CRound E G)) (s₁ : List (Move E F)) (p₁ : List (Move E G)),
        HB h up low ∧ p = cplay low ++ p₁ ∧ h.toReduction.toLTS.Run .idle s₁ y ∧ Zip s₁ X p₁
  | [], X, s, y, p, hr, hz => ⟨[], s, p, .nil, rfl, hr, hz⟩
  | ⟨g, cs, a⟩ :: up, X, s, y, p, hr, hz => by
    have hz₀ : Zip s (Sum.inr (Ev.ask g) :: (callMoves cs ++ Sum.inr (Ev.ans g a) ::
        (cplay up ++ X))) p := by
      simpa only [cplay, List.cons_append, List.append_assoc] using hz
    obtain ⟨p₁, rfl, hz₁⟩ := zip_right_of hz₀ (run_idle_ne_inl hr)
    obtain ⟨cs', s₁, p₂, H, rfl, hr₁, hz₂⟩ := hb_calls hh cs s y _ p₁ hr hz₁
    obtain ⟨p₃, rfl, hz₃⟩ := zip_right_of hz₂ (run_idle_ne_inl hr₁)
    obtain ⟨low, s₄, p₄, H', rfl, hr₄, hz₄⟩ := hb_of_zip_app hh up X s₁ y p₃ hr₁ hz₃
    exact ⟨⟨g, cs', a⟩ :: low, s₄, p₄, .cons H H',
      by simp only [cplay, List.cons_append, List.append_assoc], hr₄, hz₄⟩

/-- **A one-shot handler below a strategy at `.run g`** (`hb_inv` with a pending round): the
composite play is complete rounds `low` (`HB h up low`), then `g` pending after the lower calls
the handler made for the pending round's calls. -/
theorem hb_zip_run (hh : OneShot h) {up : List (CRound F G)} {g : G.Op} {cs : List (Round F)}
    {s : List (Move E F)} {y : h.toReduction.State} {p : List (Move E G)}
    (hr : h.toReduction.toLTS.Run .idle s y) (hz : Zip s (rplay up g cs) p) :
    ∃ (low : List (CRound E G)) (cs' : List (Round E)), HB h up low ∧ HRounds h cs cs' ∧
      p = rplay low g cs' := by
  obtain ⟨low, s₁, p₁, H, rfl, hr₁, hz₁⟩ := hb_of_zip_app hh up _ s y p hr hz
  obtain ⟨p₂, rfl, hz₂⟩ := zip_right_of hz₁ (run_idle_ne_inl hr₁)
  obtain ⟨cs', s₃, p₃, H', rfl, hr₃, hz₃⟩ := hb_calls hh cs s₁ y [] p₂ hr₁
    (by simpa only [List.append_nil] using hz₂)
  cases s₃ with
  | nil =>
    cases hz₃
    exact ⟨low, cs', H, H', by simp only [rplay, List.append_nil]⟩
  | cons m s₃ =>
    obtain ⟨q, rfl, -⟩ := run_idle_cons hr₃
    cases hz₃

end Below

/-! ## Plays ending at a waiting position -/

section Wait

/-- **A one-shot handler on top of a waiting strategy**: `hc_zip_run`, the lower call `m`
pending. -/
theorem hc_zip_wait {h : Handler F G} (hh : OneShot h) {up : List (CRound E G)} {g : G.Op}
    {cs : List (Round E)} {s : List (Move E F)} {t : List (Move F G)}
    {y : h.toReduction.State} {f : F.Op} {m : E.Op} (hs : Path .idle s (.wait f m))
    (ht : h.toReduction.toLTS.Run .idle t y)
    (hz : Zip s t (rplay up g cs ++ [.inl (.ask m)])) :
    ∃ (low : List (CRound E F)) (k : F.Ar f → G.Ar g), HC h up low ∧
      h g = .call f (fun r => .pure (k r)) ∧ s = rplay low f cs ++ [.inl (.ask m)] := by
  obtain ⟨cl, cs₀, rfl⟩ := exists_wplay hs
  obtain ⟨low, k, H, hk, he⟩ := hc_zip_run hh (path_rplay _ _ _) ht (zip_snoc_left hz)
  exact ⟨low, k, H, hk, by rw [he]⟩

theorem run_nil_inv {h : Handler F G} {x y : h.toReduction.toLTS.State}
    (hr : h.toReduction.toLTS.Run x [] y) : x = y := by
  cases hr with
  | nil => rfl
  | tau hs _ =>
    cases hs with
    | tau hc => exact hc.elim

/-- A one-shot handler stays in the states `RunInv` describes. -/
theorem runInv_run {h : Handler F G} (hh : OneShot h) :
    ∀ (t : List (Move F G)) (x y : h.toReduction.toLTS.State), RunInv h x →
      h.toReduction.toLTS.Run x t y → RunInv h y
  | [], x, y, hx, hr => run_nil_inv hr ▸ hx
  | m :: t, x, y, hx, hr => by
    obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
    refine runInv_run hh t x' y ?_ hr'
    cases hs with
    | ask q => exact .inl rfl
    | @call q c m' k hc =>
      have hc' : c = .call m' k := hc
      rcases (hx : c = h q ∨ ∃ a, c = .pure a) with hx' | ⟨a, hx'⟩
      · rcases hh q with ⟨a₀, hq⟩ | ⟨f₀, kk, hq⟩
        · rw [hx', hq] at hc'
          cases hc'
        · rw [hx', hq] at hc'
          cases hc'
          exact ⟨kk, rfl⟩
      · rw [hx'] at hc'
        cases hc'
    | resume q f' k n =>
      obtain ⟨kk, rfl⟩ := (hx : ∃ kk : F.Ar f' → G.Ar q, k = fun r => .pure (kk r))
      exact .inr ⟨kk n, rfl⟩
    | ret _ => trivial

theorem run_snoc_inv {h : Handler F G} {x y : h.toReduction.toLTS.State} {t : List (Move F G)}
    {o : Move F G} (hr : h.toReduction.toLTS.Run x (t ++ [o]) y) :
    ∃ y', h.toReduction.toLTS.Run x t y' ∧ h.toReduction.Step y' (some o) y := by
  obtain ⟨y', h₁, h₂⟩ := LTS.Run.of_append hr
  obtain ⟨x', hs, hr'⟩ := run_cons_inv h₂
  obtain rfl := run_nil_inv hr'
  exact ⟨y', h₁, hs⟩

/-- **A one-shot handler below a waiting strategy, forwarding its call**: `hb_zip_run`, the
upper strategy's pending call `m` served by the handler's pending call `e`. -/
theorem hb_zip_wait {h : Handler E F} (hh : OneShot h) {up : List (CRound F G)} {g : G.Op}
    {cs : List (Round F)} {m : F.Op} {s : List (Move E F)} {y : h.toReduction.toLTS.State}
    {p : List (Move E G)} {e : E.Op} (hr : h.toReduction.toLTS.Run .idle s y)
    (hp : Path .idle p (.wait g e)) (hz : Zip s (rplay up g cs ++ [.inl (.ask m)]) p) :
    ∃ (low : List (CRound E G)) (cs' : List (Round E)) (k : E.Ar e → F.Ar m),
      HB h up low ∧ HRounds h cs cs' ∧ h m = .call e (fun r => .pure (k r)) ∧
        p = rplay low g cs' ++ [.inl (.ask e)] := by
  obtain ⟨low', cs'', rfl⟩ := exists_wplay hp
  have htp : Path .idle (rplay up g cs ++ [.inl (.ask m)]) (.wait g m) :=
    (path_rplay up g cs).append (.single (.call g m))
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle (path_hpos hr) htp
  obtain rfl := Path.det hc' hp
  have hy : hpos y = .wait m e := by
    generalize hpos y = b at hcomp
    cases hcomp
    rfl
  -- the handler's last move is its call `e`
  rcases List.eq_nil_or_concat s with rfl | ⟨s', o, rfl⟩
  · obtain rfl := run_nil_inv hr
    cases hy
  rw [List.concat_eq_append] at hr hz
  obtain ⟨y₁, hr₁, hst⟩ := run_snoc_inv hr
  cases hst with
  | ask q => cases hy
  | resume q m' k n => cases hy
  | ret _ => cases hy
  | @call q c e' k hc =>
    simp only [hpos, Pos.wait.injEq] at hy
    obtain ⟨hq, he'⟩ := hy
    subst q
    subst e'
    have hz₁ := zip_snoc_left hz
    -- the handler took the question `m` last
    rcases List.eq_nil_or_concat s' with rfl | ⟨s'', o', rfl⟩
    · cases run_nil_inv hr₁
    rw [List.concat_eq_append] at hr₁ hz₁
    obtain ⟨y₂, hr₂, hst₂⟩ := run_snoc_inv hr₁
    have hc' : c = .call e k := hc
    cases hst₂ with
    | ask q =>
      have hk : h m = .call e k := hc'
      rcases hh m with ⟨a₀, hm⟩ | ⟨e₀, kk, hm⟩
      · rw [hm] at hk
        cases hk
      · obtain ⟨rfl, -⟩ := Prog.call.inj (hm.symm.trans hk)
        obtain ⟨low, cs', H, H', hp'⟩ := hb_zip_run hh hr₂ (zip_snoc_sync hz₁)
        exact ⟨low, cs', kk, H, H', hm, by rw [hp']⟩
    | resume q₀ m₀ k₀ n =>
      exfalso
      obtain ⟨kk, hkk⟩ := (runInv_run hh s'' .idle _ trivial hr₂ :
        ∃ kk : E.Ar m₀ → F.Ar m, k₀ = fun r => .pure (kk r))
      rw [hkk] at hc'
      cases hc'

end Wait

/-! ## A server below -/

theorem lowOf_rplay (cl : List (CRound F G)) (g : G.Op) (cs : List (Round F)) :
    lowOf (E := E) (rplay cl g cs) = twos (cl.flatMap (·.cs) ++ cs) := by
  rw [rplay, lowOf_append, lowOf_cplay, twos_append]
  exact congrArg (twos (cl.flatMap (·.cs)) ++ ·) (lowOf_calls cs)

theorem upOf_rplay (cl : List (CRound F G)) (g : G.Op) (cs : List (Round F)) :
    upOf (E := E) (rplay cl g cs) = twos (cl.map CRound.toRound) ++ [.inr (.ask g)] := by
  rw [rplay, upOf_append, upOf_cplay]
  exact congrArg (twos (cl.map CRound.toRound) ++ ·)
    (congrArg (Sum.inr (Ev.ask g) :: ·) (upOf_calls cs))

/-- **A server below a strategy at `.run g`** (`serve_inv` with a pending round): the server
answered all the lower calls, together and in order; the visible part is the complete rounds,
then `g`. -/
theorem serve_run {s : List (Move E F)} {cl : List (CRound F G)} {g : G.Op}
    {cs : List (Round F)} {p : List (Move E G)} (hs : NoInl s) (hz : Zip s (rplay cl g cs) p) :
    s = twos (cl.flatMap (·.cs) ++ cs) ∧ p = twos (cl.map CRound.toRound) ++ [.inr (.ask g)] := by
  obtain ⟨h₁, h₂⟩ := zip_noInl_left hz hs
  rw [lowOf_rplay] at h₁
  rw [upOf_rplay] at h₂
  exact ⟨h₁, h₂⟩

/-- **A server below a strategy waiting at `.wait g m`**: the server answered the earlier lower
calls and is asked `m`. -/
theorem serve_wait {s : List (Move E F)} {cl : List (CRound F G)} {g : G.Op}
    {cs : List (Round F)} {m : F.Op} {p : List (Move E G)} (hs : NoInl s)
    (hz : Zip s (rplay cl g cs ++ [.inl (.ask m)]) p) :
    s = twos (cl.flatMap (·.cs) ++ cs) ++ [.inr (.ask m)] ∧
      p = twos (cl.map CRound.toRound) ++ [.inr (.ask g)] := by
  obtain ⟨h₁, h₂⟩ := zip_noInl_left hz hs
  rw [lowOf_append, lowOf_rplay] at h₁
  rw [upOf_append, upOf_rplay] at h₂
  simp only [upOf, List.append_nil] at h₂
  exact ⟨h₁, h₂⟩

/-! ## Pairing -/

theorem halves_true_calls {F₁ F₂ : Sig.{0}} (cs : List (Round E)) :
    Split.halves true (callMoves cs : List (Move E (F₁ ⊕ₛ F₂))) = ([], callMoves cs) := by
  have e := halves_calls (F₁ := F₁) (F₂ := F₂) cs []
  rw [List.append_nil] at e
  rw [e]
  simp [Split.halves]

/-- The halves of a pending round of the right component of a pairing. -/
theorem halves_rplay_inr {F₁ F₂ : Sig.{0}} :
    ∀ (b : Bool) (l : List (CRound E F₂)) (g : F₂.Op) (cs : List (Round E)),
      Split.halves b (rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs) = ([], rplay l g cs)
  | b, [], g, cs => by
    show Split.halves b (.inr (.ask (.inr g)) :: callMoves cs) = _
    simp only [Split.halves, halves_true_calls]
    rfl
  | b, ⟨q, cs₀, a⟩ :: l, g, cs => by
    have e : rplay ((⟨q, cs₀, a⟩ :: l).map (CRound.inr (F₁ := F₁))) (.inr g) cs =
        .inr (.ask (.inr q)) :: (callMoves cs₀ ++ (.inr (.ans (.inr q) a) ::
          rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs)) := by
      simp only [rplay, List.map_cons, CRound.inr, cplay, List.cons_append, List.append_assoc]
    rw [e]
    simp only [Split.halves, halves_calls, halves_rplay_inr true l g cs]
    simp only [rplay, cplay, List.cons_append, List.append_assoc]

/-- The halves of a pending round of the right component of a pairing, waiting on the lower
call `m`. -/
theorem halves_wplay_inr {F₁ F₂ : Sig.{0}} :
    ∀ (b : Bool) (l : List (CRound E F₂)) (g : F₂.Op) (cs : List (Round E)) (m : E.Op),
      Split.halves b (rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs ++ [.inl (.ask m)]) =
        ([], rplay l g cs ++ [.inl (.ask m)])
  | b, [], g, cs, m => by
    show Split.halves b (.inr (.ask (.inr g)) :: (callMoves cs ++ [.inl (.ask m)])) = _
    simp only [Split.halves, halves_calls]
    simp [rplay, cplay]
  | b, ⟨q, cs₀, a⟩ :: l, g, cs, m => by
    have e : rplay ((⟨q, cs₀, a⟩ :: l).map (CRound.inr (F₁ := F₁))) (.inr g) cs ++
        [.inl (.ask m)] = .inr (.ask (.inr q)) :: (callMoves cs₀ ++ (.inr (.ans (.inr q) a) ::
          (rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs ++ [.inl (.ask m)]))) := by
      simp only [rplay, List.map_cons, CRound.inr, cplay, List.cons_append, List.append_assoc]
    rw [e]
    simp only [Split.halves, halves_calls, halves_wplay_inr true l g cs m]
    simp only [rplay, cplay, List.cons_append, List.append_assoc]

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
