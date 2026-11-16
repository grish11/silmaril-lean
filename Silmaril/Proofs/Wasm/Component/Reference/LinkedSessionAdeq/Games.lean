module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Games
public import Silmaril.Proofs.Wasm.Component.Reference.ImpGames

/-!
# Inverting plays of rounds with lower calls

The converse of `ImpGames` (which builds composite plays of rounds with lower calls from plays
of the parts) and the lower-call analogue of `Adequacy.Games` (which inverts plays without lower
calls):

* `exists_cplay`: a play from `idle` to `idle` is `cplay` of rounds with lower calls;
* `serve_inv`: complete rounds of `σ.comp τ`, `σ` without lower moves, are rounds `cl` of `τ`
  whose lower calls, all together and in order, are complete rounds of `σ` (`cplay_comp_serve`
  in reverse);
* `hc_inv`: rounds of `σ.comp (ofHandler h)`, `h` one-shot, come from rounds of `σ` by `HC`
  (`cplay_comp_ofHandler` in reverse);
* `hb_inv`: rounds of `(ofHandler h).comp τ`, `h` one-shot, come from rounds of `τ` by `HB`
  (`cplay_ofHandler_comp` in reverse);
* `cplay_of_pair_inr`: rounds of the right component of a pairing (`cplay_pair_inr` in
  reverse);
* `hc_forall₂`, `hb_forall₂`: `HC` and `HB` round by round.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy

variable {E F G : Sig.{0}}

/-! ## Plays from idle to idle -/

/-- The shape of a play reaching `idle`, by its first position. -/
def Shape : Pos E F → List (Move E F) → Prop
  | .idle, t => ∃ cl : List (CRound E F), t = cplay cl
  | .run q, t => ∃ (cs : List (Round E)) (a : F.Ar q) (cl : List (CRound E F)),
      t = callMoves cs ++ .inr (.ans q a) :: cplay cl
  | .wait q m, t => ∃ (n : E.Ar m) (cs : List (Round E)) (a : F.Ar q) (cl : List (CRound E F)),
      t = .inl (.ans m n) :: (callMoves cs ++ .inr (.ans q a) :: cplay cl)

theorem shape_of_path {x z : Pos E F} {t : List (Move E F)} (h : Path x t z) (hz : z = .idle) :
    Shape x t := by
  induction h with
  | nil x => subst hz; exact ⟨[], rfl⟩
  | cons hs _ ih =>
    have ih := ih hz
    cases hs with
    | ask q =>
      obtain ⟨cs, a, cl, rfl⟩ := ih
      exact ⟨⟨q, cs, a⟩ :: cl, rfl⟩
    | call q m =>
      obtain ⟨n, cs, a, cl, rfl⟩ := ih
      exact ⟨⟨m, n⟩ :: cs, a, cl, rfl⟩
    | reply q m n =>
      obtain ⟨cs, a, cl, rfl⟩ := ih
      exact ⟨n, cs, a, cl, rfl⟩
    | ret q r =>
      obtain ⟨cl, rfl⟩ := ih
      exact ⟨[], r, cl, rfl⟩

/-- **A play from idle to idle is complete rounds with lower calls.** -/
theorem exists_cplay {t : List (Move E F)} (h : Path .idle t .idle) :
    ∃ cl : List (CRound E F), t = cplay cl :=
  shape_of_path h rfl

theorem cplay_ne_inl {low : List (CRound E F)} {a : Ev E} {s : List (Move E F)} :
    cplay low ≠ .inl a :: s := by
  cases low <;> simp [cplay]

theorem callMoves_inr_inj : ∀ {cs cs' : List (Round E)} {x x' : Ev F} {R R' : List (Move E F)},
    callMoves cs ++ .inr x :: R = callMoves cs' ++ .inr x' :: R' → cs = cs' ∧ x = x' ∧ R = R'
  | [], [], _, _, _, _, h => by
    simp only [callMoves, List.nil_append, List.cons.injEq, Sum.inr.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | [], ⟨_, _⟩ :: _, _, _, _, _, h => by simp [callMoves] at h
  | ⟨_, _⟩ :: _, [], _, _, _, _, h => by simp [callMoves] at h
  | ⟨m, n⟩ :: cs, ⟨m', n'⟩ :: cs', _, _, _, _, h => by
    simp only [callMoves, List.cons_append, List.cons.injEq, Sum.inl.injEq, Ev.ask.injEq] at h
    obtain ⟨rfl, h₁, h₂⟩ := h
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    obtain ⟨rfl, h₃, h₄⟩ := callMoves_inr_inj h₂
    exact ⟨by rw [h₁], h₃, h₄⟩

theorem cplay_inj : ∀ {l l' : List (CRound E F)}, cplay l = cplay l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cplay] at h
  | _ :: _, [], h => by simp [cplay] at h
  | ⟨q, cs, a⟩ :: l, ⟨q', cs', a'⟩ :: l', h => by
    simp only [cplay, List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, h₁, h₂⟩ := callMoves_inr_inj h
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    rw [h₁, cplay_inj h₂]

theorem twos_inj' : ∀ {M M' : List (Round F)}, twos (E := E) M = twos M' → M = M'
  | [], [], _ => rfl
  | [], ⟨_, _⟩ :: _, h => by cases h
  | ⟨_, _⟩ :: _, [], h => by cases h
  | ⟨q, a⟩ :: M, ⟨q', a'⟩ :: M', h => by
    have h' : Sum.inr (Ev.ask q) :: Sum.inr (Ev.ans q a) :: twos (E := E) M =
        Sum.inr (Ev.ask q') :: Sum.inr (Ev.ans q' a') :: twos M' := h
    simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at h'
    obtain ⟨rfl, h₁, h₂⟩ := h'
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    rw [h₁, twos_inj' h₂]

/-! ## Interactions -/

section Zip

variable {α β γ : Type}

theorem zip_rr {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {c c' : γ}
    (h : Zip s (.inr c :: t) (.inr c' :: p)) : c' = c ∧ Zip s t p := by
  cases h with
  | right _ h' => exact ⟨rfl, h'⟩

theorem zip_right_of {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {c : γ}
    (h : Zip s (.inr c :: t) p) (hs : ∀ a s', s ≠ .inl a :: s') :
    ∃ p', p = .inr c :: p' ∧ Zip s t p' := by
  cases h with
  | left a _ => exact absurd rfl (hs a _)
  | right _ h' => exact ⟨_, rfl, h'⟩

theorem zip_sync_of {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {b : β}
    (h : Zip s (.inl b :: t) p) (hs : ∀ a s', s ≠ .inl a :: s') :
    ∃ s', s = .inr b :: s' ∧ Zip s' t p := by
  cases h with
  | left a _ => exact absurd rfl (hs a _)
  | sync _ h' => exact ⟨_, rfl, h'⟩

theorem zip_ll {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {a : α} {b : β}
    (h : Zip (.inl a :: s) (.inl b :: t) p) : ∃ p', p = .inl a :: p' ∧ Zip s (.inl b :: t) p' := by
  cases h with
  | left _ h' => exact ⟨_, rfl, h'⟩

theorem zip_sync {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {b b' : β}
    (h : Zip (.inr b :: s) (.inl b' :: t) p) : b = b' ∧ Zip s t p := by
  cases h with
  | sync _ h' => exact ⟨rfl, h'⟩

theorem zip_nil_inl {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {b : β}
    (h : Zip ([] : List (α ⊕ β)) (.inl b :: t) p) : False := by
  cases h

/-- Without moves on the right, every move on the left is visible. -/
theorem zip_nil_right_inr {s : List (α ⊕ β)} {p : List (α ⊕ γ)}
    (h : Zip s ([] : List (β ⊕ γ)) p) : (∀ b, Sum.inr b ∉ s) ∧ ∀ c, Sum.inr c ∉ p := by
  generalize ht : ([] : List (β ⊕ γ)) = t at h
  induction h with
  | nil => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | left a _ ih =>
    obtain ⟨h₁, h₂⟩ := ih ht
    refine ⟨fun b hb => ?_, fun c hc => ?_⟩
    · rcases List.mem_cons.mp hb with hb | hb
      · cases hb
      · exact h₁ b hb
    · rcases List.mem_cons.mp hc with hc | hc
      · cases hc
      · exact h₂ c hc
  | right _ _ _ => cases ht
  | sync _ _ _ => cases ht

/-- The calls of the left trace pass while the right trace waits for an answer. -/
theorem zip_calls_strip {s : List (Move E F)} {b : Ev F} {t : List (Move F G)}
    {p : List (Move E G)} : ∀ (cs : List (Round E)),
      Zip (callMoves cs ++ s) (.inl b :: t) p →
      ∃ p', p = callMoves cs ++ p' ∧ Zip s (.inl b :: t) p'
  | [], h => ⟨p, rfl, h⟩
  | ⟨m, n⟩ :: cs, h => by
    obtain ⟨p₁, rfl, h₁⟩ := zip_ll h
    obtain ⟨p₂, rfl, h₂⟩ := zip_ll h₁
    obtain ⟨p₃, rfl, h₃⟩ := zip_calls_strip cs h₂
    exact ⟨p₃, rfl, h₃⟩

end Zip

/-! ## The lower and upper parts of a play -/

/-- The lower moves of a play of `F ↠ G`, as upper moves of `E ↠ F`. -/
def lowOf : List (Move F G) → List (Move E F)
  | [] => []
  | .inl b :: t => .inr b :: lowOf t
  | .inr _ :: t => lowOf t

/-- The upper moves of a play of `F ↠ G`, as moves of `E ↠ G`. -/
def upOf : List (Move F G) → List (Move E G)
  | [] => []
  | .inl _ :: t => upOf t
  | .inr c :: t => .inr c :: upOf t

theorem zip_noInl_left {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) (hs : NoInl s) : s = lowOf t ∧ p = upOf t := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | left a _ _ => exact absurd List.mem_cons_self (hs a)
  | right c _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hs
    exact ⟨h₁, by rw [h₂]; rfl⟩
  | sync b _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hs.tail
    exact ⟨by rw [h₁]; rfl, h₂⟩

theorem lowOf_append : ∀ (t t' : List (Move F G)),
    lowOf (E := E) (t ++ t') = lowOf t ++ lowOf t'
  | [], _ => rfl
  | .inl b :: t, t' => congrArg (Sum.inr b :: ·) (lowOf_append t t')
  | .inr _ :: t, t' => lowOf_append t t'

theorem upOf_append : ∀ (t t' : List (Move F G)),
    upOf (E := E) (t ++ t') = upOf t ++ upOf t'
  | [], _ => rfl
  | .inl _ :: t, t' => upOf_append t t'
  | .inr c :: t, t' => congrArg (Sum.inr c :: ·) (upOf_append t t')

theorem lowOf_calls : ∀ (cs : List (Round F)),
    lowOf (E := E) (callMoves (F := G) cs) = twos cs
  | [] => rfl
  | ⟨m, n⟩ :: cs =>
    congrArg (fun l => Sum.inr (Ev.ask m) :: Sum.inr (Ev.ans m n) :: l) (lowOf_calls cs)

theorem upOf_calls : ∀ (cs : List (Round F)), upOf (E := E) (callMoves (F := G) cs) = []
  | [] => rfl
  | ⟨_, _⟩ :: cs => upOf_calls cs

/-- A round with its lower calls forgotten. -/
def CRound.toRound (r : CRound E F) : Round F := ⟨r.q, r.a⟩

theorem lowOf_cplay : ∀ (cl : List (CRound F G)),
    lowOf (E := E) (cplay cl) = twos (cl.flatMap (·.cs))
  | [] => rfl
  | r :: cl => by
    show lowOf (callMoves r.cs ++ Sum.inr (Ev.ans r.q r.a) :: cplay cl) = _
    rw [lowOf_append, lowOf_calls, List.flatMap_cons, twos_append]
    exact congrArg (twos r.cs ++ ·) (lowOf_cplay cl)

theorem upOf_cplay : ∀ (cl : List (CRound F G)),
    upOf (E := E) (cplay cl) = twos (cl.map CRound.toRound)
  | [] => rfl
  | r :: cl => by
    show Sum.inr (Ev.ask r.q) :: upOf (callMoves r.cs ++ Sum.inr (Ev.ans r.q r.a) :: cplay cl) = _
    rw [upOf_append, upOf_calls, List.nil_append]
    exact congrArg (fun l => Sum.inr (Ev.ask r.q) :: Sum.inr (Ev.ans r.q r.a) :: l)
      (upOf_cplay cl)

/-! ## A server below -/

/-- **A server below** (`cplay_comp_serve` in reverse): complete rounds of `σ.comp τ`, where `σ`
has no lower moves, are rounds `cl` of `τ` with lower calls, all of which, together and in
order, are complete rounds of `σ`. -/
theorem serve_inv {σ : Strategy E F} {τ : Strategy F G} (hσ : ∀ s ∈ σ, NoInl s)
    {l : List (Round G)} (h : twos l ∈ σ.comp τ) :
    ∃ cl : List (CRound F G), cplay cl ∈ τ ∧ twos (cl.flatMap (·.cs)) ∈ σ ∧
      cl.map CRound.toRound = l := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨a', ha'⟩ := σ.legal hs
  obtain ⟨b', hb'⟩ := τ.legal ht
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle ha' hb'
  have hc'' : c' = .idle := Path.det hc' (path_twos l)
  subst hc''
  obtain ⟨-, rfl⟩ := zipCompat_idle hcomp
  obtain ⟨cl, rfl⟩ := exists_cplay hb'
  obtain ⟨h₁, h₂⟩ := zip_noInl_left hz (hσ s hs)
  rw [lowOf_cplay] at h₁
  rw [upOf_cplay] at h₂
  subst h₁
  exact ⟨cl, ht, hs, (twos_inj' h₂).symm⟩

/-! ## Handler runs -/

theorem run_idle_ne_inl {X Y : Sig.{0}} {h : Handler X Y} {t : List (Move X Y)}
    {y : h.toReduction.State} (hr : h.toReduction.toLTS.Run .idle t y) :
    ∀ a t', t ≠ .inl a :: t' := by
  rintro a t' rfl
  obtain ⟨q, hq, -⟩ := run_idle_cons hr
  cases hq

theorem cplay_ne_inl' {low : List (CRound E F)} : ∀ a s', cplay low ≠ .inl a :: s' :=
  fun _ _ => cplay_ne_inl

theorem inr_not_mem_callMoves {x : Ev F} : ∀ (cs : List (Round E)),
    (Sum.inr x : Move E F) ∉ callMoves cs
  | [], h => nomatch h
  | ⟨_, _⟩ :: cs, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    exact inr_not_mem_callMoves cs h

/-! ## A handler on top -/

section Top

variable {h : Handler F G}

/-- The rounds through a one-shot handler on top. -/
theorem hc_of_zip (hh : OneShot h) :
    ∀ (up : List (CRound E G)) (low : List (CRound E F)) (t : List (Move F G))
      (y : h.toReduction.State),
      h.toReduction.toLTS.Run .idle t y → Zip (cplay low) t (cplay up) → HC h up low
  | [], low, t, y, hr, hz => by
    cases low with
    | nil => exact .nil
    | cons r low =>
      exfalso
      have hz' : Zip (Sum.inr (Ev.ask r.q) :: (callMoves r.cs ++
          Sum.inr (Ev.ans r.q r.a) :: cplay low)) t ([] : List (Move E G)) := hz
      cases t with
      | nil => exact (zip_nil_right_inr hz').1 _ List.mem_cons_self
      | cons m t =>
        obtain ⟨q, rfl, -⟩ := run_idle_cons hr
        cases hz'
  | ⟨g, cs, a⟩ :: up, low, t, y, hr, hz => by
    have hz₀ : Zip (cplay low) t
        (Sum.inr (Ev.ask g) :: (callMoves cs ++ Sum.inr (Ev.ans g a) :: cplay up)) := hz
    have hmem : ∀ R : List (Move E G),
        Sum.inr (Ev.ans g a) ∈ callMoves cs ++ Sum.inr (Ev.ans g a) :: R :=
      fun R => List.mem_append_right _ List.mem_cons_self
    cases t with
    | nil => exact absurd List.mem_cons_self ((zip_nil_right_inr hz₀).2 _)
    | cons m t =>
      obtain ⟨q, rfl, hr₁⟩ := run_idle_cons hr
      obtain ⟨hgq, hz₁⟩ := zip_rr hz₀
      rw [← Ev.ask.inj hgq] at hr₁
      rcases hh g with ⟨a₀, hq⟩ | ⟨f, kk, hq⟩
      · rw [hq] at hr₁
        cases t with
        | nil => exact absurd (hmem _) ((zip_nil_right_inr hz₁).2 _)
        | cons m t =>
          obtain ⟨rfl, hr₂⟩ := run_pure_cons hr₁
          obtain ⟨p', hp, hz₂⟩ := zip_right_of hz₁ cplay_ne_inl'
          have hp' : callMoves cs ++ Sum.inr (Ev.ans g a) :: cplay up =
              callMoves [] ++ Sum.inr (Ev.ans g a₀) :: p' := hp
          obtain ⟨rfl, hx, hR⟩ := callMoves_inr_inj hp'
          have ha : a = a₀ := by simpa only [Ev.ans.injEq, heq_eq_eq, true_and] using hx
          rw [← hR] at hz₂
          rw [← ha] at hq
          exact .pure hq (hc_of_zip hh up low t y hr₂ hz₂)
      · rw [hq] at hr₁
        cases t with
        | nil => exact absurd (hmem _) ((zip_nil_right_inr hz₁).2 _)
        | cons m t =>
          obtain ⟨rfl, hr₂⟩ := run_call_cons hr₁
          obtain ⟨s', hs', hz₂⟩ := zip_sync_of hz₁ cplay_ne_inl'
          cases low with
          | nil => cases hs'
          | cons r low =>
            obtain ⟨f', cs', a'⟩ := r
            have hs'' : Sum.inr (Ev.ask f') :: (callMoves cs' ++
                Sum.inr (Ev.ans f' a') :: cplay low) = Sum.inr (Ev.ask f) :: s' := hs'
            simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at hs''
            obtain ⟨rfl, rfl⟩ := hs''
            cases t with
            | nil =>
              exact ((zip_nil_right_inr hz₂).1 _
                (List.mem_append_right _ List.mem_cons_self)).elim
            | cons m t =>
              obtain ⟨n, rfl, hr₃⟩ := run_wait_cons hr₂
              obtain ⟨P', hP, hz₃⟩ := zip_calls_strip cs' hz₂
              obtain ⟨hn, hz₄⟩ := zip_sync hz₃
              have hn' : a' = n := by simpa only [Ev.ans.injEq, heq_eq_eq, true_and] using hn
              have hr₃' : h.toReduction.toLTS.Run (.run g (.pure (kk n))) t y := hr₃
              cases t with
              | nil =>
                have hm : Sum.inr (Ev.ans g a) ∈ callMoves cs' ++ P' := hP ▸ hmem _
                rcases List.mem_append.mp hm with hm | hm
                · exact (inr_not_mem_callMoves cs' hm).elim
                · exact ((zip_nil_right_inr hz₄).2 _ hm).elim
              | cons m t =>
                obtain ⟨rfl, hr₄⟩ := run_pure_cons hr₃'
                obtain ⟨P'', rfl, hz₅⟩ := zip_right_of hz₄ cplay_ne_inl'
                obtain ⟨rfl, hx, hR⟩ := callMoves_inr_inj hP
                have ha : a = kk n := by
                  simpa only [Ev.ans.injEq, heq_eq_eq, true_and] using hx
                rw [← hR] at hz₅
                rw [hn']
                exact .call hq (by rw [ha]) (hc_of_zip hh up low t y hr₄ hz₅)

/-- **A one-shot handler on top** (`cplay_comp_ofHandler` in reverse). -/
theorem hc_inv {σ : Strategy E F} (hh : OneShot h) {up : List (CRound E G)}
    (hp : cplay up ∈ σ.comp (Strategy.ofHandler h)) : ∃ low, HC h up low ∧ cplay low ∈ σ := by
  obtain ⟨s, hs, t, ht, hz⟩ := hp
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
  obtain ⟨a', ha'⟩ := σ.legal hs
  obtain ⟨b', hb'⟩ := (Strategy.ofHandler h).legal ht
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle ha' hb'
  have hc'' : c' = .idle := Path.det hc' (path_cplay up)
  subst hc''
  obtain ⟨rfl, -⟩ := zipCompat_idle hcomp
  obtain ⟨low, rfl⟩ := exists_cplay ha'
  exact ⟨low, hc_of_zip hh up low t y hy hz, hs⟩

end Top

/-! ## A handler below -/

section Below

variable {h : Handler E F}

/-- The lower calls of a round, served by a one-shot handler below. -/
theorem hb_calls (hh : OneShot h) :
    ∀ (cs : List (Round F)) (s : List (Move E F)) (y : h.toReduction.State)
      (X : List (Move F G)) (p : List (Move E G)),
      h.toReduction.toLTS.Run .idle s y → Zip s (callMoves cs ++ X) p →
      ∃ (cs' : List (Round E)) (s₁ : List (Move E F)) (p₁ : List (Move E G)),
        HRounds h cs cs' ∧ p = callMoves cs' ++ p₁ ∧ h.toReduction.toLTS.Run .idle s₁ y ∧
          Zip s₁ X p₁
  | [], s, y, X, p, hr, hz => ⟨[], s, p, .nil, rfl, hr, hz⟩
  | ⟨f, n⟩ :: cs, s, y, X, p, hr, hz => by
    have hz₀ : Zip s (Sum.inl (Ev.ask f) :: Sum.inl (Ev.ans f n) :: (callMoves cs ++ X)) p := hz
    obtain ⟨s₁, rfl, hz₁⟩ := zip_sync_of hz₀ (run_idle_ne_inl hr)
    obtain ⟨q, hq, hr₁⟩ := run_idle_cons hr
    rw [← Ev.ask.inj (Sum.inr.inj hq)] at hr₁
    rcases hh f with ⟨a₀, hf⟩ | ⟨e, kk, hf⟩
    · rw [hf] at hr₁
      cases s₁ with
      | nil => exact (zip_nil_inl hz₁).elim
      | cons m s₂ =>
        obtain ⟨rfl, hr₂⟩ := run_pure_cons hr₁
        obtain ⟨hn, hz₂⟩ := zip_sync hz₁
        have hn' : a₀ = n := by simpa only [Ev.ans.injEq, heq_eq_eq, true_and] using hn
        obtain ⟨cs', s₃, p₁, H, rfl, hr₃, hz₃⟩ := hb_calls hh cs s₂ y X p hr₂ hz₂
        rw [hn'] at hf
        exact ⟨cs', s₃, p₁, .pure hf H, rfl, hr₃, hz₃⟩
    · rw [hf] at hr₁
      cases s₁ with
      | nil => exact (zip_nil_inl hz₁).elim
      | cons m s₂ =>
        obtain ⟨rfl, hr₂⟩ := run_call_cons hr₁
        obtain ⟨p₂, rfl, hz₂⟩ := zip_ll hz₁
        cases s₂ with
        | nil => exact (zip_nil_inl hz₂).elim
        | cons m s₃ =>
          obtain ⟨n', rfl, hr₃⟩ := run_wait_cons hr₂
          obtain ⟨p₃, rfl, hz₃⟩ := zip_ll hz₂
          have hr₃' : h.toReduction.toLTS.Run (.run f (.pure (kk n'))) s₃ y := hr₃
          cases s₃ with
          | nil => exact (zip_nil_inl hz₃).elim
          | cons m s₄ =>
            obtain ⟨rfl, hr₄⟩ := run_pure_cons hr₃'
            obtain ⟨hn, hz₄⟩ := zip_sync hz₃
            have hn' : kk n' = n := by simpa only [Ev.ans.injEq, heq_eq_eq, true_and] using hn
            obtain ⟨cs', s₅, p₄, H, rfl, hr₅, hz₅⟩ := hb_calls hh cs s₄ y X p₃ hr₄ hz₄
            exact ⟨⟨e, n'⟩ :: cs', s₅, p₄, .call hf (by rw [← hn']) H, rfl, hr₅, hz₅⟩

/-- The rounds through a one-shot handler below. -/
theorem hb_of_zip (hh : OneShot h) :
    ∀ (up : List (CRound F G)) (s : List (Move E F)) (y : h.toReduction.State)
      (p : List (Move E G)),
      h.toReduction.toLTS.Run .idle s y → Zip s (cplay up) p →
      ∃ low : List (CRound E G), HB h up low ∧ p = cplay low
  | [], s, y, p, hr, hz => by
    refine ⟨[], .nil, ?_⟩
    cases s with
    | nil => cases hz; rfl
    | cons m s =>
      obtain ⟨q, rfl, -⟩ := run_idle_cons hr
      cases hz
  | ⟨g, cs, a⟩ :: up, s, y, p, hr, hz => by
    have hz₀ : Zip s (Sum.inr (Ev.ask g) :: (callMoves cs ++ Sum.inr (Ev.ans g a) :: cplay up))
        p := hz
    obtain ⟨p₁, rfl, hz₁⟩ := zip_right_of hz₀ (run_idle_ne_inl hr)
    obtain ⟨cs', s₁, p₂, H, rfl, hr₁, hz₂⟩ := hb_calls hh cs s y _ p₁ hr hz₁
    obtain ⟨p₃, rfl, hz₃⟩ := zip_right_of hz₂ (run_idle_ne_inl hr₁)
    obtain ⟨low, H', rfl⟩ := hb_of_zip hh up s₁ y p₃ hr₁ hz₃
    exact ⟨⟨g, cs', a⟩ :: low, .cons H H', rfl⟩

/-- **A one-shot handler below** (`cplay_ofHandler_comp` in reverse). -/
theorem hb_inv {τ : Strategy F G} (hh : OneShot h) {low : List (CRound E G)}
    (hp : cplay low ∈ (Strategy.ofHandler h).comp τ) : ∃ up, HB h up low ∧ cplay up ∈ τ := by
  obtain ⟨s, hs, t, ht, hz⟩ := hp
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp hs
  obtain ⟨a', ha'⟩ := (Strategy.ofHandler h).legal hs
  obtain ⟨b', hb'⟩ := τ.legal ht
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle ha' hb'
  have hc'' : c' = .idle := Path.det hc' (path_cplay low)
  subst hc''
  obtain ⟨-, rfl⟩ := zipCompat_idle hcomp
  obtain ⟨up, rfl⟩ := exists_cplay hb'
  obtain ⟨low', H, he⟩ := hb_of_zip hh up s y _ hy hz
  rw [cplay_inj he]
  exact ⟨up, H, ht⟩

end Below

/-! ## Pairing -/

/-- **Rounds of the right component of a pairing**, with lower calls (`cplay_pair_inr` in
reverse). -/
theorem cplay_of_pair_inr {F₁ F₂ : Sig.{0}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (CRound E F₂)} (h : cplay (l.map (CRound.inr (F₁ := F₁))) ∈ σ₁.pair σ₂) :
    cplay l ∈ σ₂ := by
  obtain ⟨-, -, h₂⟩ := h
  rw [halves_cplay_inr] at h₂
  exact h₂

/-! ## Round by round -/

/-- A round of `HB`: the same question and answer, the lower calls served by `h`. -/
def HBR (h : Handler E F) (u : CRound F G) (d : CRound E G) : Prop :=
  ∃ (q : G.Op) (a : G.Ar q) (cs : List (Round F)) (cs' : List (Round E)),
    u = ⟨q, cs, a⟩ ∧ d = ⟨q, cs', a⟩ ∧ HRounds h cs cs'

theorem hb_forall₂ {h : Handler E F} {up : List (CRound F G)} {low : List (CRound E G)}
    (H : HB h up low) : List.Forall₂ (HBR h) up low := by
  induction H with
  | nil => exact .nil
  | cons Hc _ ih => exact .cons ⟨_, _, _, _, rfl, rfl, Hc⟩ ih

/-- A round of `HC` answered by one call. -/
def HCR (h : Handler F G) (u : CRound E G) (d : CRound E F) : Prop :=
  ∃ k : F.Ar d.q → Prog F (G.Ar u.q), h u.q = .call d.q k ∧ d.cs = u.cs ∧ k d.a = .pure u.a

theorem hc_forall₂ {h : Handler F G} {up : List (CRound E G)} {low : List (CRound E F)}
    (H : HC h up low) (hn : ∀ r ∈ up, ∀ a, h r.q ≠ .pure a) : List.Forall₂ (HCR h) up low := by
  induction H with
  | nil => exact .nil
  | pure hq _ _ => exact absurd hq (hn _ List.mem_cons_self _)
  | call hq hk _ ih =>
    exact .cons ⟨_, hq, rfl, hk⟩ (ih fun r hr => hn r (List.mem_cons_of_mem _ hr))

section Lists

variable {α β γ : Type}

theorem forall₂_comp {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {a : List α} {b : List β} {c : List γ}, List.Forall₂ R a b → List.Forall₂ S b c →
      List.Forall₂ (fun x z => ∃ y, R x y ∧ S y z) a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons ⟨_, h₁, h₂⟩ (forall₂_comp t₁ t₂)

theorem forall₂_swap {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → List.Forall₂ (fun y x => R x y) b a
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_swap t)

theorem forall₂_map_right {R : α → γ → Prop} {f : β → γ} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a (b.map f) →
      List.Forall₂ (fun x y => R x (f y)) a b
  | [], [], _ => .nil
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | _ :: _, _ :: _, .cons h t => .cons h (forall₂_map_right t)

theorem forall₂_of_map_eq {f : α → γ} {g : β → γ} :
    ∀ {a : List α} {b : List β}, a.map f = b.map g → List.Forall₂ (fun x y => f x = g y) a b
  | [], [], _ => .nil
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq h.2)

end Lists

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
