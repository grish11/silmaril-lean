module

public import Silmaril.Formats.SExp.Reader.Defs

/-! # Proofs: the shared Lisp-family reader is sound, complete and deterministic -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Reader

open Silmaril.Formats Silmaril.Formats.SExpReader

universe u v
variable {A : Type u} {C : Type} {σ : Type v}

/-! ## Lexer runs -/

section Emits
variable {L : Lexer A C σ}

theorem next_token {s s' : σ} {t : Token A C} (h : L.next s = .token t s') :
    L.step s = .token t s' ∧ L.size s' < L.size s := by
  unfold Lexer.next at h
  cases hs : L.step s with
  | token t' r =>
      simp only [hs] at h
      by_cases hlt : L.size r < L.size s
      · simp only [hlt, ite_true, Step.token.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hlt⟩
      · simp [hlt] at h
  | eof => simp [hs] at h
  | error => simp [hs] at h

theorem next_of_step {s s' : σ} {t : Token A C} (h : L.step s = .token t s')
    (hs : L.size s' < L.size s) : L.next s = .token t s' := by
  simp [Lexer.next, h, hs]

theorem emits_nil_iff {s s' : σ} : L.Emits s [] s' ↔ s = s' := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil s

theorem emits_append {s s'' : σ} {ts us : List (Token A C)} :
    L.Emits s (ts ++ us) s'' ↔ ∃ s', L.Emits s ts s' ∧ L.Emits s' us s'' := by
  induction ts generalizing s with
  | nil => exact ⟨fun h => ⟨s, .nil s, h⟩, fun ⟨s', h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | cons t ts ih =>
      constructor
      · intro h
        cases h with
        | cons hn hr =>
            obtain ⟨s', h₁, h₂⟩ := ih.1 hr
            exact ⟨s', .cons hn h₁, h₂⟩
      · rintro ⟨s', h₁, h₂⟩
        cases h₁ with
        | cons hn hr => exact .cons hn (ih.2 ⟨s', hr, h₂⟩)

theorem emits_length {s s' : σ} {ts : List (Token A C)} (h : L.Emits s ts s') :
    ts.length + L.size s' ≤ L.size s := by
  induction h with
  | nil => simp
  | cons hn _ ih =>
      have := (next_token hn).2
      simp only [List.length_cons]; omega

end Emits

/-! ## Shape of derivations -/

theorem gram_datum_cons {m : Mode C} {ts : List (Token A C)} {e : SExp2 A}
    (h : Gram m ts e) (hm : m = .datum) :
    ∃ t ts', ts = t :: ts' ∧ t.startsDatum = true := by
  cases h with
  | atom a => exact ⟨_, _, rfl, rfl⟩
  | coll => exact ⟨_, _, rfl, rfl⟩
  | pre => exact ⟨_, _, rfl, rfl⟩
  | close => cases hm
  | dot => cases hm
  | item => cases hm

/-! ## Soundness -/

section Sound
variable (L : Lexer A C σ) [DecidableEq C]

theorem sound : ∀ n : Nat,
    (∀ t s e s', datumAfter L n t s = some (e, s') →
      ∃ ts, L.Emits s ts s' ∧ Gram .datum (t :: ts) e) ∧
    (∀ s e s', datum L n s = some (e, s') → ∃ ts, L.Emits s ts s' ∧ Gram .datum ts e) ∧
    (∀ c d first s e s', items L n c d first s = some (e, s') →
      ∃ ts, L.Emits s ts s' ∧ Gram (.items c d first) ts e) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [datumAfter, datum, items]
  | succ n ih =>
      obtain ⟨ihA, ihD, ihI⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro t s e s' h
        cases t with
        | atom a =>
            simp only [datumAfter, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨[], .nil _, .atom a⟩
        | «open» hd c d =>
            simp only [datumAfter, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨e', s₁⟩, hi, rfl, rfl⟩ := h
            obtain ⟨ts, he, hg⟩ := ihI c d true s e' s₁ hi
            exact ⟨ts, he, .coll hd c d hg⟩
        | «prefix» p =>
            simp only [datumAfter, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨e', s₁⟩, hi, rfl, rfl⟩ := h
            obtain ⟨ts, he, hg⟩ := ihD s e' s₁ hi
            exact ⟨ts, he, .pre p hg⟩
        | close => simp [datumAfter] at h
        | dot => simp [datumAfter] at h
      · intro s e s' h
        simp only [datum] at h
        split at h
        · rename_i t s₁ hn
          obtain ⟨ts, he, hg⟩ := ihA t s₁ e s' h
          exact ⟨t :: ts, .cons hn he, hg⟩
        · cases h
      · intro c d first s e s' h
        simp only [items] at h
        split at h
        · rename_i c' s₁ hn
          split at h
          · rename_i hc
            subst hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨[.close c'], .cons hn (.nil _), .close c' d first⟩
          · cases h
        · rename_i s₁ hn
          split at h
          · rename_i hdf
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hdf
            obtain ⟨rfl, rfl⟩ := hdf
            split at h
            · rename_i tail s₂ hd
              split at h
              · rename_i c' s₃ hn₂
                split at h
                · rename_i hc
                  subst hc
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨ts, he, hg⟩ := ihD s₁ tail s₂ hd
                  refine ⟨.dot :: ts ++ [.close c'], ?_, .dot c' hg⟩
                  refine .cons hn ?_
                  exact emits_append.2 ⟨s₂, he, .cons hn₂ (.nil _)⟩
                · cases h
              · cases h
            · cases h
          · cases h
        · rename_i t s₁ hclose hdot hn
          split at h
          · rename_i x s₂ hx
            split at h
            · rename_i r s₃ hr
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨ts, he, hg⟩ := ihA t s₁ x s₂ hx
              obtain ⟨us, he₂, hg₂⟩ := ihI c d false s₂ r s₃ hr
              refine ⟨(t :: ts) ++ us, ?_, .item c d first hg hg₂⟩
              exact .cons hn (emits_append.2 ⟨s₂, he, he₂⟩)
            · cases h
          · cases h
        · cases h

theorem datum_sound {n : Nat} {s s' : σ} {e : SExp2 A} (h : datum L n s = some (e, s')) :
    ∃ ts, L.Emits s ts s' ∧ Gram .datum ts e :=
  (sound L n).2.1 s e s' h

end Sound

/-! ## Completeness -/

section Complete
variable (L : Lexer A C σ) [DecidableEq C]

/-- The statement proved by induction on derivations. -/
def Motive : Mode C → List (Token A C) → SExp2 A → Prop
  | .datum, ts, e => ∀ t ts', ts = t :: ts' → ∀ (s s' : σ) (n : Nat), L.Emits s ts' s' →
      2 * ts'.length + 1 ≤ n → datumAfter L n t s = some (e, s')
  | .items c d first, ts, e => ∀ (s s' : σ) (n : Nat), L.Emits s ts s' →
      2 * ts.length ≤ n → items L n c d first s = some (e, s')

theorem datum_of_motive {ts : List (Token A C)} {e : SExp2 A}
    (hg : Gram .datum ts e) (hm : Motive L .datum ts e) {s s' : σ} {n : Nat}
    (he : L.Emits s ts s') (hn : 2 * ts.length ≤ n) : datum L n s = some (e, s') := by
  obtain ⟨t, ts', rfl, -⟩ := gram_datum_cons hg rfl
  cases he with
  | cons hnext hrest =>
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
      simp only [datum, hnext]
      exact hm t ts' rfl _ _ n hrest (by simp at hn; omega)

theorem motive_of_gram {m : Mode C} {ts : List (Token A C)} {e : SExp2 A}
    (h : Gram m ts e) : Motive L m ts e := by
  induction h with
  | atom a =>
      intro t ts' heq s s' n he hn
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [emits_nil_iff] at he
      subst he
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rfl
  | coll hd c d hg ih =>
      intro t ts' heq s s' n he hn
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [datumAfter, ih s s' n he (by omega), Option.bind_eq_bind, Option.bind_some]
  | pre p hg ih =>
      intro t ts' heq s s' n he hn
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [datumAfter, datum_of_motive L hg ih he (n := n) (by omega), Option.bind_eq_bind,
        Option.bind_some]
  | close c d first =>
      intro s s' n he hn
      cases he with
      | cons hnext hrest =>
          rw [emits_nil_iff] at hrest
          subst hrest
          obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
          simp [items, hnext]
  | dot c hg ih =>
      intro s s' n he hn
      cases he with
      | cons hnext hrest =>
          obtain ⟨s₂, h₁, h₂⟩ := emits_append.1 hrest
          cases h₂ with
          | cons hclose hnil =>
              rw [emits_nil_iff] at hnil
              subst hnil
              obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
              simp only [List.length_cons, List.length_append] at hn
              simp [items, hnext, datum_of_motive L hg ih h₁ (n := n) (by omega), hclose]
  | item c d first hx hr ihx ihr =>
      intro s s'' n he hn
      obtain ⟨s₂, h₁, h₂⟩ := emits_append.1 he
      obtain ⟨t, ts', rfl, hstart⟩ := gram_datum_cons hx rfl
      cases h₁ with
      | cons hnext hrest =>
          obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
          simp only [List.cons_append, List.length_cons, List.length_append] at hn
          have hA := ihx t ts' rfl _ _ n hrest (by omega)
          have hI := ihr _ _ n h₂ (by omega)
          cases t with
          | close => simp [Token.startsDatum] at hstart
          | dot => simp [Token.startsDatum] at hstart
          | atom a => simp only [items, hnext]; simp [hA, hI]
          | «open» => simp only [items, hnext]; simp [hA, hI]
          | «prefix» => simp only [items, hnext]; simp [hA, hI]

theorem datum_complete {ts : List (Token A C)} {e : SExp2 A} (hg : Gram .datum ts e)
    {s s' : σ} {n : Nat} (he : L.Emits s ts s') (hn : 2 * ts.length ≤ n) :
    datum L n s = some (e, s') :=
  datum_of_motive L hg (motive_of_gram L hg) he hn

end Complete

/-! ## The reader entry points -/

section Read
variable (L : Lexer A C σ) [DecidableEq C]

theorem readPrefix_iff {s s' : σ} {e : SExp2 A} :
    readPrefix L s = some (e, s') ↔ ∃ ts, L.Emits s ts s' ∧ Gram .datum ts e := by
  constructor
  · exact datum_sound L
  · rintro ⟨ts, he, hg⟩
    have := emits_length he
    exact datum_complete L hg he (by unfold fuel; omega)

theorem read_iff {s : σ} {e : SExp2 A} :
    SExpReader.read L s = some e ↔
      ∃ ts r, L.Emits s ts r ∧ (L.next r).isEof = true ∧ Gram .datum ts e := by
  unfold SExpReader.read
  constructor
  · intro h
    split at h
    · rename_i e' r hp
      split at h
      · cases h
        obtain ⟨ts, he, hg⟩ := (readPrefix_iff L).1 hp
        exact ⟨ts, r, he, by assumption, hg⟩
      · cases h
    · cases h
  · rintro ⟨ts, r, he, heof, hg⟩
    rw [(readPrefix_iff L).2 ⟨ts, he, hg⟩]
    simp [heof]

end Read

/-! ## Determinism: the phrase grammar is unambiguous and prefix-free -/

/-- The lexer that replays a token list. -/
def tokenLexer (A : Type u) (C : Type) : Lexer A C (List (Token A C)) where
  step
    | [] => .eof
    | t :: ts => .token t ts
  size := List.length

theorem emits_tokenLexer (ts rest : List (Token A C)) :
    (tokenLexer A C).Emits (ts ++ rest) ts rest := by
  induction ts with
  | nil => exact .nil _
  | cons t ts ih =>
      refine .cons ?_ ih
      simp [Lexer.next, tokenLexer]

theorem gram_prefix_free [DecidableEq C] {ts us : List (Token A C)} {e e' : SExp2 A}
    (h : Gram .datum ts e) (h' : Gram .datum (ts ++ us) e') : us = [] ∧ e' = e := by
  have h₁ := datum_complete (tokenLexer A C) h (emits_tokenLexer ts us)
    (n := 2 * (ts ++ us).length) (by simp; omega)
  have h₂ := datum_complete (tokenLexer A C) h' (emits_tokenLexer (ts ++ us) [])
    (n := 2 * (ts ++ us).length) (by simp)
  simp only [List.append_nil] at h₂
  rw [h₁] at h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h₂
  exact ⟨h₂.2, h₂.1.symm⟩

theorem gram_unique [DecidableEq C] {ts : List (Token A C)} {e e' : SExp2 A}
    (h : Gram .datum ts e) (h' : Gram .datum ts e') : e' = e :=
  (gram_prefix_free (us := []) h (by simpa using h')).2

/-! ## The encoding: reader results are well formed -/

section Wf
variable (N : Notation A C)

theorem wfItems_mono {first : Bool} {e : SExp2 A} (h : N.wfItems false first e = true) :
    N.wfItems true first e = true := by
  induction e generalizing first with
  | nil => rfl
  | atom a => simp [Notation.wfItems] at h
  | cons x r _ ihr =>
      cases x with
      | atom m =>
          cases hm : N.role m <;> simp_all [Notation.wfItems]
      | nil => simp only [Notation.wfItems, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ihr h.2⟩
      | cons => simp only [Notation.wfItems, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ihr h.2⟩

theorem wfItems_true {d first : Bool} {e : SExp2 A} (h : N.wfItems d first e = true) :
    N.wfItems true first e = true := by
  cases d
  · exact wfItems_mono N h
  · exact h

theorem wf_cons_of_not_atom {x r : SExp2 A} (hx : ∀ m, x ≠ .atom m) :
    N.wf (.cons x r) = (N.wf x && N.wfItems N.listDotted false r) := by
  cases x with
  | atom m => exact absurd rfl (hx m)
  | nil => simp [Notation.wf]
  | cons => simp [Notation.wf]

theorem wfItems_cons_of_not_atom {d first : Bool} {x r : SExp2 A} (hx : ∀ m, x ≠ .atom m) :
    N.wfItems d first (.cons x r) = (N.wf x && N.wfItems d false r) := by
  cases x with
  | atom m => exact absurd rfl (hx m)
  | nil => simp [Notation.wfItems]
  | cons => simp [Notation.wfItems]

theorem wfItems_of_le {d first : Bool} {e : SExp2 A} (hd : d = true → N.listDotted = true)
    (h : N.wfItems d first e = true) : N.wfItems N.listDotted first e = true := by
  cases d
  · cases hl : N.listDotted
    · exact h
    · exact wfItems_mono N h
  · rw [hd rfl]; exact h

theorem wf_of_wfItems_first {d : Bool} {e : SExp2 A} (hd : d = true → N.listDotted = true)
    (h : N.wfItems d true e = true) : N.wf e = true := by
  cases e with
  | nil => rfl
  | atom a => simp [Notation.wfItems] at h
  | cons x r =>
      cases x with
      | atom m =>
          cases hm : N.role m with
          | unwritable => simp_all [Notation.wfItems]
          | plain =>
              simp only [Notation.wfItems, hm] at h
              simp [Notation.wf, hm, wfItems_of_le N hd h]
          | coll => simp [Notation.wfItems, hm] at h
          | «prefix» => simp [Notation.wfItems, hm] at h
      | nil =>
          rw [wfItems_cons_of_not_atom N (by simp)] at h
          rw [wf_cons_of_not_atom N (by simp)]
          simp only [Bool.and_eq_true] at h ⊢
          exact ⟨h.1, wfItems_of_le N hd h.2⟩
      | cons =>
          rw [wfItems_cons_of_not_atom N (by simp)] at h
          rw [wf_cons_of_not_atom N (by simp)]
          simp only [Bool.and_eq_true] at h ⊢
          exact ⟨h.1, wfItems_of_le N hd h.2⟩

theorem wfItems_of_wf {e : SExp2 A} (h : N.wf e = true) : N.wfItems true false e = true := by
  cases e with
  | nil => rfl
  | atom a => simpa [Notation.wf, Notation.wfItems] using h
  | cons x r =>
      cases x with
      | atom m =>
          cases hm : N.role m with
          | unwritable => simp_all [Notation.wf]
          | plain =>
              simp only [Notation.wf, hm] at h
              simp only [Notation.wfItems, hm]
              cases hl : N.listDotted
              · exact wfItems_mono N (hl ▸ h)
              · exact hl ▸ h
          | coll => simp_all [Notation.wf, Notation.wfItems]
          | «prefix» => simp_all [Notation.wf, Notation.wfItems]
      | nil =>
          rw [wf_cons_of_not_atom N (by simp)] at h
          rw [wfItems_cons_of_not_atom N (by simp)]
          simp only [Bool.and_eq_true] at h ⊢
          exact ⟨h.1, wfItems_true N h.2⟩
      | cons =>
          rw [wf_cons_of_not_atom N (by simp)] at h
          rw [wfItems_cons_of_not_atom N (by simp)]
          simp only [Bool.and_eq_true] at h ⊢
          exact ⟨h.1, wfItems_true N h.2⟩

theorem wfItems_single {d : Bool} {e : SExp2 A} (h : N.wf e = true) :
    N.wfItems d false (.cons e .nil) = true := by
  cases e with
  | atom m =>
      have hm : N.role m = .plain := by
        cases hm : N.role m <;> simp_all [Notation.wf, Role.isPlain]
      simp [Notation.wfItems, hm]
  | nil => rw [wfItems_cons_of_not_atom N (by simp)]; simp [h, Notation.wfItems]
  | cons => rw [wfItems_cons_of_not_atom N (by simp)]; simp [h, Notation.wfItems]

/-- What a derivation guarantees about its datum. -/
def WfMotive : Mode C → List (Token A C) → SExp2 A → Prop
  | .datum, _, e => N.wf e = true
  | .items _ d first, _, e => N.wfItems d first e = true

theorem wf_of_gram {m : Mode C} {ts : List (Token A C)} {e : SExp2 A}
    (h : Gram m ts e) (hok : ∀ t ∈ ts, N.TokenOK t) : WfMotive N m ts e := by
  induction h with
  | atom a =>
      have := hok (.atom a) (by simp)
      simp only [Notation.TokenOK] at this
      simp [WfMotive, Notation.wf, this, Role.isPlain]
  | coll hd c d hg ih =>
      have hih := ih (fun t ht => hok t (by simp [ht]))
      have htok := hok _ List.mem_cons_self
      simp only [WfMotive] at hih ⊢
      cases hd with
      | none => exact wf_of_wfItems_first N htok hih
      | some m =>
          simp only [Notation.TokenOK] at htok
          simp [wrap, Notation.wf, htok, hih]
  | pre p hg ih =>
      have hih := ih (fun t ht => hok t (by simp [ht]))
      have htok := hok _ List.mem_cons_self
      simp only [Notation.TokenOK] at htok
      simp only [WfMotive] at hih ⊢
      rcases htok with htok | htok
      · simp [Notation.wf, htok, hih, SExp2.cdr, Notation.wfHead]
      · simp only [Notation.wf, htok]
        exact wfItems_single N hih
  | close => rfl
  | dot c hg ih =>
      have hih := ih (fun t ht => hok t (by simp [ht]))
      exact wfItems_of_wf N hih
  | item c d first hx hr ihx ihr =>
      have h₁ := ihx (fun t ht => hok t (by simp [ht]))
      have h₂ := ihr (fun t ht => hok t (by simp [ht]))
      simp only [WfMotive] at h₁ h₂ ⊢
      rename_i x _
      cases x with
      | atom m =>
          have hm : N.role m = .plain := by
            cases hm : N.role m <;> simp_all [Notation.wf, Role.isPlain]
          simp [Notation.wfItems, hm, h₂]
      | nil => simp [Notation.wfItems, h₁, h₂]
      | cons => simp [Notation.wfItems, h₁, h₂]

end Wf

/-! ## Printing: the tokens of a well-formed datum derive it -/

section Print
variable (N : Notation A C)

theorem tokens_cons_of_not_atom {x r : SExp2 A} (hx : ∀ m, x ≠ .atom m) :
    N.tokens (.cons x r) =
      .open none N.listCloser N.listDotted :: (N.tokens x ++ N.itemTokens N.listCloser r) := by
  cases x with
  | atom m => exact absurd rfl (hx m)
  | nil => simp only [Notation.tokens]; rfl
  | cons => simp only [Notation.tokens]; rfl

theorem itemTokens_cons_of_not_atom {c : C} {x r : SExp2 A} (hx : ∀ m, x ≠ .atom m) :
    N.itemTokens c (.cons x r) = N.tokens x ++ N.itemTokens c r := by
  cases x with
  | atom m => exact absurd rfl (hx m)
  | nil => simp only [Notation.itemTokens]
  | cons => simp only [Notation.itemTokens]

theorem tokens_gram (e : SExp2 A) :
    (N.wf e = true → Gram .datum (N.tokens e) e) ∧
    (∀ c d first, N.wfItems d first e = true → Gram (.items c d first) (N.itemTokens c e) e) ∧
    (∀ y z, e = .cons y z → N.wf y = true → Gram .datum (N.tokens y) y) := by
  induction e with
  | nil =>
      refine ⟨fun _ => ?_, fun c d first _ => ?_, fun y z h => by cases h⟩
      · exact Gram.coll none N.listCloser N.listDotted (Gram.close N.listCloser N.listDotted true)
      · exact Gram.close c d first
  | atom a =>
      refine ⟨fun _ => Gram.atom a, fun c d first h => ?_, fun y z h => by cases h⟩
      simp only [Notation.wfItems, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact Gram.dot c (Gram.atom a)
  | cons x r ihx ihr =>
      obtain ⟨Px, -, -⟩ := ihx
      obtain ⟨-, Qr, Hr⟩ := ihr
      refine ⟨fun h => ?_, fun c d first h => ?_, fun y z h hy => ?_⟩
      · cases x with
        | atom m =>
            cases hm : N.role m with
            | unwritable => simp [Notation.wf, hm] at h
            | plain =>
                simp only [Notation.wf, hm] at h
                simp only [Notation.tokens, hm]
                exact Gram.coll none N.listCloser N.listDotted
                  (Gram.item _ _ true (Gram.atom m) (Qr _ _ false h))
            | coll c d =>
                simp only [Notation.wf, hm] at h
                simp only [Notation.tokens, hm]
                exact Gram.coll (some m) c d (Qr c d true h)
            | «prefix» =>
                simp only [Notation.wf, hm, Bool.and_eq_true, SExp2.isNil_eq_true] at h
                simp only [Notation.tokens, hm]
                cases r with
                | cons y z =>
                    simp only [SExp2.cdr, Notation.wfHead] at h
                    obtain ⟨rfl, hy⟩ := h
                    exact Gram.pre m (Hr y _ rfl hy)
                | nil => simp [Notation.wfHead] at h
                | atom => simp [Notation.wfHead] at h
        | nil =>
            rw [wf_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact Gram.coll none N.listCloser N.listDotted
              (Gram.item _ _ true (Px h.1) (Qr _ _ false h.2))
        | cons =>
            rw [wf_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact Gram.coll none N.listCloser N.listDotted
              (Gram.item _ _ true (Px h.1) (Qr _ _ false h.2))
      · cases x with
        | atom m =>
            cases hm : N.role m with
            | unwritable => simp [Notation.wfItems, hm] at h
            | plain =>
                simp only [Notation.wfItems, hm] at h
                simp only [Notation.itemTokens, hm]
                exact Gram.item c d first (Gram.atom m) (Qr c d false h)
            | coll c' d' =>
                simp only [Notation.wfItems, hm, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                  Bool.not_true] at h
                obtain ⟨⟨rfl, rfl⟩, h⟩ := h
                simp only [Notation.itemTokens, hm]
                exact Gram.dot c (Gram.coll (some m) c' d' (Qr c' d' true h))
            | «prefix» =>
                simp only [Notation.wfItems, hm, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                  Bool.not_true, SExp2.isNil_eq_true] at h
                obtain ⟨⟨⟨rfl, rfl⟩, hz⟩, hy⟩ := h
                simp only [Notation.itemTokens, hm]
                cases r with
                | cons y z =>
                    simp only [SExp2.cdr] at hz
                    subst hz
                    simp only [Notation.wfHead] at hy
                    exact Gram.dot c (Gram.pre m (Hr y _ rfl hy))
                | nil => simp [Notation.wfHead] at hy
                | atom => simp [Notation.wfHead] at hy
        | nil =>
            rw [wfItems_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact Gram.item c d first (Px h.1) (Qr c d false h.2)
        | cons =>
            rw [wfItems_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact Gram.item c d first (Px h.1) (Qr c d false h.2)
      · cases h
        exact Px hy

/-- Tokens a dialect must be able to lex back. -/
def Printable : Token A C → Prop
  | .atom a => N.role a = .plain
  | .open none c d => c = N.listCloser ∧ d = N.listDotted
  | .open (some m) c d => N.role m = .coll c d
  | .prefix p => N.role p = .prefix
  | .close _ => True
  | .dot => N.Dotted

theorem tokens_printable (e : SExp2 A) :
    (N.wf e = true → ∀ t ∈ N.tokens e, Printable N t) ∧
    (∀ c d first, N.wfItems d first e = true → (d = true → N.Dotted) →
      ∀ t ∈ N.itemTokens c e, Printable N t) ∧
    (∀ y z, e = .cons y z → N.wf y = true → ∀ t ∈ N.tokens y, Printable N t) := by
  have listOpen : Printable N (.open none N.listCloser N.listDotted) := ⟨rfl, rfl⟩
  have dotted : N.listDotted = true → N.Dotted := Or.inl
  induction e with
  | nil =>
      refine ⟨fun _ t ht => ?_, fun c d first _ _ t ht => ?_, fun y z h => by cases h⟩
      · simp only [Notation.tokens, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact listOpen
        · exact trivial
      · simp only [Notation.itemTokens, List.mem_singleton] at ht
        subst ht; exact trivial
  | atom a =>
      refine ⟨fun h t ht => ?_, fun c d first h hd t ht => ?_, fun y z h => by cases h⟩
      · simp only [Notation.tokens, List.mem_singleton] at ht
        subst ht
        simp only [Notation.wf] at h
        show N.role a = .plain
        cases hm : N.role a <;> simp_all [Role.isPlain]
      · simp only [Notation.wfItems, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true] at h
        obtain ⟨⟨rfl, rfl⟩, hp⟩ := h
        simp only [Notation.itemTokens, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact hd rfl
        · show N.role a = .plain
          cases hm : N.role a <;> simp_all [Role.isPlain]
        · exact trivial
  | cons x r ihx ihr =>
      obtain ⟨Px, -, -⟩ := ihx
      obtain ⟨-, Qr, Hr⟩ := ihr
      have closeP : ∀ c, Printable N (.close c) := fun _ => trivial
      have atomP : ∀ m, N.role m = .plain → Printable N (.atom m) := fun m hm => hm
      refine ⟨fun h t ht => ?_, fun c d first h hd t ht => ?_, fun y z h hy => ?_⟩
      · cases x with
        | atom m =>
            cases hm : N.role m with
            | unwritable => simp [Notation.wf, hm] at h
            | plain =>
                simp only [Notation.wf, hm] at h
                simp only [Notation.tokens, hm, List.mem_cons] at ht
                rcases ht with rfl | rfl | ht
                · exact listOpen
                · exact atomP m hm
                · exact Qr _ _ false h dotted t ht
            | coll c d =>
                simp only [Notation.wf, hm] at h
                simp only [Notation.tokens, hm, List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hm
                · exact Qr c d true h (fun hd => Or.inr ⟨m, c, hd ▸ hm⟩) t ht
            | «prefix» =>
                simp only [Notation.wf, hm, Bool.and_eq_true, SExp2.isNil_eq_true] at h
                simp only [Notation.tokens, hm, List.mem_cons] at ht
                cases r with
                | cons y z =>
                    simp only [SExp2.cdr, Notation.wfHead] at h
                    simp only [Notation.headTokens] at ht
                    rcases ht with rfl | ht
                    · exact hm
                    · exact Hr y z rfl h.2 t ht
                | nil => simp [Notation.wfHead] at h
                | atom => simp [Notation.wfHead] at h
        | nil =>
            rw [wf_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            rw [tokens_cons_of_not_atom N (by simp)] at ht
            simp only [List.mem_cons, List.mem_append] at ht
            rcases ht with rfl | ht | ht
            · exact listOpen
            · exact Px h.1 t ht
            · exact Qr _ _ false h.2 dotted t ht
        | cons =>
            rw [wf_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            rw [tokens_cons_of_not_atom N (by simp)] at ht
            simp only [List.mem_cons, List.mem_append] at ht
            rcases ht with rfl | ht | ht
            · exact listOpen
            · exact Px h.1 t ht
            · exact Qr _ _ false h.2 dotted t ht
      · cases x with
        | atom m =>
            cases hm : N.role m with
            | unwritable => simp [Notation.wfItems, hm] at h
            | plain =>
                simp only [Notation.wfItems, hm] at h
                simp only [Notation.itemTokens, hm, List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact atomP m hm
                · exact Qr c d false h hd t ht
            | coll c' d' =>
                simp only [Notation.wfItems, hm, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                  Bool.not_true] at h
                obtain ⟨⟨rfl, rfl⟩, h⟩ := h
                simp only [Notation.itemTokens, hm, List.mem_cons, List.mem_append,
                  List.not_mem_nil, or_false] at ht
                rcases ht with (rfl | rfl | ht) | rfl
                · exact hd rfl
                · exact hm
                · exact Qr c' d' true h (fun hd' => Or.inr ⟨m, c', hd' ▸ hm⟩) t ht
                · exact closeP c
            | «prefix» =>
                simp only [Notation.wfItems, hm, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                  Bool.not_true, SExp2.isNil_eq_true] at h
                obtain ⟨⟨⟨rfl, rfl⟩, hz⟩, hy⟩ := h
                simp only [Notation.itemTokens, hm, List.mem_cons, List.mem_append,
                  List.not_mem_nil, or_false] at ht
                cases r with
                | cons y z =>
                    simp only [Notation.wfHead] at hy
                    simp only [Notation.headTokens] at ht
                    rcases ht with (rfl | rfl | ht) | rfl
                    · exact hd rfl
                    · exact hm
                    · exact Hr y z rfl hy t ht
                    · exact closeP c
                | nil => simp [Notation.wfHead] at hy
                | atom => simp [Notation.wfHead] at hy
        | nil =>
            rw [wfItems_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            rw [itemTokens_cons_of_not_atom N (by simp)] at ht
            simp only [List.mem_append] at ht
            rcases ht with ht | ht
            · exact Px h.1 t ht
            · exact Qr c d false h.2 hd t ht
        | cons =>
            rw [wfItems_cons_of_not_atom N (by simp)] at h
            simp only [Bool.and_eq_true] at h
            rw [itemTokens_cons_of_not_atom N (by simp)] at ht
            simp only [List.mem_append] at ht
            rcases ht with ht | ht
            · exact Px h.1 t ht
            · exact Qr c d false h.2 hd t ht
      · cases h
        exact Px hy

end Print

/-! ## Every derivation ends with an atom or a closer -/

def EndsWell : Mode C → List (Token A C) → Prop
  | .datum, ts => ∃ init t, ts = init ++ [t] ∧ (t.isClose = true ∨ ∃ a, t = .atom a)
  | .items c _ _, ts => ∃ init, ts = init ++ [.close c]

theorem gram_endsWell {m : Mode C} {ts : List (Token A C)} {e : SExp2 A} (h : Gram m ts e) :
    EndsWell m ts := by
  induction h with
  | atom a => exact ⟨[], _, rfl, Or.inr ⟨a, rfl⟩⟩
  | coll hd c d _ ih =>
      obtain ⟨init, rfl⟩ := ih
      exact ⟨.open hd c d :: init, _, rfl, Or.inl rfl⟩
  | pre p _ ih =>
      obtain ⟨init, t, rfl, ht⟩ := ih
      exact ⟨.prefix p :: init, t, rfl, ht⟩
  | close c d first => exact ⟨[], rfl⟩
  | dot c _ _ => exact ⟨_, rfl⟩
  | item c d first _ _ _ ihr =>
      obtain ⟨init, rfl⟩ := ihr
      exact ⟨_ ++ init, (List.append_assoc _ _ _).symm⟩

/-! ## Rendering: printed text lexes back to the printed tokens -/

section Render
variable {L : Lexer A C (List Char)} {text : Token A C → List Char}

/-- The lexing law of one token. -/
def TokLaw (L : Lexer A C (List Char)) (text : Token A C → List Char) :
    Token A C → Prop
  | .atom a => ∀ rest, Follows text rest → L.step (text (.atom a) ++ rest) = .token (.atom a) rest
  | .dot => ∀ rest, Follows text rest → L.step (text .dot ++ rest) = .token .dot rest
  | .open h c d => ∀ rest, L.step (text (.open h c d) ++ rest) = .token (.open h c d) rest
  | .close c => ∀ rest, L.step (text (.close c) ++ rest) = .token (.close c) rest
  | .prefix p => ∀ rest, L.step (text (.prefix p) ++ ' ' :: rest) = .token (.prefix p) (' ' :: rest)

theorem tokLaw_of_printable {N : Notation A C} (hl : PrintLaws N L text) {t : Token A C}
    (ht : Printable N t) : TokLaw L text t := by
  cases t with
  | atom a => exact fun rest hr => hl.atom a rest ht hr
  | dot => exact fun rest hr => hl.dot ht rest hr
  | «open» h c d =>
      cases h with
      | none => obtain ⟨rfl, rfl⟩ := ht; exact fun rest => hl.openList rest
      | some m => exact fun rest => hl.openColl m c d rest ht
  | close c => exact fun rest => hl.close c rest
  | «prefix» p => exact fun rest => hl.prefix p rest ht

theorem render_cons (u : Token A C) (ts : List (Token A C)) :
    ∃ w, render text (u :: ts) = text u ++ w := by
  cases ts with
  | nil => exact ⟨[], by simp only [render, List.append_nil]⟩
  | cons v ts => exact ⟨sep u v ++ render text (v :: ts), by simp [render]⟩

theorem emits_space (hsize : ∀ s, L.size s = s.length) (hspace : ∀ s, L.step (' ' :: s) = L.step s)
    {s r : List Char} {ts : List (Token A C)} (h : L.Emits s ts r) (hne : ts ≠ []) :
    L.Emits (' ' :: s) ts r := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hn hrest =>
      obtain ⟨hs, hlt⟩ := next_token hn
      refine .cons (next_of_step (by rw [hspace]; exact hs) ?_) hrest
      rw [hsize, hsize] at hlt; rw [hsize ((' ' :: s)), hsize]; exact Nat.lt_succ_of_lt hlt

theorem emits_render (hsize : ∀ s, L.size s = s.length)
    (hspace : ∀ s, L.step (' ' :: s) = L.step s) (hne : ∀ t, text t ≠ [])
    {ts : List (Token A C)} (hlaw : ∀ t ∈ ts, TokLaw L text t) (hts : ts ≠ [])
    (hend : ∃ init t, ts = init ++ [t] ∧ (t.isClose = true ∨ ∃ a, t = .atom a))
    {rest : List Char} (hrest : Follows text rest) :
    L.Emits (render text ts ++ rest) ts rest := by
  have step_next : ∀ {t : Token A C} {w : List Char},
      L.step (text t ++ w) = .token t w → L.next (text t ++ w) = .token t w := by
    intro t w h
    refine next_of_step h ?_
    rw [hsize, hsize, List.length_append]
    have := List.length_pos_iff.2 (hne t); omega
  induction ts with
  | nil => exact absurd rfl hts
  | cons t ts ih =>
      cases ts with
      | nil =>
          obtain ⟨init, t', heq, ht'⟩ := hend
          have : t' = t := by
            cases init with
            | nil => simpa using heq.symm
            | cons _ init => cases init <;> simp at heq
          subst this
          have hstep : L.step (text t' ++ rest) = .token t' rest := by
            have hl := hlaw t' (by simp)
            rcases ht' with hc | ⟨a, rfl⟩
            · cases t' <;> simp [Token.isClose] at hc
              exact hl rest
            · exact hl rest hrest
          exact .cons (step_next hstep) (.nil _)
      | cons u ts =>
          have ih' := ih (fun t ht => hlaw t (by simp [ht])) (by simp) (by
            obtain ⟨init, t', heq, ht'⟩ := hend
            cases init with
            | nil => simp at heq
            | cons _ init =>
              simp only [List.cons_append, List.cons.injEq] at heq
              exact ⟨init, t', heq.2, ht'⟩)
          obtain ⟨w, hw⟩ := render_cons (text := text) u ts
          have hrender : render text (t :: u :: ts) ++ rest =
              text t ++ (sep t u ++ (render text (u :: ts) ++ rest)) := by
            show (text t ++ sep t u ++ render text (u :: ts)) ++ rest = _
            simp only [List.append_assoc]
          rw [hrender]
          have hl := hlaw t (by simp)
          have hfollow : t.isOpen = false → t.isPrefix = false →
              Follows text (sep t u ++ (render text (u :: ts) ++ rest)) := by
            intro hto htp
            cases hu : u.isClose
            · have : sep t u = [' '] := by simp [sep, hto, hu]
              rw [this]; right; left; exact ⟨_, rfl⟩
            · have : sep t u = [] := by simp [sep, hto, hu, htp]
              rw [this, hw]
              cases u with
              | close c => right; right; exact ⟨c, w ++ rest, by simp⟩
              | _ => simp [Token.isClose] at hu
          have hstep : L.step (text t ++ (sep t u ++ (render text (u :: ts) ++ rest))) =
              .token t (sep t u ++ (render text (u :: ts) ++ rest)) := by
            cases t with
            | atom a => exact hl _ (hfollow rfl rfl)
            | dot => exact hl _ (hfollow rfl rfl)
            | «open» => exact hl _
            | close => exact hl _
            | «prefix» p =>
                have : sep (.prefix p) u = [' '] := by simp [sep, Token.isOpen, Token.isPrefix]
                rw [this]; exact hl _
          refine .cons (step_next hstep) ?_
          unfold sep
          split
          · exact ih'
          · exact emits_space hsize hspace ih' (by simp)

end Render

/-! ## The roundtrip -/

section Roundtrip
variable {N : Notation A C} {L : Lexer A C (List Char)} {text : Token A C → List Char}

theorem emits_print (hl : PrintLaws N L text) {e : SExp2 A} (he : N.wf e = true)
    {rest : List Char} (hrest : Follows text rest) :
    L.Emits (print N text e ++ rest) (N.tokens e) rest := by
  have hg := (tokens_gram N e).1 he
  obtain ⟨init, t, heq, ht⟩ := gram_endsWell hg
  refine emits_render hl.size_eq hl.space hl.nonempty
    (fun t ht => tokLaw_of_printable hl ((tokens_printable N e).1 he t ht)) ?_
    ⟨init, t, heq, ht⟩ hrest
  rw [heq]; simp

theorem readPrefix_print [DecidableEq C] (hl : PrintLaws N L text) {e : SExp2 A} (he : N.wf e = true)
    {rest : List Char} (hrest : Follows text rest) :
    readPrefix L (print N text e ++ rest) = some (e, rest) :=
  (readPrefix_iff L).2 ⟨_, emits_print hl he hrest, (tokens_gram N e).1 he⟩

theorem read_print [DecidableEq C] (hl : PrintLaws N L text) {e : SExp2 A} (he : N.wf e = true) :
    SExpReader.read L (print N text e) = some e := by
  have h := emits_print hl he (rest := []) (Or.inl rfl)
  rw [List.append_nil] at h
  refine (read_iff L).2 ⟨_, [], h, ?_, (tokens_gram N e).1 he⟩
  simp [Lexer.next, hl.eof, Step.isEof]

/-- Tokens produced by a lexer all come from single steps. -/
theorem emits_step {L : Lexer A C σ} {s s' : σ} {ts : List (Token A C)}
    (h : L.Emits s ts s') : ∀ t ∈ ts, ∃ s₁ s₂, L.step s₁ = .token t s₂ := by
  induction h with
  | nil => simp
  | cons hn _ ih =>
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ⟨_, _, (next_token hn).1⟩
      · exact ih t ht

theorem wf_of_readPrefix [DecidableEq C] {L : Lexer A C σ}
    (hok : ∀ s t s', L.step s = .token t s' → N.TokenOK t)
    {s s' : σ} {e : SExp2 A} (h : readPrefix L s = some (e, s')) : N.wf e = true := by
  obtain ⟨ts, he, hg⟩ := (readPrefix_iff L).1 h
  exact wf_of_gram N hg fun t ht => by
    obtain ⟨_, _, hs⟩ := emits_step he t ht
    exact hok _ _ _ hs

theorem wf_of_read [DecidableEq C] {L : Lexer A C σ}
    (hok : ∀ s t s', L.step s = .token t s' → N.TokenOK t)
    {s : σ} {e : SExp2 A} (h : SExpReader.read L s = some e) : N.wf e = true := by
  obtain ⟨ts, r, he, -, hg⟩ := (read_iff L).1 h
  exact wf_of_gram N hg fun t ht => by
    obtain ⟨_, _, hs⟩ := emits_step he t ht
    exact hok _ _ _ hs

end Roundtrip

end Silmaril.Proofs.Formats.SExp.Reader
