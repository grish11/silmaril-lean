module

public import Silmaril.Semantics.Tokens.Defs
public import Silmaril.Semantics.Streams.Thms
public import Silmaril.Semantics.Acceptors.Thms

/-! # Proofs: streaming transducers -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Tokens

open Cslib Silmaril.Streams Silmaril.Acceptor

universe u v w x

variable {ρ : Type u} {α : Type v} {τ : Type w} {σ : Type x}

theorem run_append (T : Transducer ρ α τ) (s : ρ) (u v : List α) :
    T.run s (u ++ v) =
      ((T.run (T.run s u).1 v).1, (T.run s u).2 ++ (T.run (T.run s u).1 v).2) := by
  induction u generalizing s with
  | nil => simp [Transducer.run]
  | cons a u ih => simp [Transducer.run, ih]

theorem state_append (T : Transducer ρ α τ) (u v : List α) :
    T.state (u ++ v) = (T.run (T.state u) v).1 := by
  rw [Transducer.state, run_append]; rfl

theorem emitted_append (T : Transducer ρ α τ) (u v : List α) :
    T.emitted (u ++ v) = T.emitted u ++ (T.run (T.state u) v).2 := by
  rw [Transducer.emitted, run_append]; rfl

theorem emitted_mono (T : Transducer ρ α τ) {u w : List α} (h : u <+: w) :
    T.emitted u <+: T.emitted w := by
  obtain ⟨v, rfl⟩ := h
  rw [emitted_append]; exact List.prefix_append _ _

theorem prefixAt_tokenChunks (T : Transducer ρ α τ) (cs : Chunks α) (n : ℕ) :
    (T.tokenChunks cs).prefixAt n = T.emitted (cs.prefixAt n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Chunks.prefixAt_succ, Chunks.prefixAt_succ, ih, emitted_append]; rfl

/-- Rechunking the input does not change the limit of the committed tokens. -/
theorem tokenLimit_eq_of_cofinal (T : Transducer ρ α τ) {cs cs' : Chunks α}
    (h₁ : ∀ n, ∃ m, cs.prefixAt n <+: cs'.prefixAt m)
    (h₂ : ∀ m, ∃ n, cs'.prefixAt m <+: cs.prefixAt n) :
    (T.tokenChunks cs).limit = (T.tokenChunks cs').limit := by
  apply Chunks.limit_eq_of_cofinal
  · intro n
    obtain ⟨m, hm⟩ := h₁ n
    exact ⟨m, by rw [prefixAt_tokenChunks, prefixAt_tokenChunks]; exact emitted_mono T hm⟩
  · intro m
    obtain ⟨n, hn⟩ := h₂ m
    exact ⟨n, by rw [prefixAt_tokenChunks, prefixAt_tokenChunks]; exact emitted_mono T hn⟩

/-- A terminating input commits `emitted` of its concatenation; `flush` is never applied. -/
theorem tokenLimit_ofList (T : Transducer ρ α τ) (cs : List (List α)) :
    (T.tokenChunks (Chunks.ofList cs)).limit = .fin (T.emitted cs.flatten) := by
  refine Chunks.limit_eq_iff.mpr ⟨cs.length, fun n hn => ?_⟩
  rw [prefixAt_tokenChunks, Chunks.prefixAt_ofList, List.take_of_length_le hn]

/-- A transducer that never commits a token is not productive on any input. -/
theorem not_productive_silent (cs : Chunks α) :
    ¬ (⟨(), fun _ _ => ((), []), fun _ => []⟩ : Transducer Unit α τ).Productive cs := by
  intro h
  obtain ⟨n, _, hn⟩ := h 0
  apply hn
  show (Transducer.run _ _ (cs n)).2 = []
  generalize cs n = c
  induction c with
  | nil => rfl
  | cons a c ih => simp only [Transducer.run, List.nil_append]; exact ih

/-! ## The composite acceptor -/

theorem foldl_lex (T : Transducer ρ α τ) (B : Acceptor σ τ) (w : List α) :
    w.foldl (lex T B).process (lex T B).init = (T.state w, (T.emitted w).foldl B.process B.init) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [List.foldl_append, ih, state_append, emitted_append]
    simp [Transducer.run, lex, List.foldl_append]

theorem symbolCorrect_lex (T : Transducer ρ α τ) {B : Acceptor σ τ} {L : Language τ}
    [DecidablePred (· ∈ L)] [DecidablePred (· ∈ T.pull L)] (h : B.SymbolCorrect L) :
    (lex T B).SymbolCorrect (T.pull L) := by
  intro w
  have hw := h (T.tokenize w)
  rw [Transducer.tokenize, List.foldl_append] at hw
  show (B.query ((T.flush _).foldl B.process _)).1 = _
  rw [foldl_lex, hw]
  simp only [member, decide_eq_decide]
  exact Iff.rfl

end Silmaril.Proofs.Semantics.Tokens
