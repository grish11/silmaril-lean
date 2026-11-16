module

public import Silmaril.Semantics.Tokens.Defs
public import Silmaril.Semantics.Acceptors.Thms
public import Silmaril.Semantics.Accept.Rel.Defs
import Silmaril.Proofs.Semantics.Tokens.Transducer

/-!
# Token streams: theorems

* Committed tokens grow with the input (`Transducer.emitted_mono`) and compose along
  input concatenation (`Transducer.emitted_append`, `Transducer.state_append`).
* On a chunk stream, the delivered token prefix is `emitted` of the delivered input
  (`prefixAt_tokenChunks`). Rechunking the input does not change the token limit
  (`tokenLimit_eq_of_cofinal`).
* A terminating input stream delivers only the *committed* tokens of its concatenation
  (`tokenLimit_ofList`). The flushed tokens of `tokenize` need an explicit
  end-of-input. A progressive input need not give a progressive token stream
  (`not_productive_silent`).
* `Transducer.pull` is `Silmaril.Accept.pullSome` along the graph of `tokenize`
  (`pull_eq_pullSome`).
* `Acceptor.lex T B` is symbol-correct for `T.pull L` when `B` is symbol-correct for the
  token language `L` (`symbolCorrect_lex`). It is pure with a resetting `reset`, so its
  chunked version is correct on every interleaving of `process`, `query` and `reset`
  (`correctInterleaved_lex`).
-/

public section

namespace Silmaril.Streams.Transducer

open Cslib

universe u v w

variable {ρ : Type u} {α : Type v} {τ : Type w}

theorem state_append (T : Transducer ρ α τ) (u v : List α) :
    T.state (u ++ v) = (T.run (T.state u) v).1 :=
  Silmaril.Proofs.Semantics.Tokens.state_append T u v

theorem emitted_append (T : Transducer ρ α τ) (u v : List α) :
    T.emitted (u ++ v) = T.emitted u ++ (T.run (T.state u) v).2 :=
  Silmaril.Proofs.Semantics.Tokens.emitted_append T u v

/-- Committed tokens are never retracted. -/
theorem emitted_mono (T : Transducer ρ α τ) {u w : List α} (h : u <+: w) :
    T.emitted u <+: T.emitted w :=
  Silmaril.Proofs.Semantics.Tokens.emitted_mono T h

theorem prefixAt_tokenChunks (T : Transducer ρ α τ) (cs : Chunks α) (n : ℕ) :
    (T.tokenChunks cs).prefixAt n = T.emitted (cs.prefixAt n) :=
  Silmaril.Proofs.Semantics.Tokens.prefixAt_tokenChunks T cs n

/-- Rechunking the input does not change the limit of the committed tokens. -/
theorem tokenLimit_eq_of_cofinal (T : Transducer ρ α τ) {cs cs' : Chunks α}
    (h₁ : ∀ n, ∃ m, cs.prefixAt n <+: cs'.prefixAt m)
    (h₂ : ∀ m, ∃ n, cs'.prefixAt m <+: cs.prefixAt n) :
    (T.tokenChunks cs).limit = (T.tokenChunks cs').limit :=
  Silmaril.Proofs.Semantics.Tokens.tokenLimit_eq_of_cofinal T h₁ h₂

/-- A terminating input delivers the committed tokens only; `flush` needs an end-of-input. -/
theorem tokenLimit_ofList (T : Transducer ρ α τ) (cs : List (List α)) :
    (T.tokenChunks (Chunks.ofList cs)).limit = .fin (T.emitted cs.flatten) :=
  Silmaril.Proofs.Semantics.Tokens.tokenLimit_ofList T cs

/-- Progress of the input does not give progress of the tokens. -/
theorem not_productive_silent (cs : Chunks α) :
    ¬ (⟨(), fun _ _ => ((), []), fun _ => []⟩ : Transducer Unit α τ).Productive cs :=
  Silmaril.Proofs.Semantics.Tokens.not_productive_silent cs

/-- `pull` is `Accept.pullSome` along the graph of the whole-input tokenization. -/
theorem pull_eq_pullSome (T : Transducer ρ α τ) (L : Language τ) :
    T.pull L = Silmaril.Accept.pullSome (Silmaril.Accept.ofTotal T.tokenize) L := by
  ext w; simp [pull, Silmaril.Accept.pullSome, SetRel.preimage, Function.graph]; rfl

end Silmaril.Streams.Transducer

namespace Silmaril.Acceptor

open Silmaril.Streams

universe u v w x y

variable {ρ : Type u} {α : Type v} {τ : Type w} {σ : Type x}

theorem foldl_lex (T : Transducer ρ α τ) (B : Acceptor σ τ) (w : List α) :
    w.foldl (lex T B).process (lex T B).init =
      (T.state w, (T.emitted w).foldl B.process B.init) :=
  Silmaril.Proofs.Semantics.Tokens.foldl_lex T B w

theorem pure_lex (T : Transducer ρ α τ) (B : Acceptor σ τ) : (lex T B).Pure := fun _ => rfl

/-- Lexing then accepting tokens decides the pulled-back language. -/
theorem symbolCorrect_lex (T : Transducer ρ α τ) {B : Acceptor σ τ} {L : Language τ}
    [DecidablePred (· ∈ L)] [DecidablePred (· ∈ T.pull L)] (h : B.SymbolCorrect L) :
    (lex T B).SymbolCorrect (T.pull L) :=
  Silmaril.Proofs.Semantics.Tokens.symbolCorrect_lex T h

/-- The chunked composite is correct on every interleaving of client calls. -/
theorem correctInterleaved_lex {χ : Type y} [ChunkView χ α] (T : Transducer ρ α τ)
    {B : Acceptor σ τ} {L : Language τ} [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ T.pull L)] (h : B.SymbolCorrect L) :
    ((lex T B).ofSymbols (χ := χ)).CorrectInterleaved (T.pull L) :=
  correctInterleaved_ofSymbols (pure_lex T B) (fun _ => rfl) (symbolCorrect_lex T h)

end Silmaril.Acceptor
