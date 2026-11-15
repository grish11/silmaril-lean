module

public import Silmaril.Wasi.Component.Accept.Stream.Thms
public import Silmaril.Semantics.StreamMonitors.Thms

/-! # Incremental components as monitors of chunk streams

The safety verdict of `Silmaril.Semantics.StreamMonitors` (#258) on an infinite chunk
stream `cs` is `Chunks.AlwaysAt L cs`: every prefix `cs.prefixAt n` is in `L`. Each finite
play of an incremental component sees finitely many chunks. So the bridge is per prefix:

* `specObs_process_query`: the specified answer after processing chunks `cs` is membership of
  their concatenation;
* `StreamCorrect.answer_eq_prefixAt`: in a correct component, an answer given after
  processing the first `n` chunks of `cs` is `decide (cs.prefixAt n ∈ L)`;
* `alwaysAt_iff_of_answers`: if, for every `n`, some play answers `b n` after the first `n`
  chunks, then the safety verdict holds iff every `b n` is `true`.

The answers are an explicit hypothesis. That a component answers at all is liveness, which
the finite-play strategies do not guarantee. Nothing here observes an infinite play.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept

variable {I X : Set FnName} {fns : StreamFns} {L : ByteLang} [DecidablePred (· ∈ L)]

theorem specFrom_process_query (L : ByteLang) [DecidablePred (· ∈ L)] (w : List UInt8)
    (cs : List (List UInt8)) :
    Silmaril.Acceptor.specFrom L w (cs.map .process ++ [.query]) =
      [Silmaril.Acceptor.member L (w ++ cs.flatten)] := by
  induction cs generalizing w with
  | nil => simp [Silmaril.Acceptor.specFrom]
  | cons c cs ih =>
    simp only [List.map_cons, List.cons_append, Silmaril.Acceptor.specFrom, List.flatten_cons]
    rw [ih]
    simp [Silmaril.ChunkView.toList, List.append_assoc]

/-- The specified answer after processing `cs` from the start. -/
theorem specObs_process_query (L : ByteLang) [DecidablePred (· ∈ L)] (cs : List (List UInt8)) :
    Silmaril.Acceptor.specObs L (cs.map .process ++ [.query]) =
      [Silmaril.Acceptor.member L cs.flatten] := by
  show Silmaril.Acceptor.specFrom L [] _ = _
  rw [specFrom_process_query, List.nil_append]

/-- **A correct component answers the `n`-prefix of a chunk stream by membership.** -/
theorem StreamCorrect.answer_eq_prefixAt {σ : Strategy (nsig I) (nsig X)}
    (h : StreamCorrect fns σ L) (cs : Silmaril.Streams.Chunks UInt8) (n : Nat) {t : List WEv}
    (ht : t ∈ Traces σ) (he : fns.events t = (cs.take n).map .process ++ [.query]) {b : Bool}
    (hb : (fns.answers t)[0]? = some b) : b = decide (cs.prefixAt n ∈ L) := by
  have := h.answer_eq ht hb
  rw [he, specObs_process_query] at this
  simp only [Silmaril.Acceptor.member, List.getElem?_cons_zero, Option.some.injEq] at this
  rw [← this]
  unfold Silmaril.Streams.Chunks.prefixAt
  congr

/-- **The safety verdict from a correct component's answers.** Given, for every `n`, a play
answering `b n` after the first `n` chunks, the stream is always in `L` iff every answer is
`true`. -/
theorem alwaysAt_iff_of_answers {σ : Strategy (nsig I) (nsig X)} (h : StreamCorrect fns σ L)
    (cs : Silmaril.Streams.Chunks UInt8) (b : Nat → Bool)
    (hans : ∀ n, ∃ t ∈ Traces σ, fns.events t = (cs.take n).map .process ++ [.query] ∧
      (fns.answers t)[0]? = some (b n)) :
    Silmaril.Streams.Chunks.AlwaysAt L cs ↔ ∀ n, b n = true := by
  have hb : ∀ n, b n = decide (cs.prefixAt n ∈ L) := fun n => by
    obtain ⟨t, ht, he, ha⟩ := hans n
    exact h.answer_eq_prefixAt cs n ht he ha
  simp only [Silmaril.Streams.Chunks.AlwaysAt, hb, decide_eq_true_eq]

end Silmaril.Wasi.Accept
