module

public import Silmaril.Wasi.Component.Accept.Stream.Defs
public import Silmaril.Wasi.Component.Accept.Thms

/-! # Components as incremental byte acceptors: theorems

* **Refinement preserves correctness**: a strategy refining a correct one is correct
  (`StreamCorrect.of_le`). Equal named traces and `CompEquiv` IR components preserve it
  (`streamCorrect_congr_traces`, `streamCorrect_compModel_of_compEquiv`).
* **Vacuity**: `⊥` (it never answers) is correct for every language (`streamCorrect_bot`).
  Correctness is about the answers given, not about answering.
* **Answers are sound and complete for the input of any length**: in a correct component,
  once the chunks `w` have been processed and the query is answered, the answer is
  `decide (w ++ … ∈ L)` (`answer_eq_member`). In particular a `true` answer is sound for `L`
  and a `false` answer is sound for the complement, with no bound on the length of `w`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Comp CoreModule)
open Silmaril.Wasm.Component.Algebra (CompEquiv CompRefines)

variable {I X I' X' : Set FnName} {fns : StreamFns} {L : ByteLang} [DecidablePred (· ∈ L)]

theorem StreamCorrect.of_le {σ τ : Strategy (nsig I) (nsig X)} (h : StreamCorrect fns τ L)
    (hle : σ ≤ τ) : StreamCorrect fns σ L :=
  fun t ht => h t (traces_mono hle ht)

theorem streamCorrect_congr_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    StreamCorrect fns σ L ↔ StreamCorrect fns τ L := by
  unfold StreamCorrect; rw [h]

theorem streamCorrect_compModel_of_compEquiv {M : Type} [CoreModule M]
    (C : Silmaril.Wasm.Component.CoreSem M) (Lay : Layout) {c c' : Comp M}
    (h : CompEquiv C c c') :
    StreamCorrect fns (Lay.compModel C c) L ↔ StreamCorrect fns (Lay.compModel C c') L := by
  unfold Layout.compModel; rw [h.2]

theorem StreamCorrect.of_compRefines {M : Type} [CoreModule M]
    (C : Silmaril.Wasm.Component.CoreSem M) (Lay : Layout) {c c' : Comp M}
    (h : CompRefines C c c') (hc : StreamCorrect fns (Lay.compModel C c') L) :
    StreamCorrect fns (Lay.compModel C c) L :=
  hc.of_le (Layout.view_mono Lay h.2)

/-- The bottom strategy answers nothing, so it is (vacuously) correct. -/
theorem streamCorrect_bot : StreamCorrect fns (⊥ : Strategy (nsig I) (nsig X)) L := by
  rintro _ ⟨s, hs, rfl⟩
  rcases Strategy.mem_bot.1 hs with rfl | ⟨q, rfl⟩
  · exact List.nil_prefix
  · have : List.filterMap fns.answer [WEv.call q.1.1 q.2] = [] := rfl
    simp only [wtrace, List.map_cons, List.map_nil, wev, StreamFns.answers, this]
    exact List.nil_prefix

/-- **In a correct component, the `k`-th answer given is the `k`-th specified answer.** For a
play whose events begin with `process w` and `query`, the first answer, if given, is
whether `w ∈ L`: for inputs of any length. -/
theorem StreamCorrect.answer_eq {σ : Strategy (nsig I) (nsig X)} (h : StreamCorrect fns σ L)
    {t : List WEv} (ht : t ∈ Traces σ) {k : Nat} {b : Bool} (hb : (fns.answers t)[k]? = some b) :
    (Silmaril.Acceptor.specObs L (fns.events t))[k]? = some b := by
  obtain ⟨u, hu⟩ := h t ht
  rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hb).1]
  exact hb

/-- The answer after processing `w` from the start is membership of `w`. -/
theorem StreamCorrect.answer_eq_member {σ : Strategy (nsig I) (nsig X)}
    (h : StreamCorrect fns σ L) {t : List WEv} (ht : t ∈ Traces σ) {w : List UInt8}
    {rest : List (Silmaril.Acceptor.Event (List UInt8))}
    (he : fns.events t = .process w :: .query :: rest) {b : Bool}
    (hb : (fns.answers t)[0]? = some b) : b = decide (w ∈ L) := by
  have := h.answer_eq ht hb
  rw [he] at this
  simp [Silmaril.Acceptor.specObs, Silmaril.Acceptor.specFrom, Silmaril.Acceptor.member,
    Silmaril.ChunkView.toList] at this
  exact this.symm

end Silmaril.Wasi.Accept
