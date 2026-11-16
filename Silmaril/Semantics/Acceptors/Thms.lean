module

public import Silmaril.Semantics.Acceptors.Defs
public import Silmaril.Semantics.Accept.Defs
import Silmaril.Proofs.Semantics.Acceptors.Basic
import Silmaril.Proofs.Semantics.Acceptors.Chunks

/-!
# Incremental acceptors: theorems

Theorems about `Silmaril.Semantics.Acceptors.Defs`. Proofs longer than a few lines live
under `Silmaril.Proofs.Semantics.Acceptors` and are only pointed at from here.

* The specification: `specObs_append_query` answers a final query by membership of the
  flattened `pending` chunks.
* The hierarchy: `CorrectInterleaved.correctFold` and `CorrectInterleaved.correctImmediate`
  hold unconditionally. For a `Pure` acceptor with `ResetSound`,
  `correctInterleaved_iff_correctFold` and `correctInterleaved_iff_correctImmediate`.
* Purity is needed: `answerOnce` is `CorrectFold`, `CorrectImmediate` and `ResetSound` but not
  `CorrectInterleaved`; `finalizing` is `CorrectFold` and `ResetSound` but not
  `CorrectImmediate`, for any language that separates suitable chunks.
* Chunking: the answers of a correct acceptor depend only on `toSymbolTrace`, so regrouping
  chunks and inserting or removing empty chunks changes no answer.
* Symbols: `ofSymbols` lifts a `SymbolCorrect` acceptor to a `CorrectFold` (and, when pure with
  `reset` returning `init`, `CorrectInterleaved`) chunk acceptor; `toSymbols` restricts back.
* Every language with decidable membership has a `CorrectInterleaved` acceptor (`reference`).
-/

public section

namespace Silmaril

universe u v w

namespace ChunkView

variable {α : Type w}

@[simp] theorem toList_list (l : List α) : ChunkView.toList l = l := rfl

@[simp] theorem toList_array (a : Array α) : ChunkView.toList a = a.toList := rfl

@[simp] theorem toList_byteArray (b : ByteArray) : ChunkView.toList b = b.data.toList := rfl

end ChunkView

namespace Acceptor

variable {σ : Type u} {χ : Type v} {α : Type w}

@[simp] theorem member_eq_true (L : Language α) [DecidablePred (· ∈ L)] (w : List α) :
    member L w = true ↔ w ∈ L := decide_eq_true_iff

/-! ## Running traces -/

theorem run_append (A : Acceptor σ χ) (s : σ) (t₁ t₂ : List (Event χ)) :
    A.run s (t₁ ++ t₂) =
      ((A.run s t₁).1 ++ (A.run (A.run s t₁).2 t₂).1, (A.run (A.run s t₁).2 t₂).2) :=
  Silmaril.Proofs.Semantics.Acceptors.run_append A s t₁ t₂

/-- Processing chunks one after another is folding `process`. -/
theorem run_map_process (A : Acceptor σ χ) (s : σ) (cs : List χ) (tr : List (Event χ)) :
    A.run s (cs.map .process ++ tr) = A.run (cs.foldl A.process s) tr :=
  Silmaril.Proofs.Semantics.Acceptors.run_map_process A s cs tr

theorem ResetSound.of_eq {A : Acceptor σ χ} (h : ∀ s, A.reset s = A.init) : A.ResetSound :=
  fun s _ => by rw [h]

/-! ## The specification -/

/-- A final query is answered by membership of the chunks since the last reset. -/
theorem specObs_append_query [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)]
    (tr : List (Event χ)) :
    specObs L (tr ++ [.query]) =
      specObs L tr ++ [member L ((pending tr).flatMap ChunkView.toList)] :=
  Silmaril.Proofs.Semantics.Acceptors.specFrom_append_query L [] tr

variable [ChunkView χ α] {L : Language α} [DecidablePred (· ∈ L)]

/-! ## The correctness hierarchy -/

theorem CorrectInterleaved.correctFold {A : Acceptor σ χ} (h : A.CorrectInterleaved L) :
    A.CorrectFold L :=
  Silmaril.Proofs.Semantics.Acceptors.correctFold_of_correctInterleaved h

theorem CorrectInterleaved.correctImmediate {A : Acceptor σ χ} (h : A.CorrectInterleaved L) :
    A.CorrectImmediate L :=
  fun tr _ => h tr

/-- For a pure acceptor with a sound reset, single queries after folding suffice. -/
theorem correctInterleaved_of_correctFold {A : Acceptor σ χ} (hp : A.Pure) (hr : A.ResetSound)
    (h : A.CorrectFold L) : A.CorrectInterleaved L :=
  Silmaril.Proofs.Semantics.Acceptors.correctInterleaved_of_correctFold hp hr h

/-- For a pure acceptor, the immediate-query protocol determines fold correctness. -/
theorem correctFold_of_correctImmediate {A : Acceptor σ χ} (hp : A.Pure)
    (h : A.CorrectImmediate L) : A.CorrectFold L :=
  Silmaril.Proofs.Semantics.Acceptors.correctFold_of_correctImmediate hp h

theorem correctInterleaved_iff_correctFold {A : Acceptor σ χ} (hp : A.Pure)
    (hr : A.ResetSound) : A.CorrectInterleaved L ↔ A.CorrectFold L :=
  ⟨CorrectInterleaved.correctFold, correctInterleaved_of_correctFold hp hr⟩

theorem correctInterleaved_iff_correctImmediate {A : Acceptor σ χ} (hp : A.Pure)
    (hr : A.ResetSound) : A.CorrectInterleaved L ↔ A.CorrectImmediate L :=
  ⟨CorrectInterleaved.correctImmediate,
    fun h => correctInterleaved_of_correctFold hp hr (correctFold_of_correctImmediate hp h)⟩

/-! ## Purity is needed -/

theorem answerOnce_resetSound : (answerOnce (χ := χ) L).ResetSound :=
  ResetSound.of_eq fun _ => rfl

theorem answerOnce_correctFold : (answerOnce (χ := χ) L).CorrectFold L :=
  Silmaril.Proofs.Semantics.Acceptors.answerOnce_correctFold L

theorem answerOnce_correctImmediate : (answerOnce (χ := χ) L).CorrectImmediate L :=
  Silmaril.Proofs.Semantics.Acceptors.answerOnce_correctImmediate L

/-- Two queries in a row expose `answerOnce` as soon as some chunk is accepted. -/
theorem answerOnce_not_correctInterleaved (c : χ) (hc : ChunkView.toList c ∈ L) :
    ¬ (answerOnce (χ := χ) L).CorrectInterleaved L :=
  Silmaril.Proofs.Semantics.Acceptors.answerOnce_not_correctInterleaved L c hc

theorem finalizing_resetSound : (finalizing (χ := χ) L).ResetSound :=
  ResetSound.of_eq fun _ => rfl

theorem finalizing_correctFold : (finalizing (χ := χ) L).CorrectFold L :=
  Silmaril.Proofs.Semantics.Acceptors.finalizing_correctFold L

/-- Processing after a query exposes `finalizing` when `L` separates `c₁ ++ c₂` from `c₂`. -/
theorem finalizing_not_correctImmediate (c₁ c₂ : χ)
    (h₁ : ChunkView.toList c₁ ++ ChunkView.toList c₂ ∈ L) (h₂ : ChunkView.toList c₂ ∉ L) :
    ¬ (finalizing (χ := χ) L).CorrectImmediate L :=
  Silmaril.Proofs.Semantics.Acceptors.finalizing_not_correctImmediate L c₁ c₂ h₁ h₂

/-! ## Chunking independence -/

/-- The specification depends only on the symbol-level trace. -/
theorem specObs_toSymbolTrace (tr : List (Event χ)) :
    specObs L (toSymbolTrace tr) = specObs L tr :=
  Silmaril.Proofs.Semantics.Acceptors.specFrom_toSymbolTrace L [] tr

/-- Traces over possibly different chunk types with the same symbol-level trace have the
same specified answers. -/
theorem specObs_eq_of_toSymbolTrace_eq {χ₁ : Type v} {χ₂ : Type u} [ChunkView χ₁ α]
    [ChunkView χ₂ α] {tr₁ : List (Event χ₁)} {tr₂ : List (Event χ₂)}
    (h : toSymbolTrace tr₁ = toSymbolTrace tr₂) : specObs L tr₁ = specObs L tr₂ :=
  Silmaril.Proofs.Semantics.Acceptors.specObs_eq_of_toSymbolTrace_eq L h

/-- A correct acceptor's answers depend only on the flattened input between queries and
resets, not on how it was split into chunks. -/
theorem CorrectInterleaved.run_eq_of_toSymbolTrace_eq {A : Acceptor σ χ}
    (hA : A.CorrectInterleaved L) {tr₁ tr₂ : List (Event χ)}
    (h : toSymbolTrace tr₁ = toSymbolTrace tr₂) :
    (A.run A.init tr₁).1 = (A.run A.init tr₂).1 := by
  rw [hA, hA, specObs_eq_of_toSymbolTrace_eq h]

theorem toSymbolTrace_process_nil (pre post : List (Event χ)) (c : χ)
    (hc : ChunkView.toList c = []) :
    toSymbolTrace (pre ++ .process c :: post) = toSymbolTrace (pre ++ post) :=
  Silmaril.Proofs.Semantics.Acceptors.toSymbolTrace_process_nil pre post c hc

/-- Processing an empty chunk changes no answer of a correct acceptor. -/
theorem CorrectInterleaved.run_process_nil {A : Acceptor σ χ} (hA : A.CorrectInterleaved L)
    (pre post : List (Event χ)) (c : χ) (hc : ChunkView.toList c = []) :
    (A.run A.init (pre ++ .process c :: post)).1 = (A.run A.init (pre ++ post)).1 :=
  hA.run_eq_of_toSymbolTrace_eq (toSymbolTrace_process_nil pre post c hc)

/-! ## Symbol-at-a-time acceptors -/

theorem pure_ofSymbols {B : Acceptor σ α} : (B.ofSymbols (χ := χ)).Pure ↔ B.Pure := Iff.rfl

theorem correctFold_ofSymbols {B : Acceptor σ α} (h : B.SymbolCorrect L) :
    (B.ofSymbols (χ := χ)).CorrectFold L :=
  Silmaril.Proofs.Semantics.Acceptors.correctFold_ofSymbols h

theorem correctInterleaved_ofSymbols {B : Acceptor σ α} (hp : B.Pure)
    (hr : ∀ s, B.reset s = B.init) (h : B.SymbolCorrect L) :
    (B.ofSymbols (χ := χ)).CorrectInterleaved L :=
  correctInterleaved_of_correctFold hp (ResetSound.of_eq hr) (correctFold_ofSymbols h)

/-- Restricting a fold-correct chunk acceptor to one-symbol chunks is symbol-correct. -/
theorem symbolCorrect_toSymbols {A : Acceptor σ χ} (single : α → χ)
    (hs : ∀ a, ChunkView.toList (single a) = [a]) (h : A.CorrectFold L) :
    (A.toSymbols single).SymbolCorrect L :=
  Silmaril.Proofs.Semantics.Acceptors.symbolCorrect_toSymbols single hs h

/-- Lifting to chunks and restricting to one-symbol chunks gives back the symbol acceptor. -/
theorem toSymbols_ofSymbols (B : Acceptor σ α) (single : α → χ)
    (hs : ∀ a, ChunkView.toList (single a) = [a]) :
    (B.ofSymbols (χ := χ)).toSymbols single = B :=
  Silmaril.Proofs.Semantics.Acceptors.toSymbols_ofSymbols B single hs

/-- A fold-correct chunk acceptor is refined by the symbol-at-a-time acceptor it induces:
reading every chunk symbol by symbol is again fold-correct. -/
theorem correctFold_ofSymbols_toSymbols {A : Acceptor σ χ} (single : α → χ)
    (hs : ∀ a, ChunkView.toList (single a) = [a]) (h : A.CorrectFold L) :
    ((A.toSymbols single).ofSymbols (χ := χ)).CorrectFold L :=
  correctFold_ofSymbols (symbolCorrect_toSymbols single hs h)

/-! ## The reference acceptor -/

theorem reference_pure : (reference (χ := χ) L).Pure := fun _ => rfl

theorem reference_resetSound : (reference (χ := χ) L).ResetSound :=
  ResetSound.of_eq fun _ => rfl

theorem reference_correctFold : (reference (χ := χ) L).CorrectFold L :=
  Silmaril.Proofs.Semantics.Acceptors.reference_correctFold L

theorem reference_correctInterleaved : (reference (χ := χ) L).CorrectInterleaved L :=
  correctInterleaved_of_correctFold reference_pure reference_resetSound reference_correctFold

/-- Every language with decidable membership has an interleaving-correct acceptor. -/
theorem exists_correctInterleaved (L : Language α) [DecidablePred (· ∈ L)] :
    ∃ A : Acceptor (List α) χ, A.CorrectInterleaved L :=
  ⟨reference L, reference_correctInterleaved⟩

/-- `CorrectFold` says that "process all chunks from `init`, then query" is a Bool
checker deciding (in the sense of `Silmaril.Accept.Decides`) the chunk lists whose
concatenation is in `L`. -/
theorem correctFold_iff_decides (A : Acceptor σ χ) :
    A.CorrectFold L ↔ Silmaril.Accept.Decides
      (fun cs : List χ => (A.query (cs.foldl A.process A.init)).1)
      {cs | cs.flatMap ChunkView.toList ∈ L} := by
  refine forall_congr' fun cs => ?_
  cases h : (A.query (cs.foldl A.process A.init)).1 <;>
    cases hm : member L (cs.flatMap ChunkView.toList) <;> simp_all [member]

end Acceptor

end Silmaril
