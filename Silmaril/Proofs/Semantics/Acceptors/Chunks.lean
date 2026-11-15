module

public import Silmaril.Semantics.Acceptors.Defs
import Silmaril.Proofs.Semantics.Acceptors.Basic

/-!
# Incremental acceptors: chunking, symbols, reference and counterexamples

Proofs for `Silmaril.Semantics.Acceptors.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Proofs.Semantics.Acceptors

open Silmaril Silmaril.Acceptor

universe u v w

variable {σ : Type u} {χ : Type v} {α : Type w}

@[simp] private theorem toList_list (l : List α) : ChunkView.toList l = l := rfl

/-! ## Chunking independence -/

private theorem specFrom_symbols (L : Language α) [DecidablePred (· ∈ L)] (w l : List α)
    (tr : List (Event (List α))) :
    specFrom L w (l.map (fun a => Event.process [a]) ++ tr) = specFrom L (w ++ l) tr := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih => simpa [specFrom] using ih (w ++ [a])

theorem specFrom_toSymbolTrace [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)]
    (w : List α) (tr : List (Event χ)) :
    specFrom L w (toSymbolTrace tr) = specFrom L w tr := by
  induction tr generalizing w with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | process c => simp [toSymbolTrace, specFrom, specFrom_symbols, ← ih] at *
    | query => simp [toSymbolTrace, specFrom, ← ih] at *
    | reset => simp [toSymbolTrace, specFrom, ← ih] at *

theorem specObs_eq_of_toSymbolTrace_eq {χ₁ : Type v} {χ₂ : Type u} [ChunkView χ₁ α]
    [ChunkView χ₂ α] (L : Language α) [DecidablePred (· ∈ L)] {tr₁ : List (Event χ₁)}
    {tr₂ : List (Event χ₂)} (h : toSymbolTrace tr₁ = toSymbolTrace tr₂) :
    specObs L tr₁ = specObs L tr₂ := by
  rw [specObs, specObs, ← specFrom_toSymbolTrace, h, specFrom_toSymbolTrace]

theorem toSymbolTrace_process_nil [ChunkView χ α] (pre post : List (Event χ)) (c : χ)
    (hc : ChunkView.toList c = []) :
    toSymbolTrace (pre ++ .process c :: post) = toSymbolTrace (pre ++ post) := by
  simp [toSymbolTrace, hc]

/-! ## Symbol-at-a-time acceptors -/

theorem correctFold_ofSymbols [ChunkView χ α] {B : Acceptor σ α} {L : Language α}
    [DecidablePred (· ∈ L)] (h : B.SymbolCorrect L) : (B.ofSymbols (χ := χ)).CorrectFold L := by
  intro cs
  show (B.query (cs.foldl (fun s c => (ChunkView.toList c).foldl B.process s) B.init)).1 = _
  rw [← List.foldl_flatMap]
  exact h _

theorem symbolCorrect_toSymbols [ChunkView χ α] {A : Acceptor σ χ} {L : Language α}
    [DecidablePred (· ∈ L)] (single : α → χ) (hs : ∀ a, ChunkView.toList (single a) = [a])
    (h : A.CorrectFold L) : (A.toSymbols single).SymbolCorrect L := by
  intro w
  have e := h (w.map single)
  rw [List.foldl_map] at e
  simp only [List.flatMap_map, hs, List.flatMap_singleton'] at e
  exact e

theorem toSymbols_ofSymbols [ChunkView χ α] (B : Acceptor σ α) (single : α → χ)
    (hs : ∀ a, ChunkView.toList (single a) = [a]) :
    (B.ofSymbols (χ := χ)).toSymbols single = B := by
  cases B
  simp [toSymbols, ofSymbols, hs]

/-! ## The reference acceptor -/

private theorem foldl_append_toList [ChunkView χ α] (cs : List χ) (w : List α) :
    cs.foldl (fun w c => w ++ ChunkView.toList c) w = w ++ cs.flatMap ChunkView.toList := by
  induction cs generalizing w with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem reference_correctFold [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)] :
    (reference (χ := χ) L).CorrectFold L := by
  intro cs
  show member L (cs.foldl (fun w c => w ++ ChunkView.toList c) []) = _
  rw [foldl_append_toList, List.nil_append]

/-! ## Counterexamples -/

theorem finalizing_correctFold [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)] :
    (finalizing (χ := χ) L).CorrectFold L := by
  intro cs
  show member L (cs.foldl (fun w c => w ++ ChunkView.toList c) []) = _
  rw [foldl_append_toList, List.nil_append]

theorem finalizing_not_correctImmediate [ChunkView χ α] (L : Language α)
    [DecidablePred (· ∈ L)] (c₁ c₂ : χ) (h₁ : ChunkView.toList c₁ ++ ChunkView.toList c₂ ∈ L)
    (h₂ : ChunkView.toList c₂ ∉ L) : ¬ (finalizing (χ := χ) L).CorrectImmediate L := by
  intro h
  have := h [.process c₁, .query, .process c₂, .query] (.step _ _ (.step _ _ (.nil _)))
  simp [Acceptor.run, specObs, specFrom, finalizing, member, h₁, h₂] at this

section answerOnce

variable [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)]

@[simp] private theorem answerOnce_init : (answerOnce (χ := χ) L).init = ([], false) := rfl
@[simp] private theorem answerOnce_process (s : List α × Bool) (c : χ) :
    (answerOnce L).process s c = (s.1 ++ ChunkView.toList c, false) := rfl
@[simp] private theorem answerOnce_query (s : List α × Bool) :
    (answerOnce (χ := χ) L).query s = (!s.2 && member L s.1, (s.1, true)) := rfl
@[simp] private theorem answerOnce_reset (s : List α × Bool) :
    (answerOnce (χ := χ) L).reset s = ([], false) := rfl

end answerOnce

private theorem answerOnce_foldl [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)]
    (cs : List χ) (w : List α) :
    cs.foldl (answerOnce (χ := χ) L).process (w, false) =
      (w ++ cs.flatMap ChunkView.toList, false) := by
  induction cs generalizing w with
  | nil => simp
  | cons c cs ih => simpa using ih (w ++ ChunkView.toList c)

theorem answerOnce_correctFold [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)] :
    (answerOnce (χ := χ) L).CorrectFold L := by
  intro cs
  simp [answerOnce_foldl]

private theorem answerOnce_run_immediate [ChunkView χ α] (L : Language α)
    [DecidablePred (· ∈ L)] {b : Bool} {tr : List (Event χ)} (hi : Immediate b tr) :
    ∀ (w : List α) (a : Bool), (b = true → a = false) →
      ((answerOnce L).run (w, a) tr).1 = specFrom L w tr := by
  induction hi with
  | nil => intros; rfl
  | step b c _ ih =>
    intro w a _
    simp [Acceptor.run, specFrom, ih _ true (by simp)]
  | query _ ih =>
    intro w a ha
    simp [Acceptor.run, specFrom, ha rfl, ih _ true (by simp)]
  | reset b _ ih =>
    intro w a _
    simpa [Acceptor.run, specFrom] using ih [] false (fun _ => rfl)

theorem answerOnce_correctImmediate [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)] :
    (answerOnce (χ := χ) L).CorrectImmediate L :=
  fun _ hi => answerOnce_run_immediate L hi [] false (fun _ => rfl)

theorem answerOnce_not_correctInterleaved [ChunkView χ α] (L : Language α)
    [DecidablePred (· ∈ L)] (c : χ) (hc : ChunkView.toList c ∈ L) :
    ¬ (answerOnce (χ := χ) L).CorrectInterleaved L := by
  intro h
  have := h [.process c, .query, .query]
  simp [Acceptor.run, specObs, specFrom, member, hc] at this

end Silmaril.Proofs.Semantics.Acceptors
