module

public import Silmaril.Semantics.Acceptors.Defs

/-!
# Incremental acceptors: proofs of the correctness hierarchy

Proofs for `Silmaril.Semantics.Acceptors.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Proofs.Semantics.Acceptors

open Silmaril Silmaril.Acceptor

universe u v w

variable {σ : Type u} {χ : Type v} {α : Type w}

theorem run_append (A : Acceptor σ χ) (s : σ) (t₁ t₂ : List (Event χ)) :
    A.run s (t₁ ++ t₂) =
      ((A.run s t₁).1 ++ (A.run (A.run s t₁).2 t₂).1, (A.run (A.run s t₁).2 t₂).2) := by
  induction t₁ generalizing s with
  | nil => rfl
  | cons e t ih => cases e <;> simp [Acceptor.run, ih]

theorem run_map_process (A : Acceptor σ χ) (s : σ) (cs : List χ) (tr : List (Event χ)) :
    A.run s (cs.map .process ++ tr) = A.run (cs.foldl A.process s) tr := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem specFrom_append_query [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)]
    (p : List χ) (tr : List (Event χ)) :
    specFrom L (p.flatMap ChunkView.toList) (tr ++ [.query]) =
      specFrom L (p.flatMap ChunkView.toList) tr ++
        [member L ((pendingFrom p tr).flatMap ChunkView.toList)] := by
  induction tr generalizing p with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | process c => simpa [specFrom, pendingFrom] using ih (p ++ [c])
    | query => simp [specFrom, pendingFrom, ih]
    | reset => simpa [specFrom, pendingFrom] using ih []

theorem specFrom_map_process [ChunkView χ α] (L : Language α) [DecidablePred (· ∈ L)]
    (w : List α) (cs : List χ) (tr : List (Event χ)) :
    specFrom L w (cs.map .process ++ tr) = specFrom L (w ++ cs.flatMap ChunkView.toList) tr := by
  induction cs generalizing w with
  | nil => simp
  | cons c cs ih => simpa [specFrom] using ih (w ++ ChunkView.toList c)

/-- Interleaved correctness needs no assumption to give fold correctness. -/
theorem correctFold_of_correctInterleaved [ChunkView χ α] {A : Acceptor σ χ}
    {L : Language α} [DecidablePred (· ∈ L)] (h : A.CorrectInterleaved L) : A.CorrectFold L := by
  intro cs
  have := h (cs.map .process ++ [.query])
  rw [run_map_process, specObs, specFrom_map_process] at this
  simpa [Acceptor.run, specFrom] using this

/-- The invariant: from the fold of the pending chunks, a pure acceptor with a sound
reset and correct single queries answers as specified. -/
theorem run_foldl_of_correctFold [ChunkView χ α] {A : Acceptor σ χ}
    {L : Language α} [DecidablePred (· ∈ L)] (hp : A.Pure) (hr : A.ResetSound)
    (h : A.CorrectFold L) (tr : List (Event χ)) (cs : List χ) :
    (A.run (cs.foldl A.process A.init) tr).1 = specFrom L (cs.flatMap ChunkView.toList) tr := by
  induction tr generalizing cs with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | process c => simpa [Acceptor.run, specFrom] using ih (cs ++ [c])
    | query => simp only [Acceptor.run, specFrom, hp _, h cs, ih cs]
    | reset => simpa [Acceptor.run, specFrom, hr _ t] using ih []

theorem correctInterleaved_of_correctFold [ChunkView χ α] {A : Acceptor σ χ}
    {L : Language α} [DecidablePred (· ∈ L)] (hp : A.Pure) (hr : A.ResetSound)
    (h : A.CorrectFold L) : A.CorrectInterleaved L :=
  fun tr => run_foldl_of_correctFold hp hr h tr []

/-- The immediate-query trace of a nonempty list of chunks. -/
private def immTrace (cs : List χ) : List (Event χ) :=
  cs.flatMap fun c => [.process c, .query]

private theorem immediate_immTrace (b : Bool) (cs : List χ) : Immediate b (immTrace cs) := by
  induction cs generalizing b with
  | nil => exact .nil b
  | cons c cs ih => exact .step b c (ih false)

private theorem run_immTrace_snd (A : Acceptor σ χ) (hp : A.Pure) (s : σ) (cs : List χ) :
    (A.run s (immTrace cs)).2 = cs.foldl A.process s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    show (A.run (A.query (A.process s c)).2 (immTrace cs)).2 = _
    rw [hp, ih]; rfl

private theorem specFrom_immTrace_append [ChunkView χ α] (L : Language α)
    [DecidablePred (· ∈ L)] (w : List α) (cs : List χ) (tr : List (Event χ)) :
    specFrom L w (immTrace cs ++ tr) =
      specFrom L w (immTrace cs) ++ specFrom L (w ++ cs.flatMap ChunkView.toList) tr := by
  induction cs generalizing w with
  | nil => simp [immTrace, specFrom]
  | cons c cs ih => simp [immTrace, specFrom] at *; simp [ih]

theorem correctFold_of_correctImmediate [ChunkView χ α] {A : Acceptor σ χ}
    {L : Language α} [DecidablePred (· ∈ L)] (hp : A.Pure) (h : A.CorrectImmediate L) :
    A.CorrectFold L := by
  intro cs
  rcases List.eq_nil_or_concat cs with rfl | ⟨cs, c, rfl⟩
  · simpa [Acceptor.run, specObs, specFrom] using h [.query] (.query (.nil false))
  · have e := h (immTrace (cs ++ [c])) (immediate_immTrace true _)
    have ht : immTrace (cs ++ [c]) = immTrace cs ++ [.process c, .query] := by simp [immTrace]
    rw [ht, run_append, specObs, specFrom_immTrace_append, run_immTrace_snd A hp] at e
    have := (List.append_inj' e (by simp [Acceptor.run, specFrom])).2
    simpa [Acceptor.run, specFrom] using this

end Silmaril.Proofs.Semantics.Acceptors
