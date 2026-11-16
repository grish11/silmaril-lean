module

public import Silmaril.Semantics.StreamAcceptors.Defs
public import Silmaril.Semantics.Acceptors.Thms
public import Silmaril.Semantics.StreamMonitors.Thms

/-! # Proofs: acceptor answers on chunk streams -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.StreamAcceptors

open Cslib Silmaril.Streams Silmaril.Acceptor

universe u v w

variable {σ : Type u} {χ : Type v} {α : Type w}

theorem take_map {β : Type*} (f : χ → β) (cs : ωSequence χ) (n : ℕ) :
    (cs.map f).take n = (cs.take n).map f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ωSequence.take_succ', ωSequence.take_succ', ih, List.map_append]; rfl

theorem prefixAt_view [ChunkView χ α] (cs : ωSequence χ) (n : ℕ) :
    (view cs).prefixAt n = (cs.take n).flatMap ChunkView.toList := by
  rw [Chunks.prefixAt, view, take_map, List.flatMap_def]

variable [ChunkView χ α] {L : Language α} [DecidablePred (· ∈ L)]

theorem boundaryAnswer_eq {A : Acceptor σ χ} (h : A.CorrectFold L) (cs : ωSequence χ) (n : ℕ) :
    A.boundaryAnswer cs n = member L ((view cs).prefixAt n) := by
  rw [boundaryAnswer, h, prefixAt_view]

theorem run_boundaryTrace {A : Acceptor σ χ} (hp : A.Pure) (cs : ωSequence χ) (n : ℕ) :
    A.run A.init (boundaryTrace cs n) =
      ((List.range n).map fun k => A.boundaryAnswer cs (k + 1),
        (cs.take n).foldl A.process A.init) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boundaryTrace, ωSequence.take_succ', List.flatMap_append, ← boundaryTrace,
      run_append, ih, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.foldl_cons,
      List.foldl_nil, List.map_cons, List.map_nil]
    simp only [run, boundaryAnswer, ωSequence.take_succ', List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [hp]

end Silmaril.Proofs.Semantics.StreamAcceptors
