module

public import Silmaril.Compiler.Explorer.Defs

/-!
# The deterministic cut-point specialisation

A thin specialisation of `Silmaril.Compiler.Explorer` to a **deterministic** target machine
(`τ → Option τ`) whose return is read relative to its entry state, and to the cut-point
simulation of `Silmaril.Compiler.CompilesTo.Sim` (`Corr`, `Corr.Segment`). The C/x86-64 instance
(`Silmaril.Project.Shapes.CompilesTo.Explorer`) uses it.

* `DetProblem` and its validity `DetProblem.Valid`: from every entry, a safe source makes the
  machine reach its **first** return (`DetProblem.Step` stops there) with a result a source run
  produces. `DetProblem.toProblem` reads it as a generic `Problem` whose target states carry the
  entry state as a ghost and stop at the first return; `DetProblem.refines_of_valid` (in `Thms`)
  proves the generic, backward `Problem.Refines` from it, using determinism.
* `DetMapping`, its correspondence `DetMapping.corr` and per-edge validity
  `DetMapping.EdgeValid` (`Corr.Segment`); `Det.discipline` is the segment discipline: valid
  edges of a mapping that starts at the entry and relates no state at a return compose into
  `Problem.Refines` of `toProblem`.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

open Silmaril.Compiler.CompilesTo (Source Corr)

/-- **A deterministic compilation problem**: a source model, a deterministic machine, the entry
convention `entry x0 s`, the return `tgtFinal x0 x` and the result relation `result x0 r x`,
each relative to the machine's entry state `x0`. -/
structure DetProblem (σ τ R : Type) where
  src : Source σ R
  tgt : τ → Option τ
  entry : τ → σ → Prop
  tgtFinal : τ → τ → Prop
  result : τ → R → τ → Prop

namespace DetProblem

variable {σ τ R : Type} (D : DetProblem σ τ R)

/-- One machine step before the first return of the call entered in `x0`. -/
def Step (x0 a b : τ) : Prop := D.tgt a = some b ∧ ¬ D.tgtFinal x0 a

/-- **Valid, to the first return**: from every entry with a safe source, the machine runs to its
first return, whose state corresponds to the result of some source run. -/
def Valid : Prop :=
  ∀ x0 s, D.entry x0 s → D.src.Safe s →
    ∃ t r y, Relation.ReflTransGen D.src.step s t ∧ D.src.final t r ∧
      Relation.ReflTransGen (D.Step x0) x0 y ∧ D.tgtFinal x0 y ∧ D.result x0 r y

/-- **The generic problem of a deterministic one.** Target states are pairs (entry, current);
the machine stops at its first return; it goes wrong when it faults before a return; its final
states are its returns, with the pair as result. -/
def toProblem : Problem σ (τ × τ) R (τ × τ) where
  src := D.src
  tgt :=
    { step := fun p q => q.1 = p.1 ∧ D.Step p.1 p.2 q.2
      wrong := fun p => D.tgt p.2 = none ∧ ¬ D.tgtFinal p.1 p.2
      final := fun p v => D.tgtFinal p.1 p.2 ∧ v = p }
  entry s p := p.2 = p.1 ∧ D.entry p.1 s
  result r p := D.result p.1 r p.2

end DetProblem

/-- **A cut-point mapping** of a deterministic problem: points, the states at them and their
relation relative to the entry state (`rel k x0 s x`). -/
structure DetMapping {σ τ R : Type} (D : DetProblem σ τ R) where
  srcAt : Nat → σ → Prop
  tgtAt : Nat → τ → Prop
  rel : Nat → τ → σ → τ → Prop

namespace DetMapping

variable {σ τ R : Type} {D : DetProblem σ τ R} (M : DetMapping D)

/-- The cut-point correspondence (`Silmaril.Compiler.CompilesTo.Corr`). -/
def corr : Corr σ τ R where
  src := D.src
  tgt := D.tgt
  srcAt := M.srcAt
  tgtAt := M.tgtAt
  rel := M.rel
  tgtFinal := D.tgtFinal
  result := D.result

/-- The generic mapping: target states are (entry, current) pairs. -/
def toMapping : Mapping D.toProblem where
  srcAt := M.srcAt
  tgtAt k p := M.tgtAt k p.2
  rel k s p := M.rel k p.1 s p.2

/-- **The mapping starts at the entry.** -/
def Starts : Prop := ∀ x0 s, D.entry x0 s → M.srcAt 0 s ∧ M.tgtAt 0 x0 ∧ M.rel 0 x0 s x0

/-- **One edge is valid**: the segment from point `k` is simulated (`Corr.Segment`). -/
def EdgeValid (k : Nat) : Prop := M.corr.Segment k

/-- **Every edge is valid**, at every point number. -/
def Valid : Prop := ∀ k, M.EdgeValid k

/-- **No state related at a point is a return** (so composed segments reach the first return). -/
def NoReturnAtPoints : Prop := ∀ k x0 s x, M.rel k x0 s x → ¬ D.tgtFinal x0 x

end DetMapping

end Silmaril.Compiler.Explorer

end
