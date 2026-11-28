module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (pending finishes_iff)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

private theorem packet_same {pre₁ pre₂ : PreMark p} {old : Bank (regs := regs) model}
    {roots₁ roots₂ : List (RootMark p)}
    (left : Slice p input pre₁ old (pending semantics (thetaBody p)) roots₁)
    (right : Slice p input pre₂ old (pending semantics (thetaBody p)) roots₂) :
    left.packet = right.packet :=
  (left.packet_eq p input).trans (right.packet_eq p input).symm

private theorem observation_same {pre₁ pre₂ : PreMark p} {old b₁ b₂ : Bank (regs := regs) model}
    {roots₁ roots₂ : List (RootMark p)}
    (left : Slice p input pre₁ old (pending semantics (thetaBody p)) roots₁)
    (right : Slice p input pre₂ old (pending semantics (thetaBody p)) roots₂)
    (read₁ : left.firstOuter = some b₁) (read₂ : right.firstOuter = some b₂) :
    left.observation p input b₁ = right.observation p input b₂ := by
  have bank := Option.some.inj (read₁.symm.trans
    ((left.firstOuter_eq p input).trans ((right.firstOuter_eq p input).symm.trans read₂)))
  simp only [Slice.observation, bank, packet_same p input left right]

private theorem recovered_same {pre₁ pre₂ : PreMark p} {old₁ old₂ : Bank (regs := regs) model}
    {roots₁ roots₂ : List (RootMark p)}
    (left : Recovered p input pre₁ old₁ roots₁) (right : Recovered p input pre₂ old₂ roots₂)
    (olds : old₁ = old₂) : left.observations p input = right.observations p input := by
  induction left generalizing old₂ roots₂ with
  | stop slice₁ bank₁ read₁ halt₁ _ _ _ =>
    subst old₂
    cases right with
    | stop slice₂ bank₂ read₂ _ _ _ _ =>
      exact congrArg (fun obs => [obs]) (observation_same p input slice₁ slice₂ read₁ read₂)
    | again slice₂ _ _ recur₂ _ =>
      cases halt₁.symm.trans ((congrArg feedback (packet_same p input slice₁ slice₂)).trans recur₂)
  | again slice₁ bank₁ read₁ recur₁ _ ih =>
    subst old₂
    cases right with
    | stop slice₂ _ _ halt₂ _ _ _ =>
      cases recur₁.symm.trans ((congrArg feedback (packet_same p input slice₁ slice₂)).trans halt₂)
    | again slice₂ bank₂ read₂ _ rest₂ =>
      exact congrArg₂ List.cons (observation_same p input slice₁ slice₂ read₁ read₂)
        (ih rest₂ (congrArg nextBankOf (packet_same p input slice₁ slice₂)))

theorem observations_same {roots₁ roots₂ : List (RootMark p)}
    (left : Complete p input roots₁) (right : Complete p input roots₂) :
    left.observations p input = right.observations p input :=
  recovered_same p input left.recovery right.recovery rfl

theorem result_same {roots₁ roots₂ : List (RootMark p)}
    (left : Complete p input roots₁) (right : Complete p input roots₂) :
    left.result p input = right.result p input := by
  let graph := lower p
  have returns₁ := (finishes_iff semantics graph input _).mp (left.finishes p input)
  have returns₂ := (finishes_iff semantics graph input _).mp (right.finishes p input)
  obtain ⟨a, ran₁⟩ := graph.returns_eventually semantics input _ returns₁
  obtain ⟨b, ran₂⟩ := graph.returns_eventually semantics input _ returns₂
  exact Option.some.inj ((ran₁ (max a b) (Nat.le_max_left _ _)).symm.trans (ran₂ _ (Nat.le_max_right _ _)))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs
