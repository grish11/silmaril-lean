module

public import Silmaril.Logic.TypeTheory.CIC.Scope.Defs
public import Silmaril.Logic.TypeTheory.CIC.Reduction.Defs

@[expose] public section

/-! # Explicit strict positivity of CIC constructors

Adapted from `common/theories/EnvironmentTyping.v` in MetaRocq at
`c8cd46054518193103c3bb33aa6e15c7f489e72c` (MIT; retained notice in
`licenses/MetaRocq-MIT.txt`). These are the source's direct mutual-block
positivity judgments, including zeta expansion and dependent function
arguments. They do not assert that arbitrary nested inductives are positive.
-/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Number of assumptions in a syntactic arity; local definitions do not count. -/
def Expr.arityArgumentCount : Expr → Option ℕ
  | .sort _ => some 0
  | .prod _ _ B => (arityArgumentCount B).map (· + 1)
  | .letIn _ _ _ B => arityArgumentCount B
  | _ => none

/-- Identify one locally bound member of the newest-first mutual arity context. -/
def MutualInductiveBody.AtIndex (block : MutualInductiveBody) (depth index : ℕ)
    (body : InductiveBody) : Prop :=
  depth ≤ index ∧ index < depth + block.bodies.length ∧
    block.bodies.reverse[index - depth]? = some body

/-- Strictly positive occurrence in a constructor argument type.

The `closed` rule excludes all mutual-block names, not just negative occurrences.
A recursive head must have its full arity and closed arguments. A product's
domain excludes mutual names; its codomain may remain strictly positive.
-/
inductive PositiveArgument (block : MutualInductiveBody) : ℕ → Expr → Prop where
  | closed {depth t} : t.isClosed depth = true → PositiveArgument block depth t
  | recursive {depth index body args} :
      block.AtIndex depth index body →
      args.length = body.type.arityArgumentCount.getD 0 →
      (∀ a ∈ args, a.isClosed depth = true) →
      PositiveArgument block depth (Expr.mkApps (.rel index) args)
  | letIn {depth na value A body} :
      PositiveArgument block depth (body.subst [value] 0) →
      PositiveArgument block depth (.letIn na value A body)
  | product {depth na A B} : A.isClosed depth = true →
      PositiveArgument block (depth + 1) B →
      PositiveArgument block depth (.prod na A B)

/-- Positivity of a full constructor type ending at its declared mutual member. -/
inductive PositiveConstructor (block : MutualInductiveBody) (member : ℕ) :
    ℕ → Expr → Prop where
  | conclusion {depth args} : member < block.bodies.length →
      (∀ a ∈ args, a.isClosed depth = true) →
      PositiveConstructor block member depth
        (Expr.mkApps (.rel (block.bodies.length - (member + 1) + depth)) args)
  | letIn {depth na value A body} :
      PositiveConstructor block member depth (body.subst [value] 0) →
      PositiveConstructor block member depth (.letIn na value A body)
  | product {depth na A B} : PositiveArgument block depth A →
      PositiveConstructor block member (depth + 1) B →
      PositiveConstructor block member depth (.prod na A B)

end Silmaril.Logic.TypeTheory.CIC
