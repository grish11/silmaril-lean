module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Boundary.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Boundary

/-! # Separations in the default and existing opt-in SSA relations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary

open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural
open scoped Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary

/-- The existing opt-in unit η proves the equation at the written endpoints. -/
theorem unit_joined : unitReturn.JoinedEqv unitForward :=
  unit_joined_proof

/-- Default Paper separates a valid equation at the exact packed unit input. -/
theorem unit_separation : unitReturn.Valid unitForward ∧
    ¬ Region.Paper.Eqv [(Ty.unit : Ty Empty)] unitReturn.region unitForward.region [Ty.unit] :=
  ⟨Endpoint.joined_sound unit_joined, unit_default_fails_proof⟩

/-- Even the existing joined extension separates sequencing of this pair.
The left component has a unary value let and both inputs are inhabited. -/
theorem pair_separation : paired.Valid sequenced ∧ ¬ paired.JoinedEqv sequenced :=
  ⟨pair_valid_proof, pair_joined_fails_proof⟩

open Region.Paper.UnaryReturn.Beta.Constructors.Example (source)

/-- The separating pair is derivable in the separate opt-in constructor
sequencing presentation. -/
theorem pair_constructor_step :
    Region.Paper.WithConstructorSequencing.Step [source] paired.region sequenced.region
      [Ty.product source source] :=
  pair_constructor_proof

/-- Reification fails to replay every native LetCase equation even at this
single packed binary-sum input and product output in the joined relation. -/
theorem pair_reification_fails :
    ¬ (∀ a b : Operand Empty (.snoc .nil source) (.product source source), ReificationReplay a b) :=
  pair_reification_fails_proof

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary
