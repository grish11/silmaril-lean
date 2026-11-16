module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Structure.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Examples

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Identity beta remains an actual one-level proof under a natural-number declaration. -/
theorem bounded_weakened_identity_beta :
    ECtx.JEqB 1 ∅ (.cons .nil "n" .nats) .nats
      (.app (.abs .nats (.bv 0)) .zero) .zero :=
  bounded_identity_beta.weaken_last (by decide)
    (by simp [ECtx.dv]) bounded_nats

/-- Nat successor computation keeps its one-level cofinite families under a new declaration. -/
theorem bounded_weakened_nat_successor :
    ECtx.JEqB 1 ∅ (.cons .nil "n" .nats) .nats
      (.natrec .nats (.abs .nats (.succ (.bv 0))) .zero (.succ .zero))
      (.app (.abs .nats (.succ (.bv 0)))
        (.natrec .nats (.abs .nats (.succ (.bv 0))) .zero .zero)) :=
  bounded_nat_successor.weaken (bounded_nats_context "n")
    (ECtx.Embeds.fresh (by simp [ECtx.dv]) .nats)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
