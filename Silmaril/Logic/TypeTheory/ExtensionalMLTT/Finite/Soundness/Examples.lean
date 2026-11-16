module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Examples

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open Silmaril.Logic.SetTheory

universe u

/-- The actual one-level target beta proof is valid in every actual one-level model. -/
theorem bounded_identity_beta_sound (T : FiniteTower.{u} 1) :
    (⟨.nil, .nats, .app (.abs .nats (.bv 0)) .zero, .zero⟩ : EJdg).ValidIn T.U :=
  bounded_identity_beta.sound_empty T

/-- The actual two-level target universe rule uses only the supplied finite successor membership. -/
theorem bounded_universe_sound (T : FiniteTower.{u} 2) :
    (⟨.nil, .univ 1, .univ 0, .univ 0⟩ : EJdg).ValidIn T.U :=
  bounded_univ_zero.sound_empty T

/-- Actual Nat successor computation is valid without an infinite universe hierarchy. -/
theorem bounded_natrec_successor_sound (T : FiniteTower.{u} 1) :
    (⟨.nil, .nats, .natrec .nats (.abs .nats (.succ (.bv 0))) .zero (.succ .zero),
      .app (.abs .nats (.succ (.bv 0)))
        (.natrec .nats (.abs .nats (.succ (.bv 0))) .zero .zero)⟩ : EJdg).ValidIn T.U :=
  bounded_nat_successor.sound_empty T

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
