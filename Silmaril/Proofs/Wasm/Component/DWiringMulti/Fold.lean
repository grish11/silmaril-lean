module

public import Silmaril.Wasm.Component.DWiringMulti.Defs
public import Silmaril.Wasm.Component.DWiringChatter3.Thms
public import Silmaril.Wasm.Component.OutOfRange.Thms

/-!
# The observations of `ext` and of `denNodesD`, as a fold

`obs_ext`: the observations of `ext e D N` are `(DObs.of D).ext e N`, by
`div_ext_eq_routed` (with the routed divergences distributed over the three
sources) and `inf_ext_routed`. `obs_denNodesD` follows by induction on the
nodes. `obs_ext_maskH`: above `maskH e`, a trap-propagating node neither
inherits a divergence of `maskH` (it has none) nor chatters with it
(`div_ext_maskH`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringMulti

open Silmaril.Games Silmaril.Wasm.Component

variable {X : Sig.{0}}

theorem div_ext (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (DStrategy.ext e D N).div =
      EnvDiv e D.div N ∪ NodeDiv e D.toStrategy N ∪ NodeChatter e D.inf N := by
  rw [DStrategy.div_ext_eq_routed]
  ext p
  constructor
  · rintro (⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, hr⟩⟩ | hc)
    · exact .inl (.inl ⟨s, t, hz, hs, ht⟩)
    · exact .inl (.inr ⟨s, t, hz, hs, hr⟩)
    · exact .inr hc
  · rintro ((⟨s, t, hz, hs, ht⟩ | ⟨s, t, hz, hs, hr⟩) | hc)
    · exact .inl ⟨s, t, hz, .inl ⟨hs, ht⟩⟩
    · exact .inl ⟨s, t, hz, .inr ⟨hs, hr⟩⟩
    · exact .inr hc

theorem obs_ext (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    DObs.of (DStrategy.ext e D N) = (DObs.of D).ext e N := by
  have hinf : (DStrategy.ext e D N).inf = ExtInf e (DObs.of D) N :=
    DStrategy.inf_ext_routed e D N
  simp only [DObs.of, DObs.ext, div_ext, hinf]
  rfl

theorem obs_denNodesD {M : Type} [CoreModule M] (C : DCoreSem M) :
    ∀ (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU),
      DObs.of (denNodesD C e ns D) = nodesObs C e ns (DObs.of D)
  | _, [], _ => by rw [denNodesD_nil, nodesObs]
  | e, n :: ns, D => by
    rw [denNodesD_cons, nodesObs, obs_denNodesD C (e + n.width) ns, obs_ext]

theorem obs_ext_maskH (e : Nat) {N : DStrategy sigU sigU} (hN : TrapPropagating N) :
    DObs.of (DStrategy.ext e (DStrategy.ofHandler (maskH e)) N) = firstObs e N := by
  have hdiv := DStrategy.div_ext_maskH e hN
  have hinf : (DStrategy.ext e (DStrategy.ofHandler (maskH e)) N).inf =
      ExtInf e (DObs.of (DStrategy.ofHandler (maskH e))) N := DStrategy.inf_ext_routed e _ N
  simp only [DObs.of, firstObs, hdiv, hinf]
  rfl

end Silmaril.Proofs.Wasm.Component.DWiringMulti
