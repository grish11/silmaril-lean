module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseLift.Lift

/-!
# Round 9, REH: SpecTec's `otherwise` read backward along export erasure (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift`; definitions in `Round9/ElseLift/Defs.lean`,
proofs in `Silmaril/Proofs/Wasm/SpecTec/Sim/Round9/ElseLift/`.

* **`fwdPairs_fixed`** (kernel): at every pair `(i, j)` of `ElseBwd.elsePairs` (94), rule `j` of
  `Step_read` passes `ElseBwd.goodRuleE`.
* **`otherwiseAtB_lift`** (any environment): `otherwiseAtB env x [] i (eraseV a, b₀)` at a fired
  rule `i` gives `otherwiseAtB env x [] i (a, b)` for every `b`, given `PairFireFwdB` at the
  earlier rules whose heads are not known to differ.
* **`fireFwd_goodE`**: a `Step_read` rule passing `goodRuleE` fires forward along erasure, under
  `otherwise`'s reading, given `ElseBwd.ElseBwdB` for its own `otherwise`.
* **`elseFwdB_BI : ElseFwdB (NxPrims.envBI P hn host)`**, and
* **`otherwiseAtB_lift_BI`**: at round 4's primitives, every `otherwise` rule of `Step_read`
  that fired on the erased side reads its `otherwise` at the original left-hand side, with no
  hypothesis:

```lean
theorem otherwiseAtB_lift_BI (P : Profile) (hn : H → String) (host : HostSemantics H)
    (hrel : (NxPrims.envBI P hn host).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hel : hasElse ri = true)
    (hF : Round8.NxElse.Fired (NxPrims.envBI P hn host) "Step_read" [] i (.tuple [eraseV a, b₀]))
    (h : otherwiseAtB (NxPrims.envBI P hn host) "Step_read" [] i (.tuple [eraseV a, b₀]))
    (b : Value) : otherwiseAtB (NxPrims.envBI P hn host) "Step_read" [] i (.tuple [a, b])
```

This is the `otherwise` part of the backward lift that `CoreStrip.EraseBwdAt` needs; it is not the
lift itself (the rule instances, their typing and their other premises are not treated here).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.fwdPairs_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdPairs_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.otherwiseAtB_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms otherwiseAtB_lift

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.fireFwd_goodE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fireFwd_goodE

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.elseFwdB_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elseFwdB_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.otherwiseAtB_lift_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms otherwiseAtB_lift_BI

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift
