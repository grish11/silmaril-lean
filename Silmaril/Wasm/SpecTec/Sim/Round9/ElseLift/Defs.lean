module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, REH: SpecTec's `otherwise` read backward along export erasure (definitions)

The backward SpecTec leaf `CoreStrip.EraseBwdAt` lifts a derivation at the erased image
`Swap.eraseV a` to one at `a`. At a rule `i` of `Step_read` with an `otherwise` premise, the
erased side knows (`Round6.Reading.otherwiseAtB`) that no earlier rule `j < i` fires at
`(eraseV a, c')` for any `c'`, and the lift needs the same at `(a, c)`. This is the opposite
polarity of round 9's forward transfer (`ElseBwd.PairReflectB`, a *backward* firing): here an
earlier rule that fired at `(a, c)` must fire *forward*, at `(eraseV a, c')`, to contradict the
erased side. Nothing in this direction is false: earlier rules go forward along erasure exactly
as whole derivations do.

* `PairFireFwdB env ε x i j`: wherever rule `i` fires on the image side at `(ε a, b₀)`
  (`Round8.NxElse.Fired`), a firing of rule `j` at `(a, c)` under `otherwise`'s reading (premises
  by `DDerivesB env noElse`, its own `otherwise` by `otherwiseAtB`) gives one at `(ε a, c')`.
* `ElseFwdB env`: `PairFireFwdB` along `Swap.eraseV` at every pair of `ElseBwd.elsePairs`. Pairs
  outside `elsePairs` have different heads, and a firing of each rule fixes the head of `a`.
* `fwdPairsIs m`: at every pair of `elsePairs` the earlier rule passes `ElseBwd.goodRuleE` (the
  check under which round 9 moves a rule forward). The kernel checks it on the fixed script
  (`Round9.ElseLift.fwdPairs_fixed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB RuleBodyB otherwiseAtB)

/-- **Rule `j` of `x` fires forward along `ε` at the left-hand sides where rule `i` fires on the
image side**: if rule `i` fires at `(ε a, b₀)` and rule `j` fires at `(a, c)` under SpecTec's
reading of `otherwise`, then rule `j` fires at `(ε a, c')` for some `c'`. -/
def PairFireFwdB (env : Env) (ε : Value → Value) (x : IL.Id) (i j : Nat) : Prop :=
  ∀ ps op t rules r, env.findRel? x = some (ps, op, t, rules) → rules[j]? = some r →
    ∀ a b₀ c, Round8.NxElse.Fired env x [] i (.tuple [ε a, b₀]) →
      RuleBodyB env (DDerivesB env Sim.noElse) (otherwiseAtB env x [] j (.tuple [a, c])) ps [] op
        r (.tuple [a, c]) →
      ∃ c', RuleBodyB env (DDerivesB env Sim.noElse) (otherwiseAtB env x [] j (.tuple [ε a, c']))
        ps [] op r (.tuple [ε a, c'])

/-- **The obligation of the backward `otherwise`, for RE**: `PairFireFwdB` along export erasure at
every pair of `ElseBwd.elsePairs`. Proved at round 4's primitives
(`Round9.ElseLift.elseFwdB_BI`). -/
def ElseFwdB (env : Env) : Prop :=
  ∀ p ∈ ElseBwd.elsePairs, PairFireFwdB env Swap.eraseV "Step_read" p.1 p.2

/-- At every pair of `elsePairs`, the earlier rule of every `Step_read` entry of `m` exists and
passes `ElseBwd.goodRuleE`. -/
def fwdPairsIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Step_read" || ElseBwd.elsePairs.all fun q => match p.2.2.2.2[q.2]? with
    | some rj => ElseBwd.goodRuleE rj
    | none => false

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift
