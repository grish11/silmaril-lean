module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadN.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs

/-!
# Round 9, RE: the seven rules of `BadFwdN`, one at a time (definitions)

`BadN.BadFwdN env` asks that every rule of `Step`/`Step_read` failing the three syntactic checks
(`NxStep.goodRule`, `ElseBwd.goodRuleE`, `BadN.goodRuleN`) go to the erased side: where it fires
under SpecTec's `otherwise`, its erased instance derives the erased value. In the fixed script
seven rules fail the checks (`BadN.stepBadN_fixed`). Each of them fails only because it calls
one of the four definitions the evaluator-level erasure leaves out (`EraseAll.excluded`):

* `call_ref-hostfunc-res`, `call_ref-hostfunc-div`: `$hostcall` in an `if pat <- …` premise;
* `table.grow-succeed`, `memory.grow-succeed`: `$with_tableinst`/`$with_meminst` in the
  conclusion;
* `block`, `loop`, `try_table`: `$blocktype_` in their only premise.

This header states the obligation one rule name at a time.

* `badNames`: the seven names.
* `RuleFwdNm env nm`: every rule named `nm` of `Step`/`Step_read`, wherever it fires under
  SpecTec's `otherwise`, goes to the erased side. It is `BadFwdN` at one rule name, without the
  hypothesis that the rule fails the checks.
* `LeavesREHBwd`: `CoreStrip.LeavesREH` without its forward leaf `EraseFwdAt`, which holds at
  every configuration for an export-blind host (`Round9.BadRules.eraseFwdAt_blind`). What is left
  of `Round7.Task.wholeStepValidREH` (`Round9.BadRules.wholeStepValidREH_of_bwd`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-- The seven rules of `BadN.BadFwdN` (`BadN.stepBadN_fixed`), by name. -/
def badNames : List String :=
  ["call_ref-hostfunc-res", "call_ref-hostfunc-div", "table.grow-succeed", "memory.grow-succeed",
   "block", "loop", "try_table"]

/-- The name of a rule. -/
def ruleName : Rule → IL.Id
  | .ruleD nm _ _ _ _ => nm

/-- **The rules named `nm` go to the erased side**: wherever a rule named `nm` of `Step` or
`Step_read` fires under SpecTec's `otherwise`, its erased instance derives the erased value from
the erased arguments. -/
def RuleFwdNm (env : Env) (nm : IL.Id) : Prop :=
  ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {i : Nat} {v : Value} {ps : List Param}
    {t : Typ} {rules : List Rule} {qs : List Param} {e e' : Exp} {prems : List Prem}
    {ρ₀ : VarEnv} {σ : List (IL.Id × Value)},
    Round8.NxStep.stepRel x = true →
    env.findRel? x = some (ps, op, t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    e' ∈ Round6.Reading.conclAlts e → bindParams VarEnv.empty ps args = some ρ₀ →
    QuantsOk env (ρ₀.bindVals σ) qs → EvalExp env (ρ₀.bindVals σ) e' v →
    (∀ pr ∈ prems, Round6.Reading.DPremB env (Round6.Reading.otherwiseB env)
      (Round6.Reading.otherwiseB env x args i v) (ρ₀.bindVals σ) pr) →
    Round6.Reading.DDerivesB env (Round6.Reading.otherwiseB env) x op (args.map Swap.eraseA)
      (Swap.eraseV v)

open Silmaril.Wasm.Execution.Core in
open Silmaril.Wasm.Validation in
open Silmaril.Wasm.Numerics (Profile RelaxedChoice) in
/-- **The leaves of REH left once the forward leaf is proved**: the backward SpecTec leaf
`EraseBwdAt` and the export leaf `ExactAt`, at every configuration of REH's domain, for every
injective encoding and finite, `HostOk`, export-blind host. -/
def LeavesREHBwd : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → Round7.HostExportBlind host →
      ∀ (nd : Bool) (r : RelaxedChoice) (c : Config H) (ts : List CValType),
        ConfigOk c ts → BoundedSelE c →
        CoreStrip.EraseBwdAt hn (Profile.spec nd r) host c ∧
          CoreStrip.ExactAt hn (Profile.spec nd r) host c

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
