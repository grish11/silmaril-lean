module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.Defs

/-!
# Round 9, REH: lifting SpecTec derivations backward along export erasure (definitions)

`CoreStrip.EraseBwdAt` (the backward SpecTec leaf of REH) asks for a derivation of `Step` at
`configV hn c` whose erasure is a given derivation's conclusion at the erased image. Route 2 of
rounds 7 to 9 moves derivations only *forward* along `Swap.eraseV`, outside `otherwise`
(`Round8.NxDer.derFwdN`, `Round9.ElseRef.sStepB_fwd_BI_E`). Forward is easy because erasure is a
function: every quantifier value is erased. Backward is not: erasure forgets export lists, and
two module instances of `c` may differ only in them (`Round7.REGap.collideCfg`), so the
export-carrying quantifiers of a rule instance must be **rebound positionally**, to the values at
their positions in the original input, not chosen by their erased value.

This header states the interface of that lift, with the provenance of the original input explicit:

* `liftRel x`: the relations lifted by induction, `Step`, `Step_read` and `Step_pure`. The others
  (`Ref_ok`, `Expand`, …) appear only as premises and are handled at the rule.
* `LiftV env O Prov x op args v₀`: **the lift at one erased conclusion**. For every original input
  `a` with `v₀ = (eraseV a, b₀)` whose provenance `Prov x a` holds, rule-based derivations of `x`
  reach `(a, b)` for some `b` with `eraseV b = b₀`. The successor is exact: no Core round trip,
  and the `CALL_REF` annotations and nondeterministic choices of `b` are those of the derivation.
* `DPremL env O Prov els ρ pr`: `Round6.Reading.DPremB` whose relation premises of `liftRel`
  relations also carry `LiftV` at their conclusion: the induction hypothesis, at the premises.
* `RuleLift env O Prov x i`: **the obligation at rule `i` of `x`**: a rule instance on the erased
  side (quantifiers typed, conclusion evaluated, premises with their lifts) gives `LiftV` at its
  conclusion. A proof rebinds the export-carrying quantifiers to positions of `a`, shows the
  premise inputs keep `Prov`, and reads `otherwise` by `Round9.ElseLift.otherwiseAtB_lift`.

`Round9.DerLift.dderivesB_lift` proves `LiftV` from `RuleLift` at every rule, by induction on the
erased derivation; `eraseBwdAt_of_lift` gives `CoreStrip.EraseBwdAt` from it at an export-blind
host, given `Prov "Step" (configV hn c)`. `Round9.DerLift.ruleLift_simple` proves `RuleLift` at
the `Step_read` rules of the family `liftSimple`, for any `Prov` that types the state.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB DPremB conclAlts)

/-- The relations lifted by induction: `Step`, `Step_read`, `Step_pure`. -/
def liftRel (x : IL.Id) : Bool := x == "Step" || x == "Step_read" || x == "Step_pure"

/-- **The backward lift at one erased conclusion `v₀`** of `x`: every original input `a` with
provenance `Prov x a` and `v₀ = (eraseV a, b₀)` has a derivation of `(a, b)` with
`eraseV b = b₀`. -/
def LiftV (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) (x : IL.Id) (op : MixopS)
    (args : List ArgV) (v₀ : Value) : Prop :=
  ∀ a b₀, v₀ = .tuple [Swap.eraseV a, b₀] → Prov x a →
    ∃ b, DDerivesB env O x op args (.tuple [a, b]) ∧ Swap.eraseV b = b₀

/-- **`DPremB` with the lift at its `liftRel` relation premises.** -/
inductive DPremL (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) :
    Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPremL env O Prov els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPremL env O Prov els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPremL env O Prov els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerivesB env O x op avs w →
      (liftRel x = true → LiftV env O Prov x op avs w) →
      DPremL env O Prov els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPremL env O Prov els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPremL env O Prov els (ρ.bindVals row) pr →
      DPremL env O Prov els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPremL env O Prov els (ρ.bindVals r) pr) →
      DPremL env O Prov els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPremL env O Prov els (ρ.bindVals r) pr) →
      DPremL env O Prov els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))

/-- **The obligation at rule `i` of `x`**: an instance of the rule on the erased side, with the
lift at its `liftRel` premises, has the lift at its conclusion. -/
def RuleLift (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) (x : IL.Id) (i : Nat) :
    Prop :=
  ∀ {op : MixopS} {args : List ArgV} {v₀ : Value} {ps : List Param} {t : Typ}
    {rules : List Rule} {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem}
    {ρ₀ : VarEnv} {σ : List (IL.Id × Value)},
    env.findRel? x = some (ps, op, t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    e' ∈ conclAlts e → bindParams VarEnv.empty ps args = some ρ₀ →
    QuantsOk env (ρ₀.bindVals σ) qs → EvalExp env (ρ₀.bindVals σ) e' v₀ →
    (∀ pr ∈ prems, DPremL env O Prov (O x args i v₀) (ρ₀.bindVals σ) pr) →
    LiftV env O Prov x op args v₀

/-! ## The first rule family: rebinding the state -/

/-- **A `Step_read` rule lifted by rebinding its state.** It passes `ElseBwd.simpleRuleE`: every
conclusion alternative is `(z; L, R)` with `z` a `state` quantifier and every other quantifier of
export-free type, and every premise is an `if` outside the binding sites or `otherwise`. And at
every alternative, `L` passes the flow check (`NxTyped.tyOk`, `NxFlow.auxE`) and is export-free
(`NxSites.nxE`), so its value has no export list: then `L`'s value on the erased side *is* the
original instructions, and only `z` needs rebinding, to the original state. -/
def liftSimple : Rule → Bool
  | .ruleD nm qs op e prems =>
    ElseBwd.simpleRuleE (.ruleD nm qs op e prems) &&
      (conclAlts e).all fun e' => match ElseBwd.cfgVar e' with
        | some (_, l) => NxTyped.tyOk NxTyped.sigX NxTyped.tsigFixed (NxSites.quantsΓ qs) l &&
            NxFlow.auxE NxRule.ctx0 l && NxSites.nxE NxTyped.sigX (NxSites.quantsΓ qs) l
        | none => false

/-- The indices of the `Step_read` rules of `m` that pass `liftSimple`. -/
def liftSimpleIdx (m : Map RelDef) : List Nat :=
  m.flatMap fun p => if p.1 != "Step_read" then [] else
    (List.range p.2.2.2.2.length).filter fun i => match p.2.2.2.2[i]? with
      | some r => liftSimple r
      | none => false

/-- **The `Step_read` rules of the fixed script that pass `liftSimple`** (74 of 103,
`Round9.DerLift.liftSimpleIdx_fixed`). The 29 others: `block`, `loop` (0, 1), the four
`br_on_cast` rules (2–5), `return_call_ref` at a label, handler or frame (8–11), `throw_ref` at
instructions, a label or a frame (13–15), `try_table` (22), `vload-pack-val` (45),
`ref.test`/`ref.cast` (65–68), `struct.new_default` (69), `struct.get-struct` (71),
`array.new_default` (72), `array.new_data` (75, 76), `array.get-array` (79), `array.copy-le`,
`array.copy-gt` (91, 92), `array.init_data-oob2`, `array.init_data-num` (100, 102). -/
def liftSimpleRules : List Nat :=
  [6, 7, 12, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
    38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62,
    63, 64, 70, 73, 74, 77, 78, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 93, 94, 95, 96, 97, 98,
    99, 101]

/-- Every rule of every `Step_read` entry of `m` at an index of `l` passes `liftSimple`. -/
def liftSimpleIs (m : Map RelDef) (l : List Nat) : Bool :=
  m.all fun p => p.1 != "Step_read" || l.all fun i => match p.2.2.2.2[i]? with
    | some r => liftSimple r
    | none => false

/-! ## The second rule family: nothing to rebind -/

/-- **A rule with nothing to rebind.** Every quantifier has export-free type, and at every
conclusion alternative `(L, R)` the left-hand side `L` reads only quantifiers, passes the flow
check and is export-free, and the alternative passes round 3's check (`EraseAll.xExp`). Then the
original input has no export list, so it *is* the erased input, and the erased instance is
already an instance at the original input whose successor erasure fixes. -/
def liftNx : Rule → Bool
  | .ruleD _ qs _ e _ =>
    ElseRef.quantsNxL qs [] && (conclAlts e).all fun e' => match e' with
      | .tupE [l, _] => EraseDer.varsIn (Determ.quantNames qs) (freeExp l) &&
          NxTyped.tyOk NxTyped.sigX NxTyped.tsigFixed (NxSites.quantsΓ qs) l &&
          NxFlow.auxE NxRule.ctx0 l && NxSites.nxE NxTyped.sigX (NxSites.quantsΓ qs) l &&
          EraseAll.xExp EraseAll.grE EraseAll.gdE e'
      | _ => false

/-- The indices of the rules of the relation `x` of `m` that pass `liftNx`. -/
def liftNxIdx (m : Map RelDef) (x : IL.Id) : List Nat :=
  m.flatMap fun p => if p.1 != x then [] else
    (List.range p.2.2.2.2.length).filter fun i => match p.2.2.2.2[i]? with
      | some r => liftNx r
      | none => false

/-- **The `Step_pure` rules of the fixed script that pass `liftNx`** (66 of 79,
`Round9.DerLift.liftNxIdx_fixed`; no rule of `Step` or `Step_read` does, since their left-hand
side holds the state). The 13 others hold instruction sequences or a frame:
`if-true`, `if-false`, `label-vals`, `br-label-zero`, `br-label-succ`, `br-handler` (5–10),
`frame-vals`, `return-frame`, `return-label`, `return-handler` (21–24), `trap-instrs`,
`trap-label` (26, 27), `trap-frame` (29). -/
def liftNxRules : List Nat :=
  [0, 1, 2, 3, 4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 25, 28, 30, 31, 32, 33, 34, 35, 36, 37,
    38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
    62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]

/-- Every rule of every `x` entry of `m` at an index of `l` passes `liftNx`. -/
def liftNxIs (m : Map RelDef) (x : IL.Id) (l : List Nat) : Bool :=
  m.all fun p => p.1 != x || l.all fun i => match p.2.2.2.2[i]? with
    | some r => liftNx r
    | none => false

/-- The rules covered: `liftSimpleRules` of `Step_read`, `liftNxRules` of `Step_pure`. -/
def Covered (x : IL.Id) (i : Nat) : Prop :=
  (x = "Step_read" ∧ i ∈ liftSimpleRules) ∨ (x = "Step_pure" ∧ i ∈ liftNxRules)

/-! ## What is left -/

/-- **The rule obligations left** (open): `RuleLift` at the rules outside `Covered`: all 36 rules
of `Step`, the 29 rules of `Step_read` outside `liftSimpleRules` and the 13 rules of `Step_pure`
outside `liftNxRules`. With a provenance that types the state of a `Step_read` input and holds at
the original image, it gives `CoreStrip.EraseBwdAt` (`Round9.DerLift.eraseBwdAt_of_rest`). -/
def RuleLiftRest (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) : Prop :=
  ∀ x i, liftRel x = true → ¬ Covered x i → RuleLift env O Prov x i

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
