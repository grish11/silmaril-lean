module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.Rule
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.Blocktype
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.Names
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Value
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Block
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Thms

/-!
# Round 9, RE: `block`, `loop` and `try_table` go to the erased side

The three rules of `Step_read` have the one premise `if $blocktype_(z, bt) = R`, where `R` passes
every check of the evaluator-level erasure (kernel check `btShape_fixed`). Erasure fixes `bt`
(its type `blocktype` is export-free), so `$blocktype_` goes across by
`applies_blocktype_erase`, `R` by round 7's `NxErase.erase_closed`, and the equality holds on
the erased side. The conclusion passes round 3's check. Hence `ruleFwd_block`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grE gdE xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

/-! ## The shape, checked by the kernel -/

/-- The quantifier `y : t` (a type name without arguments) is among `qs`. -/
def hasQ (qs : List Param) (y t : String) : Bool :=
  qs.any fun q => match q with
    | .expP y' (.varT t' []) => y' == y && t' == t
    | _ => false

/-- **The shape of `block`, `loop` and `try_table`**: one premise
`if $blocktype_(z, bt) = R` with `R` passing every check of the erasure, a conclusion passing
round 3's check, and quantifiers `z : state`, `bt : blocktype`. -/
def btShape : Rule → Bool
  | .ruleD _ qs _ e [.ifPr (.cmpE .eqOp _ (.callE "blocktype_"
      [.expA (.varE "z"), .expA (.varE "bt")]) R)] =>
    (conclAlts e).all (xExp grE gdE) && xExp grE gdE R &&
      tyOk sigX tsigFixed (quantsΓ qs) R && auxE ctx0 R && NxErase.auxX ctx0 R &&
      badE sigX (quantsΓ qs) R == 0 && varsIn (quantNames qs) (freeExp R) &&
      hasQ qs "z" "state" && hasQ qs "bt" "blocktype"
  | _ => false

/-- The three rule names. -/
def btNames : List String := ["block", "loop", "try_table"]

set_option maxRecDepth 100000 in
/-- **`block`, `loop` and `try_table` have the shape.** -/
theorem btShape_fixed : (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).all (fun p =>
    !Round8.NxStep.stepRel p.1 || p.2.2.2.2.all fun r =>
      !btNames.contains (ruleName r) || btShape r) = true := by
  decide +kernel

theorem hasQ_mem {qs : List Param} {y t : String} (h : hasQ qs y t = true) :
    Param.expP y (.varT t []) ∈ qs := by
  obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h
  split at hq'
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    exact hq
  · cases hq'

/-- What `btShape` says. -/
structure BtFacts (qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  prems : ∃ ty R, prems = [.ifPr (.cmpE .eqOp ty (.callE "blocktype_"
      [.expA (.varE "z"), .expA (.varE "bt")]) R)] ∧
    xExp grE gdE R = true ∧ tyOk sigX tsigFixed (quantsΓ qs) R = true ∧ auxE ctx0 R = true ∧
    NxErase.auxX ctx0 R = true ∧ badE sigX (quantsΓ qs) R = 0 ∧
    varsIn (quantNames qs) (freeExp R) = true
  alts : ∀ e' ∈ conclAlts e, xExp grE gdE e' = true
  z : Param.expP "z" (.varT "state" []) ∈ qs
  bt : Param.expP "bt" (.varT "blocktype" []) ∈ qs

theorem btShape_inv {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    (h : btShape (.ruleD nm qs op e prems) = true) : BtFacts qs e prems := by
  unfold btShape at h
  split at h
  · rename_i ty R heq
    simp only [Rule.ruleD.injEq] at heq
    obtain ⟨-, rfl, -, rfl, rfl⟩ := heq
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩, h₉⟩ := h
    exact ⟨⟨ty, R, rfl, h₂, h₃, h₄, h₅, h₆, h₇⟩, h₁, hasQ_mem h₈, hasQ_mem h₉⟩
  · cases h

theorem btFacts {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hnm : nm ∈ btNames) :
    BtFacts qs e prems := by
  rw [findRel?_utf8Env] at hrel
  have hm := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 btShape_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simp only [ruleName, List.contains_iff_mem.2 hnm, Bool.not_true, Bool.false_or] at h'
  exact btShape_inv h'

/-! ## The premise -/

theorem nxAT_blocktype : nxAT sigX.good (toAT (.varT "blocktype" [])) = true := by
  decide +kernel

theorem findDef_bindVals (σ : List (IL.Id × Value)) (y : IL.Id) :
    (VarEnv.empty.bindVals σ).findDef? y = none := rfl

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **The premise of `block`, `loop` and `try_table` goes to the erased side.** -/
theorem btPrem_fwd {qs : List Param} {σ : List (IL.Id × Value)} {ty : OpTyp} {R : Exp}
    (hq : QuantsOk (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) qs)
    (hw : "_" ∉ quantNames qs)
    (hz : Param.expP "z" (.varT "state" []) ∈ qs)
    (hbt : Param.expP "bt" (.varT "blocktype" []) ∈ qs)
    (hxR : xExp grE gdE R = true) (htR : tyOk sigX tsigFixed (quantsΓ qs) R = true)
    (haR : auxE ctx0 R = true) (hXR : NxErase.auxX ctx0 R = true)
    (hbR : badE sigX (quantsΓ qs) R = 0) (hcR : varsIn (quantNames qs) (freeExp R) = true)
    (h : EvalExp (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp ty (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")]) R)
      (.bool true)) :
    EvalExp (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ))
      (.cmpE .eqOp ty (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")]) R)
      (.bool true) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e : v₁ = v₂ := by simpa [cmpValues] using hc
  subst e
  obtain ⟨Z, fz⟩ : ∃ Z, (VarEnv.empty.bindVals σ).findVal? "z" = some Z := by
    obtain ⟨w, hw', -⟩ := hq _ _ hz
    exact ⟨w, hw'⟩
  obtain ⟨W, fW, hvt⟩ := NxQuant.vtB_of_quantsOk (NxRule.typsNx_inst σ) hq hbt
  have hW : eraseV W = W :=
    Swap.eraseV_of_nxB _ (NxTyped.nxB_of_vtB nxAT_blocktype hvt)
  have happ := Bwd.applies_of_call2 (findDef_bindVals σ _) fz fW h₁
  have happ' := applies_blocktype_erase P hn host hW happ
  have fz' : (eraseScope (VarEnv.empty.bindVals σ)).findVal? "z" = some (eraseV Z) := by
    rw [Erase.find?_eraseScope, fz]; rfl
  have fW' : (eraseScope (VarEnv.empty.bindVals σ)).findVal? "bt" = some W := by
    rw [Erase.find?_eraseScope, fW]; simp [hW]
  have h₁' : EvalExp (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ))
      (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")]) (eraseV v₁) :=
    evalExp_callE_iff.2 ((Silmaril.SpecTec.Equiv.ExecNumeric.applies_iff_callDef
      (by rw [EraseAll.eraseScope_findDef]; rfl)
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 fz')
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 fW') (evalArgs_nil _ _)))).1 happ')
  have hD := NxFlow.flowSound _ (NxPrims.builtinsVT_BI P hn host)
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (NxPrims.envBI P hn host)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase _ (NxPrims.builtinsVT_BI P hn host)
      (NxClause.biErase_QT_BI P hn host) _ k rfl rfl
  have h₂' : EvalExp (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ)) R
      (eraseV v₁) := by
    obtain ⟨n, hn'⟩ := h₂
    refine ⟨n, ?_⟩
    rw [NxErase.erase_closed hD (NxClause.biErase_QT_BI P hn host) hq hw hCE hcR htR haR hXR hbR
      hxR n, hn']
    rfl
  exact evalExp_cmpE_iff.2 ⟨_, _, h₁', h₂', by simp [cmpValues]⟩

/-! ## The rules -/

/-- **`block`, `loop` and `try_table` go to the erased side** at round 4's primitives. -/
theorem ruleFwd_block {nm : IL.Id} (hnm : nm ∈ btNames) :
    RuleFwdNm (NxPrims.envBI P hn host) nm := by
  intro x op args i v ps t rules qs e e' prems ρ₀ σ hx hrel hrule halt hps hq he hp
  have hB := NxPrims.builtinsVT_BI P hn host
  have H := NxClause.biErase_QT_BI P hn host
  have hF := btFacts hx hrel hrule hnm
  have hr : reach 0 x = true := Round8.NxStep.reach_stepRel hx
  have hw := (NxRule.rFacts hr hrel hrule).wild
  obtain ⟨ty, R, rfl, hxR, htR, haR, hXR, hbR, hcR⟩ := hF.prems
  refine ruleFwdX hB H hx hrel hrule halt hps hq (fun hρ => ?_) (fun pr hpr _ => hp pr hpr)
    (fun pr hpr _ hρ _ => ?_)
  · subst hρ
    exact concl_fwd hB H hx hrel hrule halt hq (hF.alts e' halt) he
  · subst hρ
    obtain rfl := List.mem_singleton.1 hpr
    cases hp _ (List.mem_singleton_self _) with
    | ifPr h =>
      exact .ifPr (btPrem_fwd P hn host hq hw hF.z hF.bt hxR htR haR hXR hbR hcR h)

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
