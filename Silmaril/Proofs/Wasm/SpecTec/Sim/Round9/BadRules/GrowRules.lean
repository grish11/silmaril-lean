module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.BlockRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Grow
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Inv
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.GrowRule

/-!
# Round 9, RE: `table.grow-succeed` and `memory.grow-succeed` go to the erased side

Both rules have the conclusion `(l, (%;% ($W(z, x, y), r)))` with `$W` one of `$with_tableinst`,
`$with_meminst`, excluded from the evaluator-level erasure because their body updates
`$sof(z)[.F[i] = y]` along a path ending at a module-instance field (round 3's `updOk`). Route 2
needs no such restriction for a single update: the one clause's body is evaluated across erasure
by hand (`withInstBody_erase`), reading the state `z = (S; F)` that the quantifier `z : state`
has (round 7's `state_inv`). The rest of the conclusion and the premises pass the checks (kernel
check `growShapeN_fixed`). Hence `ruleFwd_grow`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA eraseVs_eq_map)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grE gdE xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn growE evalExp_growE_iff)
open Silmaril.Wasm.SpecTec.Sim.Memory (withInstBody zxyPat WithInstDefs withInstDefs_simEnv)
open Silmaril.Wasm.SpecTec.Sim.State (StateDefs modAddr idxPayload)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB hasOptNil)

/-! ## The body of `$with_tableinst`/`$with_meminst` across erasure -/

section Body

variable {env : Env} (D : StateDefs env) {ρ₀ ρ₀' : VarEnv}
  (hf : ρ₀.findDef? "fof" = none) (hf' : ρ₀'.findDef? "fof" = none)
include D hf hf'

omit D hf hf' in
theorem idxPayload_erase (hx : ρ₀'.findVal? "x" = (ρ₀.findVal? "x").map eraseV) {v : Value}
    (h : EvalExp env ρ₀ idxPayload v) : EvalExp env ρ₀' idxPayload (eraseV v) := by
  obtain ⟨vs, hvs, h0, hv⟩ := evalExp_projE_iff.1 h
  have hX := evalExp_varE_iff.1 (evalExp_uncaseE_iff.1 hvs)
  refine evalExp_projE_iff.2 ⟨vs.map eraseV, evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 ?_), h0,
    by rw [List.getElem?_map, hv]; rfl⟩
  rw [hx, hX]
  simp [eraseV, eraseVs_eq_map]

/-- `$fof(z).MODULE.F[x!%.0]` across erasure. -/
theorem modAddr_erase {F' : AtomS} (hF' : F' ≠ "EXPORTS") {S F : Value}
    (hz : ρ₀.findVal? "z" = some (stV S F))
    (hz' : ρ₀'.findVal? "z" = some (stV (eraseV S) (eraseV F)))
    (hx : ρ₀'.findVal? "x" = (ρ₀.findVal? "x").map eraseV) {v : Value}
    (h : EvalExp env ρ₀ (modAddr F') v) : EvalExp env ρ₀' (modAddr F') (eraseV v) := by
  obtain ⟨w, i, h₁, h₂, h₃⟩ := evalExp_idxE_iff.1 h
  obtain ⟨w₁, h₁₁, hf₁⟩ := evalExp_dotE_iff.1 h₁
  obtain ⟨w₂, h₂₂, hf₂⟩ := evalExp_dotE_iff.1 h₁₁
  obtain rfl := EvalExp.unique h₂₂ (State.evalExp_fof D hf (evalExp_var hz))
  refine evalExp_idxE_iff.2 ⟨eraseV w, i, evalExp_dotE_iff.2 ⟨eraseV w₁,
    evalExp_dotE_iff.2 ⟨eraseV w₂, State.evalExp_fof D hf' (evalExp_var hz'), ?_⟩, ?_⟩,
    idxPayload_erase hx h₂, ?_⟩
  · rw [Swap.field?_eraseV (by decide), hf₂]; rfl
  · rw [Swap.field?_eraseV hF', hf₁]; rfl
  · rw [Swap.idx?_eraseV, h₃]; rfl

omit D hf hf' in
/-- An update `v[.F[e] = w]` across erasure, given that the index goes across. -/
theorem pathSet_idxDot_erase {F' : AtomS} (hF' : F' ≠ "EXPORTS") {e : Exp} {v w r : Value}
    (he : ∀ iv, EvalExp env ρ₀ e iv → EvalExp env ρ₀' e (eraseV iv))
    (h : PathSet env ρ₀ v (.idxP (.dotP .rootP F') e) w r) :
    PathSet env ρ₀' (eraseV v) (.idxP (.dotP .rootP F') e) (eraseV w) (eraseV r) := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [pathSet] at h
  simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
  obtain ⟨u, hu, iv, hiv, i, hi, u', hu', hr⟩ := h
  rcases n with _ | n
  · simp [pathGet] at hu
  simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hu
  obtain ⟨v₀, hv₀, hfu⟩ := hu
  rcases n with _ | n
  · simp [pathGet] at hv₀
  simp only [pathGet] at hv₀
  cases hv₀
  simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hr
  obtain ⟨v₁, hv₁, u'', hu'', hr⟩ := hr
  simp only [pathGet] at hv₁
  cases hv₁
  cases hr
  have hiv' : iv = .num (.natN i) := by
    cases iv with
    | num m => cases m <;> simp_all [Value.asNat?]
    | _ => simp [Value.asNat?] at hi
  subst hiv'
  exact State.pathSet_idx (State.pathGet_dot State.pathGet_root
      (by rw [Swap.field?_eraseV hF', hfu]; rfl))
    (by simpa [eraseV] using he _ ⟨_, hiv⟩)
    (by rw [Swap.setIdx_eraseV, hu']; rfl)
    (State.pathSet_dot State.pathGet_root (by rw [Swap.setField_eraseV hF', hu'']; rfl)
      State.pathSet_root)

/-- **The body `$sof(z)[.F[$fof(z).MODULE.F[x]] = y]; $fof(z)` across erasure**, from a scope
binding `z` to a state to the scope of the erased values. -/
theorem withInstBody_erase (hs : ρ₀.findDef? "sof" = none) (hs' : ρ₀'.findDef? "sof" = none)
    {F' : AtomS} (hF' : F' ≠ "EXPORTS") {y : IL.Id} {S F : Value}
    (hz : ρ₀.findVal? "z" = some (stV S F))
    (hz' : ρ₀'.findVal? "z" = some (stV (eraseV S) (eraseV F)))
    (hx : ρ₀'.findVal? "x" = (ρ₀.findVal? "x").map eraseV)
    (hy : ρ₀'.findVal? y = (ρ₀.findVal? y).map eraseV) {u : Value}
    (h : EvalExp env ρ₀ (withInstBody F' y) u) :
    EvalExp env ρ₀' (withInstBody F' y) (eraseV u) := by
  unfold withInstBody at h ⊢
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨u₁, vs', h₁, hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨u₂, vs'', h₂, hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  obtain rfl := EvalExp.unique h₂ (State.evalExp_fof D hf (evalExp_var hz))
  obtain ⟨v₁, v₂, hv₁, hv₂, hps⟩ := evalExp_updE_iff.1 h₁
  obtain rfl := EvalExp.unique hv₁ (State.evalExp_sof D hs (evalExp_var hz))
  have hY := evalExp_varE_iff.1 hv₂
  have hps' := pathSet_idxDot_erase hF'
    (fun iv hiv => modAddr_erase D hf hf' hF' hz hz' hx hiv) hps
  have hu₁ : EvalExp env ρ₀' (.updE (.callE "sof" [.expA (.varE "z")])
      (.idxP (.dotP .rootP F') (modAddr F')) (.varE y)) (eraseV u₁) :=
    evalExp_updE_iff.2 ⟨_, _, State.evalExp_sof D hs' (evalExp_var hz'),
      evalExp_var (by rw [hy, hY]; rfl), hps'⟩
  have he := evalExp_case (op := "%;%") (evalExp_tup2 hu₁
    (State.evalExp_fof D hf' (evalExp_var hz')))
  simpa [eraseV, eraseVs_eq_map] using he

end Body

/-! ## The call -/

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- The updaters in the round-7 environment. -/
theorem withInstDefs_utf8Env (B : Builtins) : WithInstDefs (utf8Env B) :=
  ⟨EraseAll.hasClause1_utf8Env (by decide) (withInstDefs_simEnv B).withTableinst,
    EraseAll.hasClause1_utf8Env (by decide) (withInstDefs_simEnv B).withMeminst⟩

/-- The updaters have no primitive. -/
theorem call_withInst_none {w : IL.Id} (hw : w = "with_tableinst" ∨ w = "with_meminst")
    (ws : List ArgV) : (utf8Env (Round4Int.BI P hn host)).builtins.call w ws = none := by
  show (if w = "utf8" then Round6.MemSimd.utf8Call ws else Prims.call P hn host w ws) = none
  rcases hw with rfl | rfl <;>
    simp [Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- The one clause of an updater, by name. -/
theorem withInst_clause {w : IL.Id} {F' : AtomS} {y : IL.Id}
    (hw : (w = "with_tableinst" ∧ F' = "TABLES" ∧ y = "ti") ∨
      (w = "with_meminst" ∧ F' = "MEMS" ∧ y = "mi")) (B : Builtins) :
    State.HasClause1 (utf8Env B) w (zxyPat y) (withInstBody F' y) := by
  rcases hw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact (withInstDefs_utf8Env B).withTableinst
  · exact (withInstDefs_utf8Env B).withMeminst

/-- **`$W(z, x, y)` across erasure**, in a scope binding `z` to a state. -/
theorem callW_erase {w : IL.Id} {F' : AtomS} {y : IL.Id}
    (hw : (w = "with_tableinst" ∧ F' = "TABLES" ∧ y = "ti") ∨
      (w = "with_meminst" ∧ F' = "MEMS" ∧ y = "mi"))
    {ρ : VarEnv} (hd : ∀ g, ρ.findDef? g = none) {S F X Y u : Value}
    (hz : ρ.findVal? "z" = some (stV S F)) (hx : ρ.findVal? "x" = some X)
    (hy : ρ.findVal? y = some Y)
    (h : EvalExp (utf8Env (Round4Int.BI P hn host)) ρ
      (.callE w [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE y)]) u) :
    EvalExp (utf8Env (Round4Int.BI P hn host)) (eraseScope ρ)
      (.callE w [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE y)]) (eraseV u) := by
  have hcl := withInst_clause hw (Round4Int.BI P hn host)
  have hw' : w = "with_tableinst" ∨ w = "with_meminst" := by
    rcases hw with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hy' : y ≠ "z" ∧ y ≠ "x" ∧ y ≠ "_" := by
    rcases hw with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> decide
  have hF' : F' ≠ "EXPORTS" := by rcases hw with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> decide
  have ha : EvalArgs (utf8Env (Round4Int.BI P hn host)) ρ
      [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE y)] [.val (stV S F), .val X, .val Y] :=
    Equiv.evalArgs_cons (evalExp_var hz) (Equiv.evalArgs_cons (evalExp_var hx)
      (Equiv.evalArgs_cons (evalExp_var hy) Equiv.evalArgs_nil))
  obtain ⟨ρ₀, hm, hb⟩ := BwdRead.evalExp_call1_inv hcl (hd w) (call_withInst_none P hn host hw' _)
    ha h
  have hfy : ((VarEnv.empty.bindVal "z" (stV S F)).bindVal "x" X).findVal? y = none := by
    simp [Ne.symm hy'.1, Ne.symm hy'.2.1]
  obtain rfl := Prims.matchArgs_unique hm (Memory.matchArgs_zxyPat hfy)
  have hfy' : ((VarEnv.empty.bindVal "z" (eraseV (stV S F))).bindVal "x" (eraseV X)).findVal? y =
      none := by
    simp [Ne.symm hy'.1, Ne.symm hy'.2.1]
  have hS := EraseAll.stateDefs_utf8Env (Round4Int.BI P hn host)
  have hb' := withInstBody_erase (h := hb) (S := S) (F := F)
    (ρ₀' := ((VarEnv.empty.bindVal "z" (eraseV (stV S F))).bindVal "x" (eraseV X)).bindVal y
      (eraseV Y)) hS rfl rfl rfl rfl hF'
    (by simp [hy'.1]) (by simp [hy'.1, stV, eraseV, eraseVs_eq_map]) (by simp [hy'.2.1])
    (by simp [Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit hy'.2.2])
  refine State.evalExp_call1 hcl (by rw [EraseAll.eraseScope_findDef]; exact hd w) ?_
    (Memory.matchArgs_zxyPat hfy') hb'
  refine Equiv.evalArgs_cons (evalExp_var ?_) (Equiv.evalArgs_cons (evalExp_var ?_)
    (Equiv.evalArgs_cons (evalExp_var ?_) Equiv.evalArgs_nil))
  · rw [Erase.find?_eraseScope, hz]; rfl
  · rw [Erase.find?_eraseScope, hx]; rfl
  · rw [Erase.find?_eraseScope, hy]; rfl

/-! ## The rules -/

/-- An expression passing every check of the evaluator-level erasure, in the scope of `qs`. -/
def closedOk (qs : List Param) (e : Exp) : Bool :=
  xExp grE gdE e && tyOk sigX tsigFixed (quantsΓ qs) e && auxE ctx0 e && NxErase.auxX ctx0 e &&
    badE sigX (quantsΓ qs) e == 0 && varsIn (quantNames qs) (freeExp e)

/-- Some quantifier of `qs` is named `y`. -/
def hasName (qs : List Param) (y : String) : Bool :=
  qs.any fun q => match q with
    | .expP y' _ => y' == y
    | _ => false

/-- **The shape of the grow rules**: conclusion `(l, (%;% ($W(z, x, y), r)))` without optional
alternatives, `$W` an updater with its field and variable, `l` and `r` passing every check,
premises passing `BadN.premN`, and quantifiers `z : state`, `x`, `y`. -/
def growShapeN : Rule → Bool
  | .ruleD _ qs _ e prems =>
    match e with
    | .tupE [l, .caseE "%;%" (.tupE [.callE w [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.varE y)], r])] =>
      !hasOptNil e && ((w == "with_tableinst" && y == "ti") || (w == "with_meminst" && y == "mi")) &&
        closedOk qs l && closedOk qs r && prems.all BadN.premN && hasQ qs "z" "state" &&
        hasName qs "x" && hasName qs y
    | _ => false

/-- The two grow rules. -/
def growNamesN : List String := ["table.grow-succeed", "memory.grow-succeed"]

set_option maxRecDepth 100000 in
/-- **The grow rules have the shape.** -/
theorem growShapeN_fixed : (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).all (fun p =>
    !Round8.NxStep.stepRel p.1 || p.2.2.2.2.all fun r =>
      !growNamesN.contains (ruleName r) || growShapeN r) = true := by
  decide +kernel

theorem hasName_mem {qs : List Param} {y : String} (h : hasName qs y = true) :
    ∃ t, Param.expP y t ∈ qs := by
  obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h
  split at hq'
  · rename_i y' t
    simp only [beq_iff_eq] at hq'
    subst hq'
    exact ⟨t, hq⟩
  · cases hq'

theorem closedOk_inv {qs : List Param} {e : Exp} (h : closedOk qs e = true) :
    xExp grE gdE e = true ∧ tyOk sigX tsigFixed (quantsΓ qs) e = true ∧ auxE ctx0 e = true ∧
      NxErase.auxX ctx0 e = true ∧ badE sigX (quantsΓ qs) e = 0 ∧
      varsIn (quantNames qs) (freeExp e) = true := by
  simp only [closedOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- What `growShapeN` says. -/
structure GrowFactsN (qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  shape : ∃ l w F' y r, e = growE l w "x" y r ∧
    ((w = "with_tableinst" ∧ F' = "TABLES" ∧ y = "ti") ∨
      (w = "with_meminst" ∧ F' = "MEMS" ∧ y = "mi")) ∧
    closedOk qs l = true ∧ closedOk qs r = true ∧ (∃ t, Param.expP y t ∈ qs)
  alts : conclAlts e = [e]
  prems : ∀ pr ∈ prems, BadN.premN pr = true
  z : Param.expP "z" (.varT "state" []) ∈ qs
  x : ∃ t, Param.expP "x" t ∈ qs

theorem growShapeN_inv {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : growShapeN (.ruleD nm qs op e prems) = true) :
    GrowFactsN qs e prems := by
  simp only [growShapeN] at h
  split at h
  · rename_i l w y r
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hno, hw⟩, hl⟩, hr⟩, hp⟩, hz⟩, hx⟩, hy⟩ := h
    refine ⟨⟨l, w, if w = "with_tableinst" then "TABLES" else "MEMS", y, r, rfl, ?_, hl, hr,
      hasName_mem hy⟩, by simp [conclAlts, hno], hp, hasQ_mem hz, hasName_mem hx⟩
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl, rfl⟩
    · exact .inr ⟨rfl, by simp, rfl⟩
  · cases h

theorem growFactsN {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hnm : nm ∈ growNamesN) :
    GrowFactsN qs e prems := by
  rw [findRel?_utf8Env] at hrel
  have hm := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 growShapeN_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simp only [ruleName, List.contains_iff_mem.2 hnm, Bool.not_true, Bool.false_or] at h'
  exact growShapeN_inv h'

/-- A closed checked expression of a rule instance at round 4's primitives goes across. -/
theorem closed_fwd {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {e₀ : Exp} {prems : List Prem}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (NxPrims.envBI P hn host).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e₀ prems)) {σ : List (IL.Id × Value)}
    (hq : QuantsOk (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) qs) {e : Exp}
    (hc : closedOk qs e = true) {v : Value}
    (h : EvalExp (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) e v) :
    EvalExp (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ)) e (eraseV v) := by
  obtain ⟨hxe, hte, hae, hXe, hbe, hce⟩ := closedOk_inv hc
  have hr : reach 0 x = true := Round8.NxStep.reach_stepRel hx
  have hw := (NxRule.rFacts hr hrel hrule).wild
  have hD := NxFlow.flowSound _ (NxPrims.builtinsVT_BI P hn host)
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (NxPrims.envBI P hn host)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase _ (NxPrims.builtinsVT_BI P hn host)
      (NxClause.biErase_QT_BI P hn host) _ k rfl rfl
  obtain ⟨n, hn'⟩ := h
  refine ⟨n, ?_⟩
  rw [NxErase.erase_closed hD (NxClause.biErase_QT_BI P hn host) hq hw hCE hce hte hae hXe hbe
    hxe n, hn']
  rfl

/-- **`table.grow-succeed` and `memory.grow-succeed` go to the erased side** at round 4's
primitives. -/
theorem ruleFwd_grow {nm : IL.Id} (hnm : nm ∈ growNamesN) :
    RuleFwdNm (NxPrims.envBI P hn host) nm := by
  intro x op args i v ps t rules qs e e' prems ρ₀ σ hx hrel hrule halt hps hq he hp
  have hB := NxPrims.builtinsVT_BI P hn host
  have H := NxClause.biErase_QT_BI P hn host
  have hF := growFactsN hx hrel hrule hnm
  rw [hF.alts, List.mem_singleton] at halt
  subst halt
  refine ruleFwdX hB H hx hrel hrule (by rw [hF.alts]; exact List.mem_singleton_self _) hps hq
    (fun hρ => ?_) (fun pr hpr _ => hp pr hpr)
    (fun pr hpr hN _ _ => absurd (hF.prems pr hpr) (by simp [hN]))
  subst hρ
  obtain ⟨l, w, F', y, r, rfl, hw, hl, hr, ⟨ty, hyq⟩⟩ := hF.shape
  obtain ⟨vl, u, vr, hvl, hu, hvr, rfl⟩ := evalExp_growE_iff.1 he
  obtain ⟨Z, fz, hZ⟩ := hq _ _ hF.z
  obtain ⟨S, F, rfl, -⟩ := EraseDer.state_inv rfl hZ
  obtain ⟨tx, hxq⟩ := hF.x
  obtain ⟨X, fx, -⟩ := hq _ _ hxq
  obtain ⟨Y, fy, -⟩ := hq _ _ hyq
  have hu' := callW_erase P hn host hw (fun g => rfl) fz fx fy hu
  have he' := evalExp_growE_iff.2 ⟨_, _, _, closed_fwd P hn host hx hrel hrule hq hl hvl, hu',
    closed_fwd P hn host hx hrel hrule hq hr hvr, rfl⟩
  simpa [eraseV, eraseVs_eq_map] using he'

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
