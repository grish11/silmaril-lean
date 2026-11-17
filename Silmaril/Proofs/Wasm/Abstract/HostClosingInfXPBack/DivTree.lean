module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.DivHead

/-!
# Divergence after a nonempty log: the tree cases (proofs)

A head tree `e` diverging alone after the events (`EvDiv` of `xcode stk [e]`), for each form of
tree. Its parts are split off (`evDiv_seq_split`, `evDiv_label_seq_split`,
`evDiv_handler_seq_split`): a part diverging with the whole log is the next problem (arguments,
condition, block, loop, arm and handler bodies, `DivG`; a callee at `call`, a resolved
`call_indirect` or a `call_ref`, `CallDivG`); a part run to completion is read back
(`evRunN_back_vals`, `evRunN_back`) and goes on. A loop body branching back re-enters the loop
on a strictly shorter divergence (its entry being its only step). Every other end of the head
tree is a finished logged run of it, ruled out by `head_contra`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H}
  {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (wasmHostSig H))} {n : Nat}

/-! ## Operators -/

/-- **An operator diverging alone**: in its arguments, or in the callee of a call. -/
theorem headDiv_op (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {i : Instr} {args es : List BExpr} (ihA : DivG tags o host n args)
    (ihC : ∀ m ≤ n, CallDivG tags o host m) (ht : TypedP tags s f stk (.op i args :: es))
    (hdv : EvDiv (profile o) host n ⟨s, f, xcode stk [.op i args]⟩ cs) :
    DivOut s f stk (.op i args :: es) cs := by
  have ht1 := typedP_head ht
  have hdv₀ := hdv
  have hcode : xcode stk [.op i args] = xcode stk args ++ [.plain i] := by
    simp [xcode, expression]
  rw [hcode] at hdv
  rcases evDiv_seq_split hdv with hda | ⟨⟨s₁, f₁, k₁⟩, n₁, m, cs₁, cs₂, ws, rfl, hm, hr₁, hw, hd₁⟩
  · exact divOut_lift₀ (fun _ => LogDivXP.args) (fun _ _ => ReachLXP.args)
      (ihA s f stk cs (args_typedP ht) hda)
  dsimp only at hw hd₁
  subst hw
  obtain ⟨l₁, stk₁, hd, hq, rfl⟩ := evRunN_back_vals hT hH hE (args_typedP ht) hr₁
  have hcons := consistent_append (evDiv_consistent hdv₀)
  obtain ⟨rest₀, hsite, hTF, hTM, hS₁, hts₁, labels, ret, o', hf⟩ :=
    site_factsH hT hH hE ht1 hd hq hcons.1 (evRunN_steps hr₁)
  have htK : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ [.plain i] ++ []⟩ := by
    have h0 := typedP_ctx' ht1
    rw [hcode] at h0
    have := ContextTyped.steps_typed hT h0 (Steps.append [.plain i] (evRunN_steps hr₁))
    simpa using this
  have hd₁' : EvDiv (profile o) host m ⟨s₁, f₁, vals stk₁.reverse ++ [.plain i] ++ []⟩ cs₂ := by
    simpa using hd₁
  have contra : ∀ {r : Store H × Frame × POut},
      EvalLXPh s f stk [.op i args] l₁ r → False := fun hd' =>
    head_contra hT hH hE ht1 hd' (.inl hq) hdv₀
  have contra' : ∀ {r : Store H × Frame × POut},
      EvalLXPh s f stk [.op i args] (l₁ ++ []) r → False := fun hd' => contra (by simpa using hd')
  rcases instr_cases i with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ |
    (⟨x, rfl⟩ | rfl) | ⟨hi, hx⟩
  · -- call
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    obtain ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩ := callArity_func? hpq
    have hst₁ : Steps (profile o) NH ⟨s₁, f₁, vals stk₁.reverse ++ [.plain (.call x)] ++ []⟩
        ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse a
          (.callRefType fi.type) []⟩ := by
      rw [← callCode_split]
      exact .single (Silmaril.Wasm.Logic.Core.Step.ctx _ _
        (Step.call (module_of_func? hfi) (funcs_of_func? hfi)))
    have hz := ihC m hm s₁ f₁ _ _ a (.callRefType fi.type) cs₂ trivial
      ⟨hS₁, hts₁, fi, ps, rs, funcs_of_func? hfi, hty, take_rev_length hp⟩ (htK.steps hst₁)
      (evDiv_through_steps hst₁ htK hd₁')
    exact .inr ⟨l₁, ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩, cs₁, cs₂, .call hd hfi hty, hq,
      hz, rfl⟩
  · -- call_indirect
    obtain ⟨ad, j, stk', o'', rfl, hres⟩ := indirect_res (.inl rfl) hsite
    cases o'' with
    | none => exact (contra (.indRes hd hres)).elim
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      have hf_t := hf
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
      have e : vals (Val.num ⟨.int ad.intType, j⟩ :: stk').reverse ++
          [.plain (.callIndirect x y)] ++ [] =
          vals stk'.reverse ++ [aconst ad j, .plain (.callIndirect x y)] ++ [] := by
        rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]; simp
      have hst₀ : Steps (profile o) NH ⟨s₁, f₁, vals (Val.num ⟨.int ad.intType, j⟩ :: stk').reverse ++
          [.plain (.callIndirect x y)] ++ []⟩
          ⟨s₁, f₁, vals stk'.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ []⟩ := by
        rw [e]
        exact Steps.ctx _ _ (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
      have hct₀ := ContextTyped.steps_typed hT htK (steps_host hst₀)
      obtain ⟨ps, rs, hty⟩ := funcType_of_callRef_cfg (P := profile o)
        (by simpa only [List.append_assoc, List.cons_append, List.singleton_append] using hct₀)
        (cr := .plain (.callRef y)) trivial hfi
      have hy := Abstract.CallXT.typeArity_of_indRes hres hfi hty hTF hTM
        (types_some_of_flatChkT hf_t)
      obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf_t
      simp only [List.length_cons] at hp
      have hst₁ : Steps (profile o) NH ⟨s₁, f₁,
          vals (Val.num ⟨.int ad.intType, j⟩ :: stk').reverse ++ [.plain (.callIndirect x y)] ++ []⟩
          ⟨s₁, f₁, Interp.callCode (stk'.drop ps.length).reverse (stk'.take ps.length).reverse fa
            (.plain (.callRef y)) []⟩ := by
        rw [← callCode_split]; exact hst₀
      have hz := ihC m hm s₁ f₁ _ _ fa (.plain (.callRef y)) cs₂ trivial
        ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, take_rev_length (by omega)⟩ (htK.steps hst₁)
        (evDiv_through_steps hst₁ htK hd₁')
      exact .inr ⟨l₁, ⟨fa, ((stk'.take ps.length).reverse, s₁)⟩, cs₁, cs₂,
        .ind hd hres hfi hty hy, hq, hz, rfl⟩
  · -- call_ref
    obtain ⟨r, stk', rfl, hr⟩ := callRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact (contra (.refNull hd)).elim
    have e : vals (Val.ref (.func fa) :: stk').reverse ++ .plain (.callRef y) :: rest₀ =
        vals stk'.reverse ++ .ref (.func fa) :: .plain (.callRef y) :: rest₀ := by
      simp [vals, Val.toAdmin]
    obtain ⟨ps, rs, hty⟩ := funcType_of_callRef_cfg (P := profile o) (e ▸ hsite)
      (cr := .plain (.callRef y)) trivial hfi
    have hy := Abstract.CallXT.typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf_t
    simp only [List.length_cons] at hp
    have e' : vals (Val.ref (.func fa) :: stk').reverse ++ [.plain (.callRef y)] ++ [] =
        Interp.callCode (stk'.drop ps.length).reverse (stk'.take ps.length).reverse fa
          (.plain (.callRef y)) [] := by
      rw [← callCode_split]; simp [vals, Val.toAdmin]
    have hz := ihC m hm s₁ f₁ _ _ fa (.plain (.callRef y)) cs₂ trivial
      ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, take_rev_length (by omega)⟩ (e' ▸ htK) (e' ▸ hd₁')
    exact .inr ⟨l₁, ⟨fa, ((stk'.take ps.length).reverse, s₁)⟩, cs₁, cs₂, .ref hd hfi hty hy, hq,
      hz, rfl⟩
  · -- return_call
    exfalso
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    have hca : ∃ p, callArity s₁.funcs f₁.module x = some p := by
      cases h : callArity s₁.funcs f₁.module x with
      | none => simp [flatChkE, tExt, h, extStep] at hf_t
      | some p => exact ⟨p, rfl⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := hca
    obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := callArity_func? hpq
    exact contra (.tail hd (.direct hfi) (funcs_of_func? hfi) hty
      (tailAnn_typed (.direct hfi) hsite (funcs_of_func? hfi) hty hTF hTM hf_t))
  · -- return_call_indirect
    exfalso
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    obtain ⟨ad, j, stk', o'', rfl, hres⟩ := indirect_res (.inr rfl) hsite
    cases o'' with
    | none => exact contra (.tailRes hd (.indirectTrap hres))
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      obtain ⟨p, hy₀⟩ := typeArity_some_rci' hf_t
      obtain ⟨ps, rs, hty⟩ := funcType_of_indRes hres hfi hTF hTM hy₀
      exact contra (.tail hd (.indirect hres) hfi hty
        (tailAnn_typed (.indirect hres) hsite hfi hty hTF hTM hf_t))
  · -- return_call_ref
    exfalso
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    obtain ⟨r, stk', rfl, hr⟩ := returnCallRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact contra (.tailRes hd .refNull)
    · obtain ⟨ps, rs, hty⟩ := funcType_of_returnCallRef_site hsite hTM hfi (hTF _ _ hfi)
      exact contra (.tail hd .ref hfi hty (tailAnn_typed .ref hsite hfi hty hTF hTM hf_t))
  · -- throw
    exfalso
    obtain ⟨p, htf, hp⟩ := throw_chk hf
    obtain ⟨ta, ti, ts, ht', he, hlen⟩ := tag_of_tagFields hts₁.1 htf
    exact contra (.throw hd ht' he (by omega))
  · -- throw_ref
    exfalso
    obtain ⟨r, stk', rfl, hr⟩ := throwRef_top hsite
    rcases hr with rfl | ⟨a, rfl⟩
    · exact contra (.throwRefNull hd)
    · exact contra (.throwRefExn hd)
  · -- a flat instruction
    exfalso
    have hf' : flatChk s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o' := by
      rw [← flatChkE_eq_flatChk (ehExt tags) hx]; exact hf
    obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := evalFlat_progressH hf' hi hsite
    by_cases hn₂ : fl₂.IsNormal
    · rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn₂
      exact contra' (.opOk hi hd hflat .nil)
    · exact contra (.opStop hi hd hflat hn₂)

/-! ## Blocks and loops -/

/-- **A block diverging alone**: in its body. -/
theorem headDiv_block (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {body es : List BExpr} (ihB : DivG tags o host n body)
    (ht : TypedP tags s f stk (.block bt body :: es))
    (hdv : EvDiv (profile o) host n ⟨s, f, xcode stk [.block bt body]⟩ cs) :
    DivOut s f stk (.block bt body :: es) cs := by
  have ht1 := typedP_head ht
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, hp, -, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  have henter : Steps (profile o) NH ⟨s, f, xcode stk [.block bt body]⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label nr [] (xcode (stk.take np) body)] ++ []⟩ := by
    rw [xcode, code_block]
    exact steps_enter hp (step_block har) []
  have hdK := evDiv_through_steps henter (typedP_ctx' ht1) hdv
  have htB := block_body_typedP har ht
  rcases evDiv_label_seq_split hdK with hdb | ⟨cb, N₁, mm, cs₁, cs₂, rfl, -, hb, hsb, hdc, -⟩
  · exact divOut_lift₀ (fun _ => LogDivXP.block har) (fun _ _ => ReachLXP.block har)
      (ihB s f _ cs htB hdb)
  exfalso
  obtain ⟨l, ⟨s₁, f₁, ob⟩, hd, hres, -⟩ := evRunN_back hT hH hE htB hb hsb hdc
  have hw := resW_of_back hres
  cases ob with
  | tail => exact head_contra hT hH hE ht1 (.blockEsc har hd trivial) hw hdv
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · exact head_contra hT hH hE ht1 (.blockOk har hd hvs .nil) (resW_nil hw) hdv
    · exact head_contra hT hH hE ht1 (.blockBrk har hd) hw hdv
    · exact head_contra hT hH hE ht1 (.blockEsc har hd hesc) hw hdv

/-- **A loop diverging alone**: in its body, or again after an iteration branching back. -/
theorem headDiv_loop (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {body es : List BExpr} (ihB : ∀ m ≤ n, DivG tags o host m body)
    (ihlt : ∀ m < n, DivG tags o host m (.loop bt body :: es))
    (ht : TypedP tags s f stk (.loop bt body :: es)) (hcs : cs ≠ [])
    (hdv : EvDiv (profile o) host n ⟨s, f, xcode stk [.loop bt body]⟩ cs) :
    DivOut s f stk (.loop bt body :: es) cs := by
  have ht1 := typedP_head ht
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨hp, hbe, -⟩ := arity_loop_pre har hc
  obtain ⟨ob₀, hb₀, -⟩ := endsAt_eq hbe
  have hb₀' : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob₀ := by rw [take_length_of_le hp]; exact hb₀
  have hcode : xcode stk [.loop bt body] =
      vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: [] := by
    rw [xcode, code_loop]; rfl
  have hstep : Step (profile o) Det.noHost
      ⟨s, f, vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: []⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label np [.loop bt (Binaryen.BExpr.lowerList body)] (xcode (stk.take np) body)] ++ []⟩ :=
    step_enter hp (step_loop har) []
  have ht0 : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: []⟩ :=
    hcode ▸ typedP_ctx' ht1
  obtain ⟨m₀, hm₀, hdK⟩ := evDiv_unique (fun c₁ h => loop_step_unique har hp h) hstep hcs
    (hcode ▸ hdv)
  have htB := loop_body_typedP har ht
  rcases evDiv_label_seq_split hdK with hdb | ⟨cb, N₁, mm, cs₁, cs₂, rfl, hmm, hb, hsb, hdc, hd₁⟩
  · exact divOut_lift₀ (fun _ => LogDivXP.loop har) (fun _ _ => ReachLXP.loop har)
      (ihB m₀ hm₀.le s f _ _ htB hdb)
  obtain ⟨l, ⟨s₁, f₁, ob⟩, hd, hres, hok⟩ := evRunN_back hT hH hE htB hb hsb hdc
  have hw := resW_of_back hres
  cases ob with
  | tail => exact (head_contra hT hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
    · exact (head_contra hT hH hE ht1 (.loopOk har hd .nil) (resW_nil hw) hdv).elim
    · -- the body branches back to the loop
      have hq : Shape.SubstPre Cl (l.map OCall.lift) cs₁ := by
        rcases hres with h | ⟨h, -⟩
        · exact h
        · cases h
      have hcons₁ := (consistent_append (evDiv_consistent hdv)).1
      obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hcons₁
      obtain ⟨t₁, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
        hev hts
      obtain ⟨hpo, inv, -⟩ := hA hS hb₀'
      obtain ⟨n', hn', hnv⟩ := hpo
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn'
      subst hn'
      rcases hok with ⟨oc, he, hm'⟩ | ⟨h, -⟩
      swap
      · cases h
      rcases matchP_flow_iff.mp hm' with ⟨hs₁, hf₁, hfm⟩ | ⟨h, -⟩
      swap
      · cases h
      obtain ⟨cst, cfr, ccd⟩ := cb
      dsimp only at hs₁ hf₁ he hb hd₁
      subst hs₁ hf₁
      have hex := exit_br0 (P := profile o) (host := NH) (s₁ := cst) (f₁ := cfr)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hfm hnv ((stk.drop np).reverse) []
      have hcont : vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
          expression [.loop bt (Binaryen.BExpr.lowerList body)] ++ [] =
          xcode (vs.take np ++ stk.drop np) [.loop bt body] := by
        rw [xcode, code_loop]; simp [expression]
      rw [hcont] at hex
      have h3 : Steps (profile o) host
          ⟨s, f, vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: []⟩
          ⟨cst, cfr, xcode (vs.take np ++ stk.drop np) [.loop bt body]⟩ :=
        ((Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
          (Steps.ctx _ _ (Steps.label np _ (evRunN_steps hb)))).trans (steps_host hex)
      have htL := ContextTyped.steps_typed hT ht0
        ((Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
          (Steps.ctx _ _ (Steps.label np _ (evRunN_steps hb))))
      have hd₂ := evDiv_append (expression (Binaryen.BExpr.lowerList es))
        (evDiv_through_steps hex htL hd₁)
      have e₂ : ∀ st : List Val, xcode st [.loop bt body] ++
          expression (Binaryen.BExpr.lowerList es) = xcode st (.loop bt body :: es) := by
        intro st; simp [xcode, expression]
      rw [e₂] at hd₂
      have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have e₁ : xcode stk (.loop bt body :: es) ++ rest =
          (vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: []) ++
            (expression (Binaryen.BExpr.lowerList es) ++ rest) := by
        rw [xcode, code_loop]; simp
      have e₃ : xcode (vs.take np ++ stk.drop np) (.loop bt body :: es) ++ rest =
          xcode (vs.take np ++ stk.drop np) [.loop bt body] ++
            (expression (Binaryen.BExpr.lowerList es) ++ rest) := by
        rw [← e₂, List.append_assoc]
      have hall : Steps (profile o) host ⟨s, f, xcode stk (.loop bt body :: es) ++ rest⟩
          ⟨cst, cfr, xcode (vs.take np ++ stk.drop np) (.loop bt body :: es) ++ rest⟩ := by
        rw [e₁, e₃]; exact Steps.append _ h3
      have htk : TypedP tags cst cfr (vs.take np ++ stk.drop np) (.loop bt body :: es) :=
        ⟨rest, labels, ret, out, storeChk_inv inv hS, by rw [hlen]; exact chk_inv inv hc,
          ContextTyped.steps_typed hT hct hall, by rw [inv.2.1]; exact hTM, t₁⟩
      exact divOut_lift (fun _ h => LogDivXP.loopBack har hd h)
        (fun _ _ h => ReachLXP.loopBack har hd h) hq (ihlt mm (by omega) _ _ _ _ htk hd₂)
    · exact (head_contra hT hH hE ht1 (.loopBrk har hd) hw hdv).elim
    · exact (head_contra hT hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim
    · exact (head_contra hT hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim
    · exact (head_contra hT hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
