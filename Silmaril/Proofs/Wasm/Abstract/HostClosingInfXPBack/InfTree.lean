module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.InfGoal

/-!
# Productive runs: operator, block, conditional and handler cases (proofs)

A head tree `e` running productively alone (`CoreInf` of `xcode stk [e]`), for each form of
tree other than a loop. Its parts are split off (`coreInf_split_seq`, `coreInf_split_label`,
`coreInf_handler_seq_split`): a part running productively is the next problem (arguments,
condition, block, arm and handler bodies, `InfG`; a callee at `call`, a resolved
`call_indirect` or a `call_ref`, `CallInfX`, its prefix-free reach a host-free run into a context
around the call); a part run to completion is read back (`evRunN_back_vals`, `evRunN_back`) and
goes on. Every other end of the head tree is a finished logged run of it, ruled out by
`head_contraI`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)
open Shape (streamAppend)

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H}
  {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → Call (wasmHostSig H)}

theorem rtg_of_eq {R : Config H → Config H → Prop} {a b : Config H} (h : a = b) :
    Relation.ReflTransGen R a b := h ▸ .refl

/-- The consistency of a stream's prefix. -/
theorem consistent_of_coreInf {P : Numerics.Profile} {K : Config H}
    {q : List (Call (wasmHostSig H))} {ω' : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host K (q ++ω ω')) : (coreHostRel host).Consistent q := fun c hc => by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have := coreInf_consistent h i
  rwa [Shape.streamAppend_lt hi] at this

/-! ## Operators -/

/-- **An operator running productively alone**: in its arguments, or in the callee of a call. -/
theorem headInf_op (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {i : Instr} {args es : List BExpr} (ihA : InfG tags o host args)
    (ht : TypedP tags s f stk (.op i args :: es))
    (hdv : CoreInf (profile o) host (pcfg s f stk [.op i args]) ω) :
    InfOutX tags o host s f stk (.op i args :: es) ω := by
  have ht1 := typedP_head ht
  have hdv₀ := hdv
  have hcode : xcode stk [.op i args] = xcode stk args ++ [.plain i] := by
    simp [xcode, expression]
  have hX : (pcfg s f stk [.op i args] : Config H) = ⟨s, f, xcode stk args ++ [.plain i]⟩ := by
    simp only [pcfg, hcode]
  rw [hX] at hdv
  rcases coreInf_split_seq hdv with hda | ⟨cs₁, ω₂, ⟨s₁, f₁, k₁⟩, n₁, ws, rfl, hr₁, hw, hd₁⟩
  · exact infOut_lift₀ (fun _ => InfLXP.args) (fun _ _ => ReachLXP.args)
      (link_cons ⟨_, lifts_suffix [.plain i], rtg_of_eq hX⟩)
      (ihA s f stk ω (args_typedP ht) hda)
  dsimp only at hw hd₁
  subst hw
  obtain ⟨l₁, stk₁, hd, hq, rfl⟩ := evRunN_back_vals hT hH hE (args_typedP ht) hr₁
  have hcons := consistent_of_coreInf hdv₀
  obtain ⟨rest₀, hsite, hTF, hTM, hS₁, hts₁, labels, ret, o', hf⟩ :=
    site_factsH hT hH hE ht1 hd hq hcons (evRunN_steps hr₁)
  have htK : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ [.plain i] ++ []⟩ := by
    have h0 := typedP_ctx' ht1
    rw [hcode] at h0
    have := ContextTyped.steps_typed hT h0 (Steps.append [.plain i] (evRunN_steps hr₁))
    simpa using this
  have hd₁' : CoreInf (profile o) host ⟨s₁, f₁, vals stk₁.reverse ++ [.plain i] ++ []⟩ ω₂ := by
    simpa using hd₁
  have hpre : cs₁ = [] → Relation.ReflTransGen (Det.DStep o) (pcfg s f stk [.op i args])
      ⟨s₁, f₁, vals stk₁.reverse ++ [.plain i] ++ []⟩ := by
    rintro rfl
    have := (lifts_suffix (o := o) [.plain i]).rtg (evRunN_nil_dsteps hr₁)
    rw [hX]
    simpa using this
  have reach : ∀ (z : (wasmOShape H).self.Op) (pre : List Val) (cr : Admin),
      cr.IsCallRef → z.2.2 = s₁ → CallChkP tags z.2.2 z.1 z.2.1 →
      Steps (profile o) NH ⟨s₁, f₁, vals stk₁.reverse ++ [.plain i] ++ []⟩
        ⟨s₁, f₁, Interp.callCode pre z.2.1 z.1 cr []⟩ →
      ReachLXP s f stk (.op i args :: es) l₁ z →
      InfOutX tags o host s f stk (.op i args :: es) (cs₁ ++ω ω₂) := by
    rintro ⟨a, us, s'⟩ pre cr hcr rfl hcc hst hr
    refine .inr ⟨l₁, ⟨a, us, s'⟩, cs₁, ⟨s', f₁, Interp.callCode pre us a cr []⟩, ω₂, hr, hq,
      ⟨f₁, pre, cr, hcr, rfl, hcc, htK.steps hst, coreInf_through_dsteps hst hd₁'⟩, rfl,
      fun h0 => link_cons ⟨_, lifts_id, (hpre h0).trans hst⟩⟩
  have contra : ∀ {r : Store H × Frame × POut},
      EvalLXPh s f stk [.op i args] l₁ r → False := fun hd' =>
    head_contraI hH hE ht1 hd' (.inl hq) hdv₀
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
    exact reach ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ _ (.callRefType fi.type) trivial rfl
      ⟨hS₁, hts₁, fi, ps, rs, funcs_of_func? hfi, hty, take_rev_length hp⟩ hst₁
      (.call hd hfi hty)
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
      exact reach ⟨fa, ((stk'.take ps.length).reverse, s₁)⟩ _ (.plain (.callRef y)) trivial rfl
        ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, take_rev_length (by omega)⟩ hst₁
        (.ind hd hres hfi hty hy)
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
    exact reach ⟨fa, ((stk'.take ps.length).reverse, s₁)⟩ _ (.plain (.callRef y)) trivial rfl
      ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, take_rev_length (by omega)⟩ (rtg_of_eq (by rw [e']))
      (.ref hd hfi hty hy)
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

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
