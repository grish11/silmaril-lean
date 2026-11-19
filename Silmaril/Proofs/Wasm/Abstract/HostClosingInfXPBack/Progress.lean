module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Run

/-!
# Typed problems with no closed outcome and no host reach diverge (proofs)

`Interp.evalDivXP_of_noOutcome` (a typed problem with no outcome in `EvalOXP closedCallXP`
diverges, `EvalDivXP`) assumes a store of Wasm functions only (`Interp.WasmFuncsT`): with the
closed host, a host callee has neither an answer nor a divergence. Here the store may hold host
functions; the problem instead **reaches no host call** in the closed semantics (`¬ HReach`):

* `evalDivXP_of_noReach`: a typed problem (`J.TypedP tags`) with no closed outcome that
  reaches no host call diverges;
* `funDivXP_of_noReach`: a typed call (`J.CallTypedP tags`) with no closed answer that
  reaches no host call diverges.

The joint coinduction is that of `Interp.badXP_le`, case by case: typing rules out every way of
getting stuck; a callee with no answer is a Wasm function (a host callee would be a reach,
`HCallReach.host`); the callee function types of `call_indirect`, `call_ref` and
`return_call_indirect`/`return_call_ref` come from typing (`funcType_of_indRes`,
`J.funcType_of_callRef_cfg`, `J.funcType_of_returnCallRef_site`) rather than from the store; and the
absence of a reach passes to every subproblem along the constructors of `HReach`/`HCallReach`,
which are the unfoldings of `DivStepXP`/`CallStepXP`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP
open Silmaril.Wasm.Binaryen (BExpr liftInstrs truthy)

variable {H : Type} {J : Silmaril.Wasm.Interp.BackInv H}

/-- A typed problem that reaches no host call. -/
def GoodR (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) :
    Prop :=
  J.TypedP tags s f stk es ∧ ¬ HReach s f stk es

/-- Such a problem with no closed outcome. -/
def BadR (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) :
    Prop :=
  GoodR J tags s f stk es ∧ ¬ ∃ r, EvalOXP closedCallXP s f stk es r

/-- A typed call that reaches no host call and has no closed answer. -/
def BadCallR (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (s : Store H) (a : Nat) (args : List Val) : Prop :=
  J.CallTypedP tags s a args ∧ ¬ HCallReach s a args ∧ ¬ ∃ out, closedCallXP s a args out

section Cases

variable {tags : List TagInst}

theorem goodR_split {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (hg : GoodR J tags s f stk es) : BadR J tags s f stk es ∨ ∃ r, EvalOXP closedCallXP s f stk es r := by
  by_cases h : ∃ r, EvalOXP closedCallXP s f stk es r
  · exact .inr h
  · exact .inl ⟨hg, h⟩

theorem goodR_cont {e : BExpr} {es : List BExpr} {s s₂ : Store H} {f f₂ : Frame}
    {stk stk₂ : List Val} (d : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂)))
    (hg : GoodR J tags s f stk (e :: es)) : GoodR J tags s₂ f₂ stk₂ es :=
  ⟨J.cont_typedP d hg.1, fun h => hg.2 (.cont d h)⟩

/-- A typed call that reaches no host call has no answer, or answers by returning, trapping or
throwing. -/
theorem callee_splitR {s₁ : Store H} {a : Nat} {us : List Val} (hct : J.CallTypedP tags s₁ a us)
    (hnr : ¬ HCallReach s₁ a us) :
    BadCallR J tags s₁ a us ∨ ∃ (s₂ : Store H) (fl : Binaryen.Flow), closedCallXP s₁ a us (s₂, fl) ∧
      ((∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) := by
  by_cases h : ∃ out, closedCallXP s₁ a us out
  · obtain ⟨⟨s₂, fl⟩, hcall⟩ := h
    exact .inr ⟨s₂, fl, hcall, calleeP_flow hct.1 hcall⟩
  · exact .inl ⟨hct, hnr, h⟩

/-- A check of `call_indirect` names a type of the instance with an arity. -/
theorem typeArity_some_ci {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TableIdx} {y : TypeIdx} {o : Option Nat}
    (hc : flatChkE tExt F mi nl ret labels h (.callIndirect x y) = some o) :
    ∃ p, typeArity mi y = some p := by
  cases hta : typeArity mi y with
  | none => simp [flatChkE, tExt, hta, extStep] at hc
  | some p => exact ⟨p, rfl⟩

/-- A check of `return_call_indirect` names a type of the instance with an arity. -/
theorem typeArity_some_rci' {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TableIdx} {y : TypeIdx} {o : Option Nat}
    (hc : flatChkE tExt F mi nl ret labels h (.returnCallIndirect x y) = some o) :
    ∃ p, typeArity mi y = some p := by
  cases hta : typeArity mi y with
  | none => simp [flatChkE, tExt, hta, extStep] at hc
  | some p => exact ⟨p, rfl⟩

end Cases

section Op

variable {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}

/-- **Operators.** -/
theorem badR_op {i : Instr} {args : List BExpr} (hbad : BadR J tags s f stk (.op i args :: es)) :
    DivStepXP (BadR J tags) (BadCallR J tags) s f stk (.op i args :: es) := by
  obtain ⟨⟨ht, hnr⟩, hne⟩ := hbad
  have hta := J.args_typedP ht
  rcases goodR_split ⟨hta, fun h => hnr (.args h)⟩ with hb | ⟨⟨s₁, f₁, o⟩, hargs⟩
  · exact .args hb
  by_cases hn : o.IsNormal
  swap
  · exact absurd ⟨_, .argsAbort hargs hn⟩ hne
  obtain ⟨stk₁, rfl⟩ := POut.normal_of hn
  obtain ⟨rest₀, hsite, hTF, hTM, hS₁, hts₁, labels, ret, o, hf⟩ := J.site_typedP hargs ht
  have hg : GoodR J tags s f stk (.op i args :: es) := ⟨ht, hnr⟩
  rcases instr_cases i with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ |
    (⟨x, rfl⟩ | rfl) | ⟨hi, hx⟩
  · -- call
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    obtain ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩ := callArity_func? hpq
    have hct := J.callTyped_call hsite hfi hty hp hS₁ hts₁
    rcases callee_splitR hct (fun h => hnr (.callee hargs hfi hty h)) with
      hb | ⟨s₂, fl, hcall, hfl⟩
    · exact .callee hargs hfi hty hb
    rcases hfl with ⟨vs, hvs⟩ | hab
    · rcases goodR_split (goodR_cont (.callOk hargs hfi hty hcall hvs .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.callOk hargs hfi hty hcall hvs .nil) hb
      · exact absurd ⟨r, .callOk hargs hfi hty hcall hvs hk⟩ hne
    · cases fl with
      | trap => exact absurd ⟨_, .callTrap hargs hfi hty hcall⟩ hne
      | throw t => exact absurd ⟨_, .callThrow hargs hfi hty hcall⟩ hne
      | _ => exact absurd hab id
  · -- call_indirect
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := J.indirect_res (.inl rfl) hsite
    cases o' with
    | none => exact absurd ⟨_, .callIndRes hargs hres⟩ hne
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
      obtain ⟨p₀, hy₀⟩ := typeArity_some_ci hf
      obtain ⟨ps, rs, hty⟩ := Silmaril.Wasm.Abstract.funcType_of_indRes hres hfi hTF hTM hy₀
      have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
      obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf
      simp only [List.length_cons] at hp
      have hct := J.callTyped_ind hsite hres hfi hty (by omega) hS₁ hts₁
      rcases callee_splitR hct (fun h => hnr (.callIndCallee hargs hres hfi hty hy h)) with
        hb | ⟨s₂, fl, hcall, hfl⟩
      · exact .callIndCallee hargs hres hfi hty hy hb
      rcases hfl with ⟨vs, hvs⟩ | hab
      · rcases goodR_split (goodR_cont (.callIndOk hargs hres hfi hty hy hcall hvs .nil) hg) with
          hb | ⟨r, hk⟩
        · exact .cont (.callIndOk hargs hres hfi hty hy hcall hvs .nil) hb
        · exact absurd ⟨r, .callIndOk hargs hres hfi hty hy hcall hvs hk⟩ hne
      · exact absurd ⟨_, .callIndStop hargs hres hfi hty hy hcall hab⟩ hne
  · -- call_ref
    obtain ⟨r, stk', rfl, hr⟩ := J.callRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact absurd ⟨_, .callRefNull hargs⟩ hne
    have e : vals (Val.ref (.func fa) :: stk').reverse ++ .plain (.callRef y) :: rest₀ =
        vals stk'.reverse ++ .ref (.func fa) :: .plain (.callRef y) :: rest₀ := by
      simp [vals, Val.toAdmin]
    obtain ⟨ps, rs, hty⟩ := J.funcType_of_callRef_cfg
      (P := SingleThreaded.profile (fun _ _ _ _ => false)) (e ▸ hsite) (cr := .plain (.callRef y))
      trivial hfi
    have hy := J.typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf
    simp only [List.length_cons] at hp
    have hct := J.callTyped_ref hsite hfi hty (by omega) hS₁ hts₁
    rcases callee_splitR hct (fun h => hnr (.callRefCallee hargs hfi hty hy h)) with
      hb | ⟨s₂, fl, hcall, hfl⟩
    · exact .callRefCallee hargs hfi hty hy hb
    rcases hfl with ⟨vs, hvs⟩ | hab
    · rcases goodR_split (goodR_cont (.callRefOk hargs hfi hty hy hcall hvs .nil) hg) with
        hb | ⟨r, hk⟩
      · exact .cont (.callRefOk hargs hfi hty hy hcall hvs .nil) hb
      · exact absurd ⟨r, .callRefOk hargs hfi hty hy hcall hvs hk⟩ hne
    · exact absurd ⟨_, .callRefStop hargs hfi hty hy hcall hab⟩ hne
  · -- return_call: a pending tail call, an outcome
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
    have hca : ∃ p, callArity s₁.funcs f₁.module x = some p := by
      cases h : callArity s₁.funcs f₁.module x with
      | none => simp [flatChkE, tExt, h, extStep] at hf
      | some p => exact ⟨p, rfl⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := hca
    obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := callArity_func? hpq
    exact absurd ⟨_, .tail hargs (.direct hfi) (funcs_of_func? hfi) hty
      (J.tailAnn_typed (.direct hfi) hsite (funcs_of_func? hfi) hty hTF hTM hf)⟩ hne
  · -- return_call_indirect
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := J.indirect_res (.inr rfl) hsite
    cases o' with
    | none => exact absurd ⟨_, .tailRes hargs (.indirectTrap hres)⟩ hne
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
      obtain ⟨p₀, hy₀⟩ := typeArity_some_rci' hf
      obtain ⟨ps, rs, hty⟩ := Silmaril.Wasm.Abstract.funcType_of_indRes hres hfi hTF hTM hy₀
      exact absurd ⟨_, .tail hargs (.indirect hres) hfi hty
        (J.tailAnn_typed (.indirect hres) hsite hfi hty hTF hTM hf)⟩ hne
  · -- return_call_ref
    obtain ⟨r, stk', rfl, hr⟩ := J.returnCallRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact absurd ⟨_, .tailRes hargs .refNull⟩ hne
    · obtain ⟨ps, rs, hty⟩ :=
        J.funcType_of_returnCallRef_site hsite hTM hfi (hTF _ _ hfi)
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
      exact absurd ⟨_, .tail hargs .ref hfi hty (J.tailAnn_typed .ref hsite hfi hty hTF hTM hf)⟩ hne
  · -- throw x: the tag exists, with its fields on the stack
    obtain ⟨p, htf, hp⟩ := throw_chk hf
    obtain ⟨ta, ti, ts, ht', he, hlen⟩ := tag_of_tagFields hts₁.1 htf
    exact absurd ⟨_, .throw hargs ht' he (by omega)⟩ hne
  · -- throw_ref: a null or an exception reference
    obtain ⟨r, stk', rfl, hr⟩ := J.throwRef_top hsite
    rcases hr with rfl | ⟨a, rfl⟩
    · exact absurd ⟨_, .throwRefNull hargs⟩ hne
    · exact absurd ⟨_, .throwRefExn hargs⟩ hne
  · -- a flat instruction
    have hf' : flatChk s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
      rw [← flatChkE_eq_flatChk (ehExt tags) hx]; exact hf
    obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := J.evalFlat_progress hf' hi hsite
    by_cases hn₂ : fl₂.IsNormal
    swap
    · exact absurd ⟨_, .opStop hi hargs hflat hn₂⟩ hne
    rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn₂
    rcases goodR_split (goodR_cont (.opOk hi hargs hflat .nil) hg) with hb | ⟨r, hk⟩
    · exact .cont (.opOk hi hargs hflat .nil) hb
    · exact absurd ⟨r, .opOk hi hargs hflat hk⟩ hne

end Op

section Ctl

variable {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}

/-- **Blocks.** -/
theorem badR_block {bt : BlockType} {body : List BExpr}
    (hbad : BadR J tags s f stk (.block bt body :: es)) :
    DivStepXP (BadR J tags) (BadCallR J tags) s f stk (.block bt body :: es) := by
  obtain ⟨⟨ht, hnr⟩, hne⟩ := hbad
  have hg : GoodR J tags s f stk (.block bt body :: es) := ⟨ht, hnr⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodR_split ⟨J.block_body_typedP har ht, fun h => hnr (.block har h)⟩ with
    hb | ⟨⟨s₁, f₁, o⟩, hbody⟩
  · exact .block har hb
  cases o with
  | tail => exact absurd ⟨_, .blockEsc har hbody trivial⟩ hne
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · rcases goodR_split (goodR_cont (.blockOk har hbody hvs .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.blockOk har hbody hvs .nil) hb
      · exact absurd ⟨r, .blockOk har hbody hvs hk⟩ hne
    · exact absurd ⟨_, .blockBrk har hbody⟩ hne
    · exact absurd ⟨_, .blockEsc har hbody hesc⟩ hne

/-- **Loops.** -/
theorem badR_loop {bt : BlockType} {body : List BExpr}
    (hbad : BadR J tags s f stk (.loop bt body :: es)) :
    DivStepXP (BadR J tags) (BadCallR J tags) s f stk (.loop bt body :: es) := by
  obtain ⟨⟨ht, hnr⟩, hne⟩ := hbad
  have hg : GoodR J tags s f stk (.loop bt body :: es) := ⟨ht, hnr⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodR_split ⟨J.loop_body_typedP har ht, fun h => hnr (.loop har h)⟩ with
    hb | ⟨⟨s₁, f₁, o⟩, hbody⟩
  · exact .loop har hb
  cases o with
  | tail => exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
    · rcases goodR_split (goodR_cont (.loopOk har hbody .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.loopOk har hbody .nil) hb
      · exact absurd ⟨r, .loopOk har hbody hk⟩ hne
    · have hgb : GoodR J tags s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) :=
        ⟨J.loop_back_typedP har hbody ht, fun h => hnr (.loopBack har hbody h)⟩
      rcases goodR_split hgb with hb | ⟨r, hk⟩
      · exact .loopBack har hbody hb
      · exact absurd ⟨r, .loopBack har hbody hk⟩ hne
    · exact absurd ⟨_, .loopBrk har hbody⟩ hne
    · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
    · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
    · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne

/-- **Conditionals.** -/
theorem badR_if {bt : BlockType} {c t el : List BExpr}
    (hbad : BadR J tags s f stk (.if_ bt c t el :: es)) :
    DivStepXP (BadR J tags) (BadCallR J tags) s f stk (.if_ bt c t el :: es) := by
  obtain ⟨⟨ht, hnr⟩, hne⟩ := hbad
  have hg : GoodR J tags s f stk (.if_ bt c t el :: es) := ⟨ht, hnr⟩
  have htc := J.cond_typedP ht
  rcases goodR_split ⟨htc, fun h => hnr (.cond h)⟩ with hb | ⟨⟨s₁, f₁, o⟩, hcond⟩
  · exact .cond hb
  by_cases hn : o.IsNormal
  swap
  · exact absurd ⟨_, .ifAbort hcond hn⟩ hne
  obtain ⟨stk₁', rfl⟩ := POut.normal_of hn
  obtain ⟨rest, labels, ret, out, hS, hc, hct, -, hts⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  rw [code_if] at hct
  have hct' : J.CT ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c) ++
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨hct₁, ho, inv1, -⟩ := J.prefix_typedP hcond hS hco hct' hts
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := J.truthy_progress (by simpa only [List.cons_append] using hct₁)
  obtain ⟨np, nr, ha, -, -, -, -⟩ := hk1 _ ho
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [arity_eq, inv1.2.1]
    exact ha
  rcases goodR_split ⟨J.arm_typedP hcond hb har ht, fun h => hnr (.arm hcond hb har h)⟩ with
    hba | ⟨⟨s₂, f₂, o⟩, harm⟩
  · exact .arm hcond hb har hba
  cases o with
  | tail => exact absurd ⟨_, .ifEsc hcond hb har harm trivial⟩ hne
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · rcases goodR_split (goodR_cont (.ifOk hcond hb har harm hvs .nil) hg) with hbk | ⟨r, hk⟩
      · exact .cont (.ifOk hcond hb har harm hvs .nil) hbk
      · exact absurd ⟨r, .ifOk hcond hb har harm hvs hk⟩ hne
    · exact absurd ⟨_, .ifBrk hcond hb har harm⟩ hne
    · exact absurd ⟨_, .ifEsc hcond hb har harm hesc⟩ hne

/-- **`try_table`**: a thrown exception is always resolved by the clauses (`catches_total`). -/
theorem badR_try {bt : BlockType} {cs : List Catch} {body : List BExpr}
    (hbad : BadR J tags s f stk (.tryTable bt cs body :: es)) :
    DivStepXP (BadR J tags) (BadCallR J tags) s f stk (.tryTable bt cs body :: es) := by
  obtain ⟨⟨ht, hnr⟩, hne⟩ := hbad
  have hg : GoodR J tags s f stk (.tryTable bt cs body :: es) := ⟨ht, hnr⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨ns, np, nr, -, ha, -, -, -, -⟩ := chk1_tryTableE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodR_split ⟨J.try_body_typedP har ht, fun h => hnr (.try_ har h)⟩ with
    hb | ⟨⟨s₁, f₁, o⟩, hbody⟩
  · exact .try_ har hb
  cases o with
  | tail => exact absurd ⟨_, .tryEsc har hbody trivial trivial⟩ hne
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | a
    · rcases goodR_split (goodR_cont (.tryOk har hbody rfl .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.tryOk har hbody rfl .nil) hb
      · exact absurd ⟨r, .tryOk har hbody rfl hk⟩ hne
    · rcases goodR_split (goodR_cont (.tryOk har hbody rfl .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.tryOk har hbody rfl .nil) hb
      · exact absurd ⟨r, .tryOk har hbody rfl hk⟩ hne
    · exact absurd ⟨_, .tryBrk har hbody⟩ hne
    · exact absurd ⟨_, .tryEsc har hbody trivial trivial⟩ hne
    · exact absurd ⟨_, .tryEsc har hbody trivial trivial⟩ hne
    · obtain ⟨r, hr⟩ := Cfg.Region.catches_total s₁ f₁ a cs
      cases r with
      | none => exact absurd ⟨_, .tryRethrow har hbody hr⟩ hne
      | some p => exact absurd ⟨_, .tryCatch (us := p.1) (l := p.2) har hbody hr⟩ hne

/-- **One unfolding of a problem.** -/
theorem badR_step (hbad : BadR J tags s f stk es) :
    DivStepXP (BadR J tags) (BadCallR J tags) s f stk es := by
  rcases es with _ | ⟨e, es⟩
  · exact absurd ⟨_, .nil⟩ hbad.2
  · cases e with
    | op i args => exact badR_op hbad
    | block bt body => exact badR_block hbad
    | loop bt body => exact badR_loop hbad
    | if_ bt c t el => exact badR_if hbad
    | tryTable bt cs body => exact badR_try hbad

end Ctl

/-- **One unfolding of a call**: a typed call with no answer and no host reach is a call of a Wasm
function whose body has no outcome, or ends in a pending tail call whose own call has neither. -/
theorem badCallR_step {tags : List TagInst} {s : Store H} {a : Nat} {args : List Val}
    (hb : BadCallR J tags s a args) : CallStepXP (BadR J tags) (BadCallR J tags) s a args := by
  obtain ⟨hct, hnr, hne⟩ := hb
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, -⟩, -⟩ := id hct
  cases hcode : fi.code with
  | host hh => exact absurd (.host hfi hcode) hnr
  | wasm fn =>
  have htb := J.callee_typedP hct hfi hcode
  by_cases hex : ∃ r, EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
      (liftInstrs fn.body) r
  swap
  · exact .body hfi hcode ⟨⟨htb, fun h => hnr (.body hfi hcode h)⟩, hex⟩
  obtain ⟨⟨s₁, f₂, o⟩, d⟩ := hex
  cases o with
  | flow fl => exact absurd ⟨_, closedCallXP_of_body hfi hcode hty d .flow⟩ hne
  | tail a' args' n =>
    have hct' := J.callTyped_tail hct hfi hcode d
    rcases callee_splitR hct' (fun h => hnr (.frameTail hfi hcode d h)) with
      hb' | ⟨s₂, fl, hcall, hfl⟩
    · exact .frameTail hfi hcode d hb'
    · exact absurd ⟨_, closedCallXP_of_body hfi hcode hty d (.tail hcall hfl)⟩ hne

/-- **Bad problems and calls diverge.** -/
theorem badR_le {tags : List TagInst} :
    (BadR J tags : Interp.Problem H) ≤ EvalDivXP ∧ (BadCallR J tags : CallProblem H) ≤ FunDivXP :=
  evalDivXP_of_coind (fun _ _ _ _ h => badR_step h) (fun _ _ _ h => badCallR_step h)

/-- **No closed outcome and no host reach means divergence**, for typed problems. -/
theorem evalDivXP_of_noReach {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (ht : J.TypedP tags s f stk es) (hnr : ¬ HReach s f stk es)
    (hne : ¬ ∃ r, EvalOXP closedCallXP s f stk es r) : EvalDivXP s f stk es :=
  badR_le.1 s f stk es ⟨⟨ht, hnr⟩, hne⟩

/-- **No closed answer and no host reach means divergence**, for typed calls. -/
theorem funDivXP_of_noReach {tags : List TagInst} {s : Store H} {a : Nat} {args : List Val}
    (ht : J.CallTypedP tags s a args) (hnr : ¬ HCallReach s a args)
    (hne : ¬ ∃ out, closedCallXP s a args out) : FunDivXP s a args :=
  badR_le.2 s a args ⟨ht, hnr, hne⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
