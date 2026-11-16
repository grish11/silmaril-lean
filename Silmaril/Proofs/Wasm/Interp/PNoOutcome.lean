module

public import Silmaril.Proofs.Wasm.Interp.PTyped
public import Silmaril.Wasm.Cfg.Region.Thms

/-!
# Typed problems with no closed outcome diverge, with exceptions and pending tail calls (proofs)

The analog of `XNoOutcome.evalDivX_of_noOutcome` for `CallXP.EvalOXP closedCallXP`: a typed
problem (`TypedP tags`) in a store of Wasm functions with function types (`WasmFuncsT`) that has
no outcome diverges coinductively (`evalDivXP_of_noOutcome`), and a typed call (`CallTypedP`)
with no closed answer diverges (`funDivXP_of_noAnswer`).

By joint coinduction (`badXP_step`, `badCallP_step`): typing rules out every way of getting
stuck — flat instructions (`evalFlat_progressH`), conditions (`truthy_progressH`), the operands
of reference calls (`callRef_top`, `returnCallRef_top`) and of `throw_ref` (`throwRef_top`),
indirect resolution (`indirect_res`), the tag of a `throw` (`tag_of_tagFields`, from the check and
the tag invariants), the typed callee arities of the indirect, reference and tail forms
(`typeArity_of_indRes`, `typeArity_of_callRef_site`, `tailAnn_typed`), and a `try_table`'s
resolution of a thrown exception (total: `Cfg.Region.catches_total`). A call with no answer
either has a body with no outcome, or a body ending in a pending tail call whose own call has
no answer (a checked callee's answer returns, traps or throws, `calleeP_flow`, so the frame can
always be left once the tail callee answers).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP

variable {H : Type}

/-- A typed problem in a store of Wasm functions. -/
def GoodXP (tags : List TagInst) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) : Prop :=
  TypedP tags s f stk es ∧ WasmFuncsT s

/-- A good problem with no closed outcome. -/
def BadXP (tags : List TagInst) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) : Prop :=
  GoodXP tags s f stk es ∧ ¬ ∃ r, EvalOXP closedCallXP s f stk es r

/-- A typed call in a store of Wasm functions with no closed answer. -/
def BadCallP (tags : List TagInst) (s : Store H) (a : Nat) (args : List Val) : Prop :=
  CallTypedP tags s a args ∧ WasmFuncsT s ∧ ¬ ∃ out, closedCallXP s a args out

section Cases

variable {tags : List TagInst}

theorem goodXP_split {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    (hg : GoodXP tags s f stk es) : BadXP tags s f stk es ∨ ∃ r, EvalOXP closedCallXP s f stk es r := by
  by_cases h : ∃ r, EvalOXP closedCallXP s f stk es r
  · exact .inr h
  · exact .inl ⟨hg, h⟩

theorem goodXP_cont {e : Binaryen.BExpr} {es : List Binaryen.BExpr} {s s₂ : Store H}
    {f f₂ : Frame} {stk stk₂ : List Val}
    (d : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂)))
    (hg : GoodXP tags s f stk (e :: es)) : GoodXP tags s₂ f₂ stk₂ es :=
  ⟨cont_typedP d hg.1, wasmFuncsT_runP d hg.2⟩

/-- A typed call either has no answer, or answers by returning, trapping or throwing. -/
theorem callee_splitP {s₁ : Store H} {a : Nat} {us : List Val} (hct : CallTypedP tags s₁ a us)
    (hW : WasmFuncsT s₁) :
    BadCallP tags s₁ a us ∨ ∃ (s₂ : Store H) (fl : Binaryen.Flow), closedCallXP s₁ a us (s₂, fl) ∧
      ((∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) := by
  by_cases h : ∃ out, closedCallXP s₁ a us out
  · obtain ⟨⟨s₂, fl⟩, hcall⟩ := h
    exact .inr ⟨s₂, fl, hcall, calleeP_flow hct.1 hcall⟩
  · exact .inl ⟨hct, hW, h⟩

theorem POut.normal_of {o : POut} (h : o.IsNormal) : ∃ stk, o = .flow (.normal stk) := by
  cases o with
  | flow fl =>
    cases fl with
    | normal stk => exact ⟨stk, rfl⟩
    | _ => exact False.elim h
  | tail => exact False.elim h

end Cases

section Op

variable {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

/-- **Operators.** -/
theorem badXP_op {i : Instr} {args : List Binaryen.BExpr}
    (hbad : BadXP tags s f stk (.op i args :: es)) :
    DivStepXP (BadXP tags) (BadCallP tags) s f stk (.op i args :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hta := args_typedP ht
  rcases goodXP_split ⟨hta, hW⟩ with hb | ⟨⟨s₁, f₁, o⟩, hargs⟩
  · exact .args hb
  by_cases hn : o.IsNormal
  swap
  · exact absurd ⟨_, .argsAbort hargs hn⟩ hne
  obtain ⟨stk₁, rfl⟩ := POut.normal_of hn
  obtain ⟨rest₀, hsite, hTF, hTM, hS₁, hts₁, labels, ret, o, hf⟩ := site_typedP hargs ht
  have hW₁ : WasmFuncsT s₁ := wasmFuncsT_runP hargs hW
  have hg : GoodXP tags s f stk (.op i args :: es) := ⟨ht, hW⟩
  rcases instr_cases i with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ |
    (⟨x, rfl⟩ | rfl) | ⟨hi, hx⟩
  · -- call
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    obtain ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩ := callArity_func? hpq
    have hct := callTyped_call hsite hfi hty hp hS₁ hts₁
    rcases callee_splitP hct hW₁ with hb | ⟨s₂, fl, hcall, hfl⟩
    · exact .callee hargs hfi hty hb
    rcases hfl with ⟨vs, hvs⟩ | hab
    · rcases goodXP_split (goodXP_cont (.callOk hargs hfi hty hcall hvs .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.callOk hargs hfi hty hcall hvs .nil) hb
      · exact absurd ⟨r, .callOk hargs hfi hty hcall hvs hk⟩ hne
    · cases fl with
      | trap => exact absurd ⟨_, .callTrap hargs hfi hty hcall⟩ hne
      | throw t => exact absurd ⟨_, .callThrow hargs hfi hty hcall⟩ hne
      | _ => exact absurd hab id
  · -- call_indirect
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := indirect_res (.inl rfl) hsite
    cases o' with
    | none => exact absurd ⟨_, .callIndRes hargs hres⟩ hne
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      obtain ⟨fn, ps, rs, hcode, hty⟩ := hW₁ fa fi hfi
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
      have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
      obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf
      simp only [List.length_cons] at hp
      have hct := callTyped_ind hsite hres hfi hty (by omega) hS₁ hts₁
      rcases callee_splitP hct hW₁ with hb | ⟨s₂, fl, hcall, hfl⟩
      · exact .callIndCallee hargs hres hfi hty hy hb
      rcases hfl with ⟨vs, hvs⟩ | hab
      · rcases goodXP_split (goodXP_cont (.callIndOk hargs hres hfi hty hy hcall hvs .nil) hg) with
          hb | ⟨r, hk⟩
        · exact .cont (.callIndOk hargs hres hfi hty hy hcall hvs .nil) hb
        · exact absurd ⟨r, .callIndOk hargs hres hfi hty hy hcall hvs hk⟩ hne
      · exact absurd ⟨_, .callIndStop hargs hres hfi hty hy hcall hab⟩ hne
  · -- call_ref
    obtain ⟨r, stk', rfl, hr⟩ := callRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact absurd ⟨_, .callRefNull hargs⟩ hne
    obtain ⟨fn, ps, rs, hcode, hty⟩ := hW₁ fa fi hfi
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf
    simp only [List.length_cons] at hp
    have hct := callTyped_ref hsite hfi hty (by omega) hS₁ hts₁
    rcases callee_splitP hct hW₁ with hb | ⟨s₂, fl, hcall, hfl⟩
    · exact .callRefCallee hargs hfi hty hy hb
    rcases hfl with ⟨vs, hvs⟩ | hab
    · rcases goodXP_split (goodXP_cont (.callRefOk hargs hfi hty hy hcall hvs .nil) hg) with
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
      (tailAnn_typed (.direct hfi) hsite (funcs_of_func? hfi) hty hTF hTM hf)⟩ hne
  · -- return_call_indirect
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := indirect_res (.inr rfl) hsite
    cases o' with
    | none => exact absurd ⟨_, .tailRes hargs (.indirectTrap hres)⟩ hne
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      obtain ⟨fn, ps, rs, hcode, hty⟩ := hW₁ fa fi hfi
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
      exact absurd ⟨_, .tail hargs (.indirect hres) hfi hty
        (tailAnn_typed (.indirect hres) hsite hfi hty hTF hTM hf)⟩ hne
  · -- return_call_ref
    obtain ⟨r, stk', rfl, hr⟩ := returnCallRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact absurd ⟨_, .tailRes hargs .refNull⟩ hne
    · obtain ⟨fn, ps, rs, hcode, hty⟩ := hW₁ fa fi hfi
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
      exact absurd ⟨_, .tail hargs .ref hfi hty (tailAnn_typed .ref hsite hfi hty hTF hTM hf)⟩ hne
  · -- throw x: the tag exists, with its fields on the stack
    obtain ⟨p, htf, hp⟩ := throw_chk hf
    obtain ⟨ta, ti, ts, ht', he, hlen⟩ := tag_of_tagFields hts₁.1 htf
    exact absurd ⟨_, .throw hargs ht' he (by omega)⟩ hne
  · -- throw_ref: a null or an exception reference
    obtain ⟨r, stk', rfl, hr⟩ := throwRef_top hsite
    rcases hr with rfl | ⟨a, rfl⟩
    · exact absurd ⟨_, .throwRefNull hargs⟩ hne
    · exact absurd ⟨_, .throwRefExn hargs⟩ hne
  · -- a flat instruction
    have hf' : flatChk s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
      rw [← flatChkE_eq_flatChk (ehExt tags) hx]; exact hf
    obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := evalFlat_progressH hf' hi hsite
    by_cases hn₂ : fl₂.IsNormal
    swap
    · exact absurd ⟨_, .opStop hi hargs hflat hn₂⟩ hne
    rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn₂
    rcases goodXP_split (goodXP_cont (.opOk hi hargs hflat .nil) hg) with hb | ⟨r, hk⟩
    · exact .cont (.opOk hi hargs hflat .nil) hb
    · exact absurd ⟨r, .opOk hi hargs hflat hk⟩ hne

end Op

section Ctl

variable {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

/-- **Blocks.** -/
theorem badXP_block {bt : BlockType} {body : List Binaryen.BExpr}
    (hbad : BadXP tags s f stk (.block bt body :: es)) :
    DivStepXP (BadXP tags) (BadCallP tags) s f stk (.block bt body :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodXP tags s f stk (.block bt body :: es) := ⟨ht, hW⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodXP_split ⟨block_body_typedP har ht, hW⟩ with hb | ⟨⟨s₁, f₁, o⟩, hbody⟩
  · exact .block har hb
  cases o with
  | tail => exact absurd ⟨_, .blockEsc har hbody trivial⟩ hne
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · rcases goodXP_split (goodXP_cont (.blockOk har hbody hvs .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.blockOk har hbody hvs .nil) hb
      · exact absurd ⟨r, .blockOk har hbody hvs hk⟩ hne
    · exact absurd ⟨_, .blockBrk har hbody⟩ hne
    · exact absurd ⟨_, .blockEsc har hbody hesc⟩ hne

/-- **Loops.** -/
theorem badXP_loop {bt : BlockType} {body : List Binaryen.BExpr}
    (hbad : BadXP tags s f stk (.loop bt body :: es)) :
    DivStepXP (BadXP tags) (BadCallP tags) s f stk (.loop bt body :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodXP tags s f stk (.loop bt body :: es) := ⟨ht, hW⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodXP_split ⟨loop_body_typedP har ht, hW⟩ with hb | ⟨⟨s₁, f₁, o⟩, hbody⟩
  · exact .loop har hb
  cases o with
  | tail => exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
    · rcases goodXP_split (goodXP_cont (.loopOk har hbody .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.loopOk har hbody .nil) hb
      · exact absurd ⟨r, .loopOk har hbody hk⟩ hne
    · have hgb : GoodXP tags s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) :=
        ⟨loop_back_typedP har hbody ht, wasmFuncsT_runP hbody hW⟩
      rcases goodXP_split hgb with hb | ⟨r, hk⟩
      · exact .loopBack har hbody hb
      · exact absurd ⟨r, .loopBack har hbody hk⟩ hne
    · exact absurd ⟨_, .loopBrk har hbody⟩ hne
    · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
    · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
    · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne

/-- **Conditionals.** -/
theorem badXP_if {bt : BlockType} {c t el : List Binaryen.BExpr}
    (hbad : BadXP tags s f stk (.if_ bt c t el :: es)) :
    DivStepXP (BadXP tags) (BadCallP tags) s f stk (.if_ bt c t el :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodXP tags s f stk (.if_ bt c t el :: es) := ⟨ht, hW⟩
  have htc := cond_typedP ht
  rcases goodXP_split ⟨htc, hW⟩ with hb | ⟨⟨s₁, f₁, o⟩, hcond⟩
  · exact .cond hb
  by_cases hn : o.IsNormal
  swap
  · exact absurd ⟨_, .ifAbort hcond hn⟩ hne
  obtain ⟨stk₁', rfl⟩ := POut.normal_of hn
  obtain ⟨rest, labels, ret, out, hS, hc, hct, -, hts⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  rw [code_if] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c) ++
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨hct₁, ho, inv1, -⟩ := prefix_typedP hcond hS hco hct' hts
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := truthy_progressH (by simpa only [List.cons_append] using hct₁)
  obtain ⟨np, nr, ha, -, -, -, -⟩ := hk1 _ ho
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [arity_eq, inv1.2.1]
    exact ha
  rcases goodXP_split ⟨arm_typedP hcond hb har ht, wasmFuncsT_runP hcond hW⟩ with
    hba | ⟨⟨s₂, f₂, o⟩, harm⟩
  · exact .arm hcond hb har hba
  cases o with
  | tail => exact absurd ⟨_, .ifEsc hcond hb har harm trivial⟩ hne
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · rcases goodXP_split (goodXP_cont (.ifOk hcond hb har harm hvs .nil) hg) with hbk | ⟨r, hk⟩
      · exact .cont (.ifOk hcond hb har harm hvs .nil) hbk
      · exact absurd ⟨r, .ifOk hcond hb har harm hvs hk⟩ hne
    · exact absurd ⟨_, .ifBrk hcond hb har harm⟩ hne
    · exact absurd ⟨_, .ifEsc hcond hb har harm hesc⟩ hne

/-- **`try_table`**: a thrown exception is always resolved by the clauses (`catches_total`). -/
theorem badXP_try {bt : BlockType} {cs : List Catch} {body : List Binaryen.BExpr}
    (hbad : BadXP tags s f stk (.tryTable bt cs body :: es)) :
    DivStepXP (BadXP tags) (BadCallP tags) s f stk (.tryTable bt cs body :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodXP tags s f stk (.tryTable bt cs body :: es) := ⟨ht, hW⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨ns, np, nr, -, ha, -, -, -, -⟩ := chk1_tryTableE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodXP_split ⟨try_body_typedP har ht, hW⟩ with hb | ⟨⟨s₁, f₁, o⟩, hbody⟩
  · exact .try_ har hb
  cases o with
  | tail => exact absurd ⟨_, .tryEsc har hbody trivial trivial⟩ hne
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | a
    · rcases goodXP_split (goodXP_cont (.tryOk har hbody rfl .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.tryOk har hbody rfl .nil) hb
      · exact absurd ⟨r, .tryOk har hbody rfl hk⟩ hne
    · rcases goodXP_split (goodXP_cont (.tryOk har hbody rfl .nil) hg) with hb | ⟨r, hk⟩
      · exact .cont (.tryOk har hbody rfl .nil) hb
      · exact absurd ⟨r, .tryOk har hbody rfl hk⟩ hne
    · exact absurd ⟨_, .tryBrk har hbody⟩ hne
    · exact absurd ⟨_, .tryEsc har hbody trivial trivial⟩ hne
    · exact absurd ⟨_, .tryEsc har hbody trivial trivial⟩ hne
    · obtain ⟨r, hr⟩ := Cfg.Region.catches_total s₁ f₁ a cs
      cases r with
      | none => exact absurd ⟨_, .tryRethrow har hbody hr⟩ hne
      | some p => exact absurd ⟨_, .tryCatch (us := p.1) (l := p.2) har hbody hr⟩ hne

/-- **One unfolding of a problem**: a good problem without a closed outcome takes a divergence
step into such problems and calls. -/
theorem badXP_step (hbad : BadXP tags s f stk es) :
    DivStepXP (BadXP tags) (BadCallP tags) s f stk es := by
  rcases es with _ | ⟨e, es⟩
  · exact absurd ⟨_, .nil⟩ hbad.2
  · cases e with
    | op i args => exact badXP_op hbad
    | block bt body => exact badXP_block hbad
    | loop bt body => exact badXP_loop hbad
    | if_ bt c t el => exact badXP_if hbad
    | tryTable bt cs body => exact badXP_try hbad

end Ctl

/-- **One unfolding of a call**: a typed call without an answer has a body without an outcome,
or a body ending in a pending tail call whose own call has no answer. -/
theorem badCallP_step {tags : List TagInst} {s : Store H} {a : Nat} {args : List Val}
    (hb : BadCallP tags s a args) : CallStepXP (BadXP tags) (BadCallP tags) s a args := by
  obtain ⟨hct, hW, hne⟩ := hb
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, -⟩, -⟩ := id hct
  obtain ⟨fn, -, -, hcode, -⟩ := hW a fi hfi
  have htb := callee_typedP hct hfi hcode
  by_cases hex : ∃ r, EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
      (Binaryen.liftInstrs fn.body) r
  swap
  · exact .body hfi hcode ⟨⟨htb, hW⟩, hex⟩
  obtain ⟨⟨s₁, f₂, o⟩, d⟩ := hex
  cases o with
  | flow fl => exact absurd ⟨_, closedCallXP_of_body hfi hcode hty d .flow⟩ hne
  | tail a' args' n =>
    have hct' := callTyped_tail hct hfi hcode d
    rcases callee_splitP hct' (wasmFuncsT_runP d hW) with hb' | ⟨s₂, fl, hcall, hfl⟩
    · exact .frameTail hfi hcode d hb'
    · exact absurd ⟨_, closedCallXP_of_body hfi hcode hty d (.tail hcall hfl)⟩ hne

/-- **Bad problems and calls diverge.** -/
theorem badXP_le {tags : List TagInst} :
    (BadXP tags : Interp.Problem H) ≤ EvalDivXP ∧ (BadCallP tags : CallProblem H) ≤ FunDivXP :=
  evalDivXP_of_coind (fun _ _ _ _ h => badXP_step h) (fun _ _ _ h => badCallP_step h)

/-- **No closed outcome means divergence**, for typed problems in a store of Wasm functions. -/
theorem evalDivXP_of_noOutcome {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (ht : TypedP tags s f stk es) (hW : WasmFuncsT s)
    (hne : ¬ ∃ r, EvalOXP closedCallXP s f stk es r) : EvalDivXP s f stk es :=
  badXP_le.1 s f stk es ⟨⟨ht, hW⟩, hne⟩

/-- **No closed answer means divergence**, for typed calls in a store of Wasm functions. -/
theorem funDivXP_of_noAnswer {tags : List TagInst} {s : Store H} {a : Nat} {args : List Val}
    (ht : CallTypedP tags s a args) (hW : WasmFuncsT s)
    (hne : ¬ ∃ out, closedCallXP s a args out) : FunDivXP s a args :=
  badXP_le.2 s a args ⟨ht, hW, hne⟩

end Silmaril.Wasm.Interp
