module

public import Silmaril.Proofs.Wasm.Interp.XIndRes
public import Silmaril.Proofs.Wasm.Interp.DivergeTyped

/-!
# Typed problems with no closed extended outcome diverge (proofs)

The extended analog of `bad_le_evalDiv`: a typed problem (`TypedT`, every call form) in a store
whose functions are all Wasm functions with function types (`WasmFuncsT`), that has no outcome
in the closed extended semantics, diverges coinductively (`evalDivX_of_noOutcome`).

`badX_step`: such a problem unfolds into a divergence step (`DivStepX`) whose parts are again
such problems. Typing rules out every way of getting stuck: flat instructions
(`evalFlat_progressH`), conditions (`truthy_progressH`), callee answers (`calleeX_flow`), the
operand of a reference call (`callRef_top`, `returnCallRef_top`), and indirect resolution
(`indirect_res`). A host callee would have neither an outcome nor a divergence (Core is stuck
there), hence `WasmFuncsT`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Wasm.Abstract.XDiverge

variable {H : Type}

/-- The profile used for the Core side of the invariants (any profile would do). -/
abbrev Pd : Numerics.Profile := SingleThreaded.profile o₀

/-- Every function of the store is a Wasm function with a function type. -/
def WasmFuncsT (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H), s.funcs[a]? = some fi →
    ∃ (fn : Func) (ps rs : List Validation.CValType), fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs)

/-- A typed problem in such a store. -/
def GoodX (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  TypedT s f stk es ∧ WasmFuncsT s

/-- A good problem with no closed extended outcome. -/
def BadX (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  GoodX s f stk es ∧ ¬ ∃ r, EvalOX closedCallX s f stk es r

section Cases

variable {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

theorem goodX_split {s' : Store H} {f' : Frame} {stk' : List Val} {es' : List Binaryen.BExpr}
    (hg : GoodX s' f' stk' es') : BadX s' f' stk' es' ∨ ∃ r, EvalOX closedCallX s' f' stk' es' r := by
  by_cases h : ∃ r, EvalOX closedCallX s' f' stk' es' r
  · exact .inr h
  · exact .inl ⟨hg, h⟩

theorem wasmFuncsT_run {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (d : EvalOX closedCallX s f stk es r)
    (hW : WasmFuncsT s) : WasmFuncsT r.1 :=
  fun a fi h => hW a fi (evalOX_funcs (fun _ _ _ _ h => closedCallX_funcs h) d ▸ h)

theorem goodX_cont {e : Binaryen.BExpr} {s₂ : Store H} {f₂ : Frame} {stk₂ : List Val}
    (d : EvalOX closedCallX s f stk [e] (s₂, f₂, .normal stk₂)) (hg : GoodX s f stk (e :: es)) :
    GoodX s₂ f₂ stk₂ es :=
  ⟨cont_typedT (P := Pd) oracleSoundT_typedClosed keepsTy_CX
    (evalOXT_restrictT (P := Pd) oracleSoundT_typedClosed keepsTy_closedCallX d (head_typedT hg.1))
    hg.1, wasmFuncsT_run d hg.2⟩

/-- A typed callee body either has no outcome, or answers by returning, trapping or throwing. -/
theorem callee_split {s₁ : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hS : StoreChkE tExt s₁.funcs) (hW : WasmFuncsT s₁)
    (hE : TypedEntry s₁ a us) (hfi : s₁.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    BadX s₁ (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) ∨
      ∃ (s₂ : Store H) (f₂ : Frame) (fl : Binaryen.Flow),
        EvalOX closedCallX s₁ (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
          (s₂, f₂, fl) ∧ closedCallX s₁ a us (s₂, fl) ∧ ((∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) := by
  rcases goodX_split ⟨callee_typedT hS hE hfi hcode hty hn, hW⟩ with hb | ⟨⟨s₂, f₂, fl⟩, d⟩
  · exact .inl hb
  have hcall : closedCallX s₁ a us (s₂, fl) := by
    rw [closedCallX_fixpoint]; exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d⟩
  refine .inr ⟨s₂, f₂, fl, d, hcall, ?_⟩
  rcases calleeX_flow (P := Pd) hS hfi hcode hty hn hE hcall with h | rfl | ⟨t, rfl⟩
  · exact .inl h
  · exact .inr trivial
  · exact .inr trivial

theorem instr_cases (i : Instr) :
    (∃ x, i = .call x) ∨ (∃ x y, i = .callIndirect x y) ∨ (∃ y, i = .callRef y) ∨
      (∃ x, i = .returnCall x) ∨ (∃ x y, i = .returnCallIndirect x y) ∨ (∃ y, i = .returnCallRef y) ∨
      ((∃ x, i = .throw x) ∨ i = .throwRef) ∨ ((∀ x, i ≠ .call x) ∧ ¬ Instr.IsExtCall i) := by
  cases i <;> simp [Instr.IsExtCall]

end Cases

section Op

variable {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

/-- The tail call forms, once resolved. -/
theorem badX_tail {i : Instr} {args : List Binaryen.BExpr} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {fa : Nat} {fi : FuncInst H} {rest₀ : List Admin} {labels : List Nat}
    {ret : Nat} {o : Option Nat} (hne : ¬ ∃ r, EvalOX closedCallX s f stk (.op i args :: es) r)
    (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
    (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
    (hfi : s₁.funcs[fa]? = some fi)
    (hsite : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest₀⟩)
    (hTF : TyFuncs s₁) (hTM : TyTypes f₁.module)
    (hf : flatChkE tExt s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o)
    (hS₁ : StoreChkE tExt s₁.funcs) (hW₁ : WasmFuncsT s₁) :
    DivStepX BadX BadX s f stk (.op i args :: es) := by
  obtain ⟨fn, ps, rs, hcode, hty⟩ := hW₁ fa fi hfi
  have hy := tailAnn_typed hres hsite hfi hty hTF hTM hf
  obtain ⟨hp, -, -⟩ := flatChk_tailForm (tExt_tail hres hfi hty hy) hf
  have hE := entry_of_tail_site (P := Pd) hsite hres hfi hty hy hTF hTM hf
  rcases callee_split hS₁ hW₁ hE hfi hcode hty
      (by simp only [List.length_reverse, List.length_take, List.length_drop]; omega) with
    hb | ⟨s₂, f₂, fl, hbody, hcall, hfl⟩
  · exact .tailCallee hargs hres hfi hcode hty hb
  · exact absurd ⟨_, .tail hargs hres hfi hty hcall hfl⟩ hne

theorem fi_of_indRes {s₁ : Store H} {f₁ : Frame} {x : TableIdx} {y : TypeIdx} {ad : AddrType}
    {j : BitVec ad.intType.width} {fa : Nat}
    (hres : Abstract.CallRes.IndRes s₁ f₁ x y ad j (some fa)) : ∃ fi, s₁.funcs[fa]? = some fi := by
  cases hres with
  | func _ _ hc =>
    obtain ⟨rt₀, e, -⟩ := hc.principal
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, h, -⟩ := e
    exact ⟨fi, h⟩

/-- **Operators.** -/
theorem badX_op {i : Instr} {args : List Binaryen.BExpr} (hbad : BadX s f stk (.op i args :: es)) :
    DivStepX BadX BadX s f stk (.op i args :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hta := args_typedT ht
  rcases goodX_split ⟨hta, hW⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hargs⟩
  · exact .args hb
  by_cases hn : fl.IsNormal
  swap
  · exact absurd ⟨_, .argsAbort hargs hn⟩ hne
  rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
  have hC := oracleSoundT_typedClosed (P := Pd) (H := H)
  have dA := evalOXT_restrictT (P := Pd) hC keepsTy_closedCallX hargs hta
  obtain ⟨-, hS₁⟩ := prefix_runT (P := Pd) hargs hta
  obtain ⟨rest₀, hsite, hTF, hTM, labels, ret, o, -, hf⟩ := site_typedT (P := Pd) hC keepsTy_CX dA ht
  have hW₁ : WasmFuncsT s₁ := wasmFuncsT_run hargs hW
  have hg : GoodX s f stk (.op i args :: es) := ⟨ht, hW⟩
  rcases instr_cases i with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ |
    (⟨x, rfl⟩ | rfl) | ⟨hi, hx⟩
  rotate_left 6
  · -- `tExt` rejects `throw`
    simp [flatChkE, tExt, extStep] at hf
  · -- and `throw_ref`
    simp [flatChkE, tExt, extStep] at hf
  rotate_right 6
  · -- call
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    obtain ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩ := callArity_func? hpq
    obtain ⟨fn, -, -, hcode, -⟩ := hW₁ a fi (funcs_of_func? hfi)
    have hE := entry_of_call_siteT (P := Pd) hsite hfi hty hf
    rcases callee_split hS₁ hW₁ hE (funcs_of_func? hfi) hcode hty
        (by simp only [List.length_reverse, List.length_take]; omega) with
      hb | ⟨s₂, f₂, fl, hbody, hcall, hfl⟩
    · exact .callee hargs hfi hcode hty hb
    rcases hfl with ⟨vs, hvs⟩ | hab
    · rcases goodX_split (goodX_cont (.callOk hargs hfi hty hcall hvs .nil) hg) with hb | ⟨r, hk⟩
      · exact .callRet hargs hfi hcode hty hbody hvs hb
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
      have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
      obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf
      simp only [List.length_cons] at hp
      have hE := entry_of_ind_siteT (P := Pd) hsite hres hfi hty hy hf
      rcases callee_split hS₁ hW₁ hE hfi hcode hty
          (by simp only [List.length_reverse, List.length_take]; omega) with
        hb | ⟨s₂, f₂, fl, hbody, hcall, hfl⟩
      · exact .callIndCallee hargs hres hfi hcode hty hb
      rcases hfl with ⟨vs, hvs⟩ | hab
      · rcases goodX_split (goodX_cont (.callIndOk hargs hres hfi hty hcall hvs .nil) hg) with
          hb | ⟨r, hk⟩
        · exact .callIndRet hargs hres hfi hcode hty hbody hvs hb
        · exact absurd ⟨r, .callIndOk hargs hres hfi hty hcall hvs hk⟩ hne
      · exact absurd ⟨_, .callIndStop hargs hres hfi hty hcall hab⟩ hne
  · -- call_ref
    obtain ⟨r, stk', rfl, hr⟩ := callRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact absurd ⟨_, .callRefNull hargs⟩ hne
    obtain ⟨fn, ps, rs, hcode, hty⟩ := hW₁ fa fi hfi
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf
    simp only [List.length_cons] at hp
    have hE := entry_of_callRef_siteT (P := Pd) hsite hfi hty hy hf
    rcases callee_split hS₁ hW₁ hE hfi hcode hty
        (by simp only [List.length_reverse, List.length_take]; omega) with
      hb | ⟨s₂, f₂, fl, hbody, hcall, hfl⟩
    · exact .callRefCallee hargs hfi hcode hty hb
    rcases hfl with ⟨vs, hvs⟩ | hab
    · rcases goodX_split (goodX_cont (.callRefOk hargs hfi hty hcall hvs .nil) hg) with
        hb | ⟨r, hk⟩
      · exact .callRefRet hargs hfi hcode hty hbody hvs hb
      · exact absurd ⟨r, .callRefOk hargs hfi hty hcall hvs hk⟩ hne
    · exact absurd ⟨_, .callRefStop hargs hfi hty hcall hab⟩ hne
  · -- return_call
    have hca : ∃ p, callArity s₁.funcs f₁.module x = some p := by
      cases h : callArity s₁.funcs f₁.module x with
      | none => simp [flatChkE, tExt, h, extStep] at hf
      | some p => exact ⟨p, rfl⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := hca
    obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := callArity_func? hpq
    exact badX_tail hne hargs (.direct hfi) (funcs_of_func? hfi) hsite hTF hTM hf hS₁ hW₁
  · -- return_call_indirect
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := indirect_res (.inr rfl) hsite
    cases o' with
    | none => exact absurd ⟨_, .tailRes hargs (.indirectTrap hres)⟩ hne
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      exact badX_tail hne hargs (.indirect hres) hfi hsite hTF hTM hf hS₁ hW₁
  · -- return_call_ref
    obtain ⟨r, stk', rfl, hr⟩ := returnCallRef_top hsite hTM
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact absurd ⟨_, .tailRes hargs .refNull⟩ hne
    · exact badX_tail hne hargs .ref hfi hsite hTF hTM hf hS₁ hW₁
  · -- a flat instruction
    have hf' : flatChk s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
      rw [← flatChkE_eq_flatChk tExt hx]; exact hf
    obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := evalFlat_progressH hf' hi hsite
    by_cases hn₂ : fl₂.IsNormal
    swap
    · exact absurd ⟨_, .opStop hi hargs hflat hn₂⟩ hne
    rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn₂
    rcases goodX_split (goodX_cont (.opOk hi hargs hflat .nil) hg) with hb | ⟨r, hk⟩
    · exact .opK hi hargs hflat hb
    · exact absurd ⟨r, .opOk hi hargs hflat hk⟩ hne

end Op

section Ctl

variable {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

/-- **Blocks.** -/
theorem badX_block {bt : BlockType} {body : List Binaryen.BExpr}
    (hbad : BadX s f stk (.block bt body :: es)) : DivStepX BadX BadX s f stk (.block bt body :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodX s f stk (.block bt body :: es) := ⟨ht, hW⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  rcases goodX_split ⟨block_body_typedT (P := Pd) har ht, hW⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hbody⟩
  · exact .block har hb
  rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
  · rcases goodX_split (goodX_cont (.blockOk har hbody hvs .nil) hg) with hb | ⟨r, hk⟩
    · exact .blockK har hbody hvs hb
    · exact absurd ⟨r, .blockOk har hbody hvs hk⟩ hne
  · exact absurd ⟨_, .blockBrk har hbody⟩ hne
  · exact absurd ⟨_, .blockEsc har hbody hesc⟩ hne

/-- **Loops.** -/
theorem badX_loop {bt : BlockType} {body : List Binaryen.BExpr}
    (hbad : BadX s f stk (.loop bt body :: es)) : DivStepX BadX BadX s f stk (.loop bt body :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodX s f stk (.loop bt body :: es) := ⟨ht, hW⟩
  obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  have hbt := loop_body_typedT (P := Pd) har ht
  rcases goodX_split ⟨hbt, hW⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hbody⟩
  · exact .loop har hb
  rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
  · rcases goodX_split (goodX_cont (.loopOk har hbody .nil) hg) with hb | ⟨r, hk⟩
    · exact .loopK har hbody hb
    · exact absurd ⟨r, .loopOk har hbody hk⟩ hne
  · have hgb : GoodX s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) :=
      ⟨loop_back_typedT (P := Pd) oracleSoundT_typedClosed keepsTy_CX har
        (evalOXT_restrictT (P := Pd) oracleSoundT_typedClosed keepsTy_closedCallX hbody hbt) ht,
        wasmFuncsT_run hbody hW⟩
    rcases goodX_split hgb with hb | ⟨r, hk⟩
    · exact .loopBack har hbody hb
    · exact absurd ⟨r, .loopBack har hbody hk⟩ hne
  · exact absurd ⟨_, .loopBrk har hbody⟩ hne
  · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
  · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
  · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne

/-- **Conditionals.** -/
theorem badX_if {bt : BlockType} {c t el : List Binaryen.BExpr}
    (hbad : BadX s f stk (.if_ bt c t el :: es)) : DivStepX BadX BadX s f stk (.if_ bt c t el :: es) := by
  obtain ⟨⟨ht, hW⟩, hne⟩ := hbad
  have hg : GoodX s f stk (.if_ bt c t el :: es) := ⟨ht, hW⟩
  have htc := cond_typedT ht
  rcases goodX_split ⟨htc, hW⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hcond⟩
  · exact .cond hb
  by_cases hn : fl.IsNormal
  swap
  · exact absurd ⟨_, .ifAbort hcond hn⟩ hne
  rcases fl with stk₁' | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
  have hC := oracleSoundT_typedClosed (P := Pd) (H := H)
  have dC := evalOXT_restrictT (P := Pd) hC keepsTy_closedCallX hcond htc
  obtain ⟨rest, labels, ret, out, hS, hc, hct, -, -⟩ := id ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  rw [code_if] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c) ++
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨hct₁, ho, inv1⟩ := prefix_typedT (P := Pd) hC dC hS hco hct'
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := truthy_progressH (by simpa only [List.cons_append] using hct₁)
  obtain ⟨np, nr, ha, -, -, -, -⟩ := hk1 _ ho
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [arity_eq, inv1.2.1]
    exact ha
  have dC' : EvalOXT (CX (closedCallX : Abstract.CallRel H)) s f stk c (s₁, f₁, .normal (cv :: stk₁)) := dC
  rcases goodX_split ⟨arm_typedT (P := Pd) hC keepsTy_CX dC' hb har ht, wasmFuncsT_run hcond hW⟩ with
    hba | ⟨⟨s₂, f₂, fl⟩, harm⟩
  · exact .arm hcond hb har hba
  rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
  · rcases goodX_split (goodX_cont (.ifOk hcond hb har harm hvs .nil) hg) with hbk | ⟨r, hk⟩
    · exact .ifK hcond hb har harm hvs hbk
    · exact absurd ⟨r, .ifOk hcond hb har harm hvs hk⟩ hne
  · exact absurd ⟨_, .ifBrk hcond hb har harm⟩ hne
  · exact absurd ⟨_, .ifEsc hcond hb har harm hesc⟩ hne

/-- **One unfolding**: a good problem without a closed extended outcome takes a divergence
step into such problems. -/
theorem badX_step (hbad : BadX s f stk es) : DivStepX BadX BadX s f stk es := by
  rcases es with _ | ⟨e, es⟩
  · exact absurd ⟨_, .nil⟩ hbad.2
  · cases e with
    | op i args => exact badX_op hbad
    | block bt body => exact badX_block hbad
    | loop bt body => exact badX_loop hbad
    | if_ bt c t el => exact badX_if hbad
    | tryTable bt cs body =>
      obtain ⟨⟨⟨rest, labels, ret, out, -, hc, -⟩, -⟩, -⟩ := hbad
      obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
      simp [chk1E, tExt] at h1

end Ctl

/-- **A good problem without a closed extended outcome diverges.** -/
theorem badX_le_evalDivX : (BadX : Problem H) ≤ EvalDivX :=
  evalDivX_of_coind fun _ _ _ _ h => badX_step h

/-- **No closed extended outcome means extended divergence**, for typed problems (`TypedT`,
every call form) in a store of Wasm functions. -/
theorem evalDivX_of_noOutcome {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    (ht : TypedT s f stk es) (hW : WasmFuncsT s)
    (hne : ¬ ∃ r, EvalOX closedCallX s f stk es r) : EvalDivX s f stk es :=
  badX_le_evalDivX s f stk es ⟨⟨ht, hW⟩, hne⟩

end Silmaril.Wasm.Interp
