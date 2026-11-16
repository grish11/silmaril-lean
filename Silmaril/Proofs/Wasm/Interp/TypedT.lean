module

public import Silmaril.Proofs.Wasm.Interp.TypedX
public import Silmaril.Proofs.Wasm.Interp.TailX

/-!
# The arity premises with tail calls, from typing (proofs)

`TypedX.evalOXT_of_typed` for the tail checker `tExt`: a run of `tExt`-checked code whose
Core configuration is typed in context is an `EvalOXT` run (`evalOXT_of_typedT`). Besides the
indirect and reference calls, the tail forms carry their premise: `return_call_indirect` from
the cast (`CallXT.typeArity_of_indRes`), `return_call_ref` from the typed site
(`CallXT.typeArity_of_returnCallRef_site`). The typing is carried along the run as in
`TypedX`, by the tail-aware simulation `evalOXT_goodT` (a terminating prefix ends matched).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

variable {H : Type} {P : Numerics.Profile}

/-- **A typed terminating prefix keeps the rest typed.** -/
theorem prefix_typedT {C : Abstract.CallRel H} (hC : OracleSoundT P noHostX C) {s s' : Store H}
    {f f' : Frame} {stk stk' : List Val} {es : List Binaryen.BExpr} {rest : List Admin}
    {labels : List Nat} {ret : Nat} {o : Option Nat}
    (d : EvalOXT C s f stk es (s', f', .normal stk')) (hS : StoreChkE tExt s.funcs)
    (hc : chkE tExt s.funcs f.module f.locals.length ret labels (some stk.length) es = some o)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩) :
    Sim.ContextTyped ⟨s', f', vals stk'.reverse ++ rest⟩ ∧ o = some stk'.length ∧
      EvalInvE tExt s f (s', f', .normal stk') := by
  obtain ⟨hA, hCo⟩ := evalOXT_goodT (P := P) (host := noHostX) hC d
  obtain ⟨hok, hinv⟩ := hA hS hc
  obtain ⟨c', oc, hrun, he, hm⟩ := run_of_wp (by simpa only [matchT_normal] using hCo hS hc)
  have hc' := ends_normal hm he
  subst hc'
  exact ⟨Sim.ContextTyped.steps ht (Steps.append rest hrun), hok, hinv⟩

/-- A typed problem: checked by `tExt` in a checked store, its Core code typed in
context, with valid function and instance types. -/
def TypedT (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  ∃ (rest : List Admin) (labels : List Nat) (ret : Nat) (out : Option Nat),
    StoreChkE tExt s.funcs ∧
    chkE tExt s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩ ∧
    TyFuncs s ∧ TyTypes f.module

theorem chkE_nil_selfT {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat} {labels : List Nat}
    (o : Option Nat) : chkE tExt F mi nl ret labels o [] = some o := by
  cases o <;> rfl

section
variable {C : Abstract.CallRel H} (hC : OracleSoundT P noHostX C) (hCk : KeepsTy C)
include hC hCk

/-- **The continuation after a typed head is typed.** -/
theorem cont_typedT {e : Binaryen.BExpr} {es : List Binaryen.BExpr} {s s₂ : Store H} {f f₂ : Frame}
    {stk stk₂ : List Val} (d : EvalOXT C s f stk [e] (s₂, f₂, .normal stk₂))
    (ht : TypedT s f stk (e :: es)) : TypedT s₂ f₂ stk₂ es := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  have h1' : chkE tExt s.funcs f.module f.locals.length ret labels (some stk.length) [e] = some o :=
    chk_consE.mpr ⟨o, h1, chkE_nil_selfT o⟩
  rw [code_consX] at hct
  obtain ⟨ht₂, ho, inv⟩ := prefix_typedT (P := P) hC d hS h1' hct
  subst ho
  refine ⟨rest, labels, ret, out, inv.1.2.1 hS, chk_inv inv h2, by simpa only [List.append_assoc] using ht₂,
    evalOX_tyFuncs hCk (EvalOXT.forget d) hTF, ?_⟩
  rw [inv.2.1]; exact hTM

omit hC hCk in
/-- The arguments of a typed operator are typed. -/
theorem args_typedT {i : Instr} {args es : List Binaryen.BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (ht : TypedT s f stk (.op i args :: es)) : TypedT s f stk args := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  refine ⟨.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, oa, hS, ha, ?_,
    hTF, hTM⟩
  rw [code_op] at hct
  simpa only [List.append_assoc, List.cons_append] using hct

/-- **The site of an operator, after its typed arguments.** -/
theorem site_typedT {i : Instr} {args es : List Binaryen.BExpr} {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} (d : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
    (ht : TypedT s f stk (.op i args :: es)) :
    ∃ rest, Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ ∧ TyFuncs s₁ ∧
      TyTypes f₁.module ∧ ∃ labels ret o, StoreChkE tExt s.funcs ∧
        flatChkE tExt s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, hf⟩ := chk1_opE h1
  rw [code_op] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args) ++
      (.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨ht₁, ho, inv⟩ := prefix_typedT (P := P) hC d hS ha hct'
  subst ho
  refine ⟨_, ht₁, evalOX_tyFuncs hCk (EvalOXT.forget d) hTF, by rw [inv.2.1]; exact hTM,
    labels, ret, o, hS, flatChk_inv inv (hf _ rfl)⟩

end

section
variable {C : Abstract.CallRel H} (hC : OracleSoundT P noHostX C) (hCk : KeepsTy C)

omit hC hCk in
include P in
/-- A block body of a typed problem is typed. -/
theorem block_body_typedT {bt : BlockType} {body es : List Binaryen.BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedT s f stk (.block bt body :: es)) : TypedT s f (stk.take np) body := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  rw [code_block] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := steps_enter (P := P) (host := noHostX) (s := s) (f := f) hp
    (step_block (B := Binaryen.BExpr.lowerList body) har) (expression (Binaryen.BExpr.lowerList es) ++ rest)
  have hin := Sim.ContextTyped.label (Sim.ContextTyped.steps hct' hst)
  refine ⟨[], nr :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', ?_, hTF, hTM⟩
  simpa only [List.append_nil] using hin

omit hC hCk in
include P in
/-- A loop body of a typed problem is typed. -/
theorem loop_body_typedT {bt : BlockType} {body es : List Binaryen.BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedT s f stk (.loop bt body :: es)) : TypedT s f (stk.take np) body := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  rw [code_loop] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := steps_enter (P := P) (host := noHostX) (s := s) (f := f) hp
    (step_loop (B := Binaryen.BExpr.lowerList body) har) (expression (Binaryen.BExpr.lowerList es) ++ rest)
  have hin := Sim.ContextTyped.label (Sim.ContextTyped.steps hct' hst)
  refine ⟨[], np :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', ?_, hTF, hTM⟩
  simpa only [List.append_nil] using hin

include hC hCk in
/-- **The next iteration of a typed loop whose body branched back is typed.** -/
theorem loop_back_typedT {bt : BlockType} {body es : List Binaryen.BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk vs : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (d : EvalOXT C s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ht : TypedT s f stk (.loop bt body :: es)) :
    TypedT s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hb'' : chkE tExt s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by rw [take_length_of_le hp]; exact hb'
  obtain ⟨hA, hCo⟩ := evalOXT_goodT (P := P) (host := noHostX) hC d
  obtain ⟨hok, inv⟩ := hA hS hb''
  obtain ⟨n, hn, hnv⟩ := hok
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
  subst hn
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (by simpa only [matchT_brk] using hCo hS hb'')
  rw [code_loop] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := tg_loop_back (P := P) (host := noHostX)
    (rest := expression (Binaryen.BExpr.lowerList es) ++ rest) har hp hrun he hm hnv
  have hnew := Sim.ContextTyped.steps hct' hst.to_reflTransGen
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  refine ⟨rest, labels, ret, out, inv.1.2.1 hS, by rw [hlen]; exact chk_inv inv hc, ?_,
    evalOX_tyFuncs hCk (EvalOXT.forget d) hTF, by rw [inv.2.1]; exact hTM⟩
  rw [code_loop]
  simpa only [List.append_assoc, List.cons_append] using hnew

omit hC hCk in
/-- The condition of a typed `if` is typed. -/
theorem cond_typedT {bt : BlockType} {c t el es : List Binaryen.BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (ht : TypedT s f stk (.if_ bt c t el :: es)) : TypedT s f stk c := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  refine ⟨.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
    expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, oc, hS, hco, ?_, hTF, hTM⟩
  rw [code_if] at hct
  simpa only [List.append_assoc, List.cons_append] using hct

include hC hCk in
/-- **The chosen arm of a typed `if`, after its typed condition, is typed.** -/
theorem arm_typedT {bt : BlockType} {c t el es : List Binaryen.BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool} {np nr : Nat}
    (d : EvalOXT C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hbv : Binaryen.truthy cv = some b)
    (har : Binaryen.arity f₁ bt = some (np, nr)) (ht : TypedT s f stk (.if_ bt c t el :: es)) :
    TypedT s₁ f₁ (stk₁.take np) (if b then t else el) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨hA, -⟩ := evalOXT_goodT (P := P) (host := noHostX) hC d
  obtain ⟨inv1, hp, hb, -⟩ := arity_if_pre (b := b) hS (fun hS' hc' => hA hS' hc') har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq (chk_inv_endsAt inv1 hb)
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c) ++
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨htc, -, -⟩ := prefix_typedT (P := P) hC d hS hco hct'
  -- the `if` steps to the chosen arm, as a block
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hbv
  let R := expression (Binaryen.BExpr.lowerList es) ++ rest
  have hif : Steps P noHostX ⟨s₁, f₁, vals (Val.i32 c₀ :: stk₁).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R⟩
      ⟨s₁, f₁, vals stk₁.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if (c₀ != 0) then t else el))) :: R⟩ := by
    have e : vals (Val.i32 c₀ :: stk₁).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R =
        vals stk₁.reverse ++ [constI32 c₀,
          .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ R := by
      simp [vals, constI32]
    rw [e]
    by_cases h0 : c₀ = 0
    · subst h0
      simpa using Relation.ReflTransGen.single (Step.ctx (P := P) (host := noHostX) stk₁.reverse R
        (Step.ifFalse (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
          (b₂ := Binaryen.BExpr.lowerList el)))
    · have h1 : (c₀ != 0) = true := by simpa using h0
      simp only [h1, ↓reduceIte]
      simpa using Relation.ReflTransGen.single (Step.ctx (P := P) (host := noHostX) stk₁.reverse R
        (Step.ifTrue (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
          (b₂ := Binaryen.BExpr.lowerList el) h0))
  have hst := steps_enter (P := P) (host := noHostX) (s := s₁) (f := f₁) hp
    (step_block (B := Binaryen.BExpr.lowerList (if (c₀ != 0) then t else el)) har) R
  have hin := Sim.ContextTyped.label (Sim.ContextTyped.steps (Sim.ContextTyped.steps htc hif) hst)
  refine ⟨[], nr :: labels, ret, ob, storeChk_inv inv1 hS,
    by rw [take_length_of_le hp]; exact hb', ?_, evalOX_tyFuncs hCk (EvalOXT.forget d) hTF,
    by rw [inv1.2.1]; exact hTM⟩
  simpa only [List.append_nil, apply_ite Binaryen.BExpr.lowerList] using hin

end

/-- A checked `call_indirect` names a type of the instance. -/
theorem types_some_of_flatChkT {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TableIdx} {y : TypeIdx} {o : Option Nat}
    (hc : flatChkE tExt F mi nl ret labels h (.callIndirect x y) = some o) :
    (mi.types[y.toNat]?).isSome = true := by
  cases hta : typeArity mi y with
  | none => simp [flatChkE, tExt, hta, extStep] at hc
  | some p =>
    unfold typeArity at hta
    cases hd : mi.types[y.toNat]? with
    | none => simp [hd] at hta
    | some _ => rfl

/-- A checked `return_call_indirect` names a type of the instance. -/
theorem types_some_of_flatChk_rci {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TableIdx} {y : TypeIdx} {o : Option Nat}
    (hc : flatChkE tExt F mi nl ret labels h (.returnCallIndirect x y) = some o) :
    (mi.types[y.toNat]?).isSome = true := by
  cases hta : typeArity mi y with
  | none => simp [flatChkE, tExt, hta, extStep] at hc
  | some p =>
    unfold typeArity at hta
    cases hd : mi.types[y.toNat]? with
    | none => simp [hd] at hta
    | some _ => rfl

/-- **The premise of a resolved tail call at a typed site**: `return_call_indirect` from
the cast, `return_call_ref` from the site's typing. -/
theorem tailAnn_typed {i : Instr} {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    {rest : List Admin} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    {labels : List Nat} {ret : Nat} {o : Option Nat}
    (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
    (hsite : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hTF : TyFuncs s₁) (hTM : TyTypes f₁.module)
    (hf : flatChkE tExt s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o) :
    ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length) := by
  intro y hy
  cases hres with
  | direct => simp [tailAnn] at hy
  | indirect hres' =>
    simp only [tailAnn, Option.some.injEq] at hy
    subst hy
    exact typeArity_of_indRes hres' hfi hty hTF hTM (types_some_of_flatChk_rci hf)
  | ref =>
    simp only [tailAnn, Option.some.injEq] at hy
    subst hy
    exact typeArity_of_returnCallRef_site hsite hTM hfi hty (hTF _ _ hfi)

section
variable {C : Abstract.CallRel H} (hC : OracleSoundT P noHostX C) (hCk : KeepsTy C)
include hC hCk

/-- **Typed runs carry their arity premises.** A run of `tExt`-checked code in a
checked store, whose Core configuration is typed in context, with valid function and
instance types and an oracle keeping them, is an `EvalOXT` run. -/
theorem evalOXT_of_typedT {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX C s f stk es r) :
    TypedT s f stk es → EvalOXT C s f stk es r := by
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih => exact fun ht => .argsAbort (ih (args_typedT ht)) hfl
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    exact .callOk dA hfi hty hcall hvs
      (ihk (cont_typedT (P := P) hC hCk (.callOk dA hfi hty hcall hvs .nil) ht))
  | callTrap _ hfi hty hcall iha => exact fun ht => .callTrap (iha (args_typedT ht)) hfi hty hcall
  | callThrow _ hfi hty hcall iha => exact fun ht => .callThrow (iha (args_typedT ht)) hfi hty hcall
  | opOk hi _ hflat _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    exact .opOk hi dA hflat (ihk (cont_typedT (P := P) hC hCk (.opOk hi dA hflat .nil) ht))
  | opStop hi _ hflat hfl iha => exact fun ht => .opStop hi (iha (args_typedT ht)) hflat hfl
  | blockOk har _ hvs _ ihb ihk =>
    intro ht
    have dB := ihb (block_body_typedT (P := P) har ht)
    exact .blockOk har dB hvs (ihk (cont_typedT (P := P) hC hCk (.blockOk har dB hvs .nil) ht))
  | blockBrk har _ ihb => exact fun ht => .blockBrk har (ihb (block_body_typedT (P := P) har ht))
  | blockEsc har _ hfl ihb =>
    exact fun ht => .blockEsc har (ihb (block_body_typedT (P := P) har ht)) hfl
  | loopOk har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedT (P := P) har ht)
    exact .loopOk har dB (ihk (cont_typedT (P := P) hC hCk (.loopOk har dB .nil) ht))
  | loopBack har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedT (P := P) har ht)
    exact .loopBack har dB (ihk (loop_back_typedT (P := P) hC hCk har dB ht))
  | loopBrk har _ ihb => exact fun ht => .loopBrk har (ihb (loop_body_typedT (P := P) har ht))
  | loopEsc har _ hfl ihb =>
    exact fun ht => .loopEsc har (ihb (loop_body_typedT (P := P) har ht)) hfl
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    intro ht
    have dC := ihc (cond_typedT ht)
    have dA := iharm (arm_typedT (P := P) hC hCk dC hb har ht)
    exact .ifOk dC hb har dA hvs (ihk (cont_typedT (P := P) hC hCk (.ifOk dC hb har dA hvs .nil) ht))
  | ifBrk _ hb har _ ihc iharm =>
    intro ht
    have dC := ihc (cond_typedT ht)
    exact .ifBrk dC hb har (iharm (arm_typedT (P := P) hC hCk dC hb har ht))
  | ifEsc _ hb har _ hfl ihc iharm =>
    intro ht
    have dC := ihc (cond_typedT ht)
    exact .ifEsc dC hb har (iharm (arm_typedT (P := P) hC hCk dC hb har ht)) hfl
  | ifAbort _ hfl ihc => exact fun ht => .ifAbort (ihc (cond_typedT ht)) hfl
  | callIndOk _ hres hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, _, hTF, hTM, _, _, _, _, hf⟩ := site_typedT (P := P) hC hCk dA ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
    exact .callIndOk dA hres hfi hty hy hcall hvs
      (ihk (cont_typedT (P := P) hC hCk (.callIndOk dA hres hfi hty hy hcall hvs .nil) ht))
  | callIndRes _ hres iha => exact fun ht => .callIndRes (iha (args_typedT ht)) hres
  | callIndStop _ hres hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, _, hTF, hTM, _, _, _, _, hf⟩ := site_typedT (P := P) hC hCk dA ht
    exact .callIndStop dA hres hfi hty
      (typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)) hcall hfl
  | callRefOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨rest, hsite, hTF, hTM, -⟩ := site_typedT (P := P) hC hCk dA ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    exact .callRefOk dA hfi hty hy hcall hvs
      (ihk (cont_typedT (P := P) hC hCk (.callRefOk dA hfi hty hy hcall hvs .nil) ht))
  | callRefNull _ iha => exact fun ht => .callRefNull (iha (args_typedT ht))
  | callRefStop _ hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨rest, hsite, hTF, hTM, -⟩ := site_typedT (P := P) hC hCk dA ht
    exact .callRefStop dA hfi hty (typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)) hcall hfl
  | tail _ hres hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, hTF, hTM, _, _, _, _, hf⟩ := site_typedT (P := P) hC hCk dA ht
    exact .tail dA hres hfi hty (tailAnn_typed hres hsite hfi hty hTF hTM hf) hcall hfl
  | tailRes _ hres iha => exact fun ht => .tailRes (iha (args_typedT ht)) hres

end

end Silmaril.Wasm.Interp
