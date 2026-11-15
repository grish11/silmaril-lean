module

public import Silmaril.Proofs.Wasm.Interp.OracleCloseX
public import Silmaril.Wasm.Abstract.CallXT.Thms
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

/-!
# The arity premises of the extended relation, from typing (proofs)

`Abstract.CallXT.EvalOXT` records, at each indirect or reference call, that the
resolved callee has the annotated type's counts. This module discharges both
premises from typing, for whole runs: a run of `irExt`-checked code whose Core
configuration is typed in context (`Sim.ContextTyped`) is an `EvalOXT` run
(`evalOXT_of_typed`). The indirect premise comes from the cast
(`CallXT.typeArity_of_cast`); the reference premise from the typed site
(`CallXT.typeArity_of_callRef_site`).

The typing is carried along the run: a terminating prefix's Core run
(`evalOXT_goodE` on its `EvalOXT` derivation) keeps the rest typed in context, by
Core preservation (`Sim.ContextTyped.steps`, `prefix_typed`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

variable {H : Type} {P : Numerics.Profile}

/-- The closed host: no host function answers. -/
abbrev noHostX : HostSemantics H := fun _ _ _ _ => False

/-- **A typed terminating prefix keeps the rest typed.** -/
theorem prefix_typed {C : Abstract.CallRel H} (hC : OracleSoundX P noHostX C) {s s' : Store H}
    {f f' : Frame} {stk stk' : List Val} {es : List Binaryen.BExpr} {rest : List Admin}
    {labels : List Nat} {ret : Nat} {o : Option Nat}
    (d : EvalOXT C s f stk es (s', f', .normal stk')) (hS : StoreChkE irExt s.funcs)
    (hc : chkE irExt s.funcs f.module f.locals.length ret labels (some stk.length) es = some o)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩) :
    Sim.ContextTyped ⟨s', f', vals stk'.reverse ++ rest⟩ ∧ o = some stk'.length ∧
      EvalInvE irExt s f (s', f', .normal stk') := by
  obtain ⟨hA, hCo⟩ := evalOXT_goodE (P := P) (host := noHostX) hC d
  obtain ⟨hok, hinv⟩ := hA hS hc
  obtain ⟨c', oc, hrun, he, hm⟩ := run_of_wp (hCo hS hc)
  have hc' := ends_normal hm he
  subst hc'
  exact ⟨Sim.ContextTyped.steps ht (Steps.append rest hrun), hok, hinv⟩

/-- A typed problem: checked by `irExt` in a checked store, its Core code typed in
context, with valid function and instance types. -/
def TypedX (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  ∃ (rest : List Admin) (labels : List Nat) (ret : Nat) (out : Option Nat),
    StoreChkE irExt s.funcs ∧
    chkE irExt s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩ ∧
    TyFuncs s ∧ TyTypes f.module

theorem chkE_nil_self {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat} {labels : List Nat}
    (o : Option Nat) : chkE irExt F mi nl ret labels o [] = some o := by
  cases o <;> rfl

theorem code_consX (stk : List Val) (e : Binaryen.BExpr) (es : List Binaryen.BExpr) (rest : List Admin) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (e :: es)) ++ rest =
      vals stk.reverse ++ expression (Binaryen.BExpr.lowerList [e]) ++
        (expression (Binaryen.BExpr.lowerList es) ++ rest) := by
  simp [expression, List.append_assoc]

section
variable {C : Abstract.CallRel H} (hC : OracleSoundX P noHostX C) (hCk : KeepsTy C)
include hC hCk

/-- **The continuation after a typed head is typed.** -/
theorem cont_typedX {e : Binaryen.BExpr} {es : List Binaryen.BExpr} {s s₂ : Store H} {f f₂ : Frame}
    {stk stk₂ : List Val} (d : EvalOXT C s f stk [e] (s₂, f₂, .normal stk₂))
    (ht : TypedX s f stk (e :: es)) : TypedX s₂ f₂ stk₂ es := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  have h1' : chkE irExt s.funcs f.module f.locals.length ret labels (some stk.length) [e] = some o :=
    chk_consE.mpr ⟨o, h1, chkE_nil_self o⟩
  rw [code_consX] at hct
  obtain ⟨ht₂, ho, inv⟩ := prefix_typed (P := P) hC d hS h1' hct
  subst ho
  refine ⟨rest, labels, ret, out, inv.1.2.1 hS, chk_inv inv h2, by simpa only [List.append_assoc] using ht₂,
    evalOX_tyFuncs hCk (EvalOXT.forget d) hTF, ?_⟩
  rw [inv.2.1]; exact hTM

omit hC hCk in
/-- The arguments of a typed operator are typed. -/
theorem args_typedX {i : Instr} {args es : List Binaryen.BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (ht : TypedX s f stk (.op i args :: es)) : TypedX s f stk args := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  refine ⟨.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, oa, hS, ha, ?_,
    hTF, hTM⟩
  rw [code_op] at hct
  simpa only [List.append_assoc, List.cons_append] using hct

/-- **The site of an operator, after its typed arguments.** -/
theorem site_typedX {i : Instr} {args es : List Binaryen.BExpr} {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} (d : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
    (ht : TypedX s f stk (.op i args :: es)) :
    ∃ rest, Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ ∧ TyFuncs s₁ ∧
      TyTypes f₁.module ∧ ∃ labels ret o, StoreChkE irExt s.funcs ∧
        flatChkE irExt s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, hf⟩ := chk1_opE h1
  rw [code_op] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args) ++
      (.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨ht₁, ho, inv⟩ := prefix_typed (P := P) hC d hS ha hct'
  subst ho
  refine ⟨_, ht₁, evalOX_tyFuncs hCk (EvalOXT.forget d) hTF, by rw [inv.2.1]; exact hTM,
    labels, ret, o, hS, flatChk_inv inv (hf _ rfl)⟩

end

section
variable {C : Abstract.CallRel H} (hC : OracleSoundX P noHostX C) (hCk : KeepsTy C)

omit hC hCk in
include P in
/-- A block body of a typed problem is typed. -/
theorem block_body_typedX {bt : BlockType} {body es : List Binaryen.BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedX s f stk (.block bt body :: es)) : TypedX s f (stk.take np) body := by
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
theorem loop_body_typedX {bt : BlockType} {body es : List Binaryen.BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedX s f stk (.loop bt body :: es)) : TypedX s f (stk.take np) body := by
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
theorem loop_back_typedX {bt : BlockType} {body es : List Binaryen.BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk vs : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (d : EvalOXT C s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ht : TypedX s f stk (.loop bt body :: es)) :
    TypedX s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hb'' : chkE irExt s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by rw [take_length_of_le hp]; exact hb'
  obtain ⟨hA, hCo⟩ := evalOXT_goodE (P := P) (host := noHostX) hC d
  obtain ⟨hok, inv⟩ := hA hS hb''
  obtain ⟨n, hn, hnv⟩ := hok
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
  subst hn
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (hCo hS hb'')
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
theorem cond_typedX {bt : BlockType} {c t el es : List Binaryen.BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (ht : TypedX s f stk (.if_ bt c t el :: es)) : TypedX s f stk c := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  refine ⟨.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
    expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, oc, hS, hco, ?_, hTF, hTM⟩
  rw [code_if] at hct
  simpa only [List.append_assoc, List.cons_append] using hct

include hC hCk in
/-- **The chosen arm of a typed `if`, after its typed condition, is typed.** -/
theorem arm_typedX {bt : BlockType} {c t el es : List Binaryen.BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool} {np nr : Nat}
    (d : EvalOXT C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hbv : Binaryen.truthy cv = some b)
    (har : Binaryen.arity f₁ bt = some (np, nr)) (ht : TypedX s f stk (.if_ bt c t el :: es)) :
    TypedX s₁ f₁ (stk₁.take np) (if b then t else el) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨hA, -⟩ := evalOXT_goodE (P := P) (host := noHostX) hC d
  obtain ⟨inv1, hp, hb, -⟩ := arity_if_pre (b := b) hS (fun hS' hc' => hA hS' hc') har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq (chk_inv_endsAt inv1 hb)
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c) ++
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨htc, -, -⟩ := prefix_typed (P := P) hC d hS hco hct'
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
theorem types_some_of_flatChk {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TableIdx} {y : TypeIdx} {o : Option Nat}
    (hc : flatChkE irExt F mi nl ret labels h (.callIndirect x y) = some o) :
    (mi.types[y.toNat]?).isSome = true := by
  cases hta : typeArity mi y with
  | none => simp [flatChkE, irExt, hta, extStep] at hc
  | some p =>
    unfold typeArity at hta
    cases hd : mi.types[y.toNat]? with
    | none => simp [hd] at hta
    | some _ => rfl

section
variable {C : Abstract.CallRel H} (hC : OracleSoundX P noHostX C) (hCk : KeepsTy C)
include hC hCk

/-- **Typed runs carry their arity premises.** A run of `irExt`-checked code in a
checked store, whose Core configuration is typed in context, with valid function and
instance types and an oracle keeping them, is an `EvalOXT` run. -/
theorem evalOXT_of_typed {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX C s f stk es r) :
    TypedX s f stk es → EvalOXT C s f stk es r := by
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih => exact fun ht => .argsAbort (ih (args_typedX ht)) hfl
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    exact .callOk dA hfi hty hcall hvs
      (ihk (cont_typedX (P := P) hC hCk (.callOk dA hfi hty hcall hvs .nil) ht))
  | callTrap _ hfi hty hcall iha => exact fun ht => .callTrap (iha (args_typedX ht)) hfi hty hcall
  | callThrow _ hfi hty hcall iha => exact fun ht => .callThrow (iha (args_typedX ht)) hfi hty hcall
  | opOk hi _ hflat _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    exact .opOk hi dA hflat (ihk (cont_typedX (P := P) hC hCk (.opOk hi dA hflat .nil) ht))
  | opStop hi _ hflat hfl iha => exact fun ht => .opStop hi (iha (args_typedX ht)) hflat hfl
  | blockOk har _ hvs _ ihb ihk =>
    intro ht
    have dB := ihb (block_body_typedX (P := P) har ht)
    exact .blockOk har dB hvs (ihk (cont_typedX (P := P) hC hCk (.blockOk har dB hvs .nil) ht))
  | blockBrk har _ ihb => exact fun ht => .blockBrk har (ihb (block_body_typedX (P := P) har ht))
  | blockEsc har _ hfl ihb =>
    exact fun ht => .blockEsc har (ihb (block_body_typedX (P := P) har ht)) hfl
  | loopOk har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedX (P := P) har ht)
    exact .loopOk har dB (ihk (cont_typedX (P := P) hC hCk (.loopOk har dB .nil) ht))
  | loopBack har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedX (P := P) har ht)
    exact .loopBack har dB (ihk (loop_back_typedX (P := P) hC hCk har dB ht))
  | loopBrk har _ ihb => exact fun ht => .loopBrk har (ihb (loop_body_typedX (P := P) har ht))
  | loopEsc har _ hfl ihb =>
    exact fun ht => .loopEsc har (ihb (loop_body_typedX (P := P) har ht)) hfl
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    intro ht
    have dC := ihc (cond_typedX ht)
    have dA := iharm (arm_typedX (P := P) hC hCk dC hb har ht)
    exact .ifOk dC hb har dA hvs (ihk (cont_typedX (P := P) hC hCk (.ifOk dC hb har dA hvs .nil) ht))
  | ifBrk _ hb har _ ihc iharm =>
    intro ht
    have dC := ihc (cond_typedX ht)
    exact .ifBrk dC hb har (iharm (arm_typedX (P := P) hC hCk dC hb har ht))
  | ifEsc _ hb har _ hfl ihc iharm =>
    intro ht
    have dC := ihc (cond_typedX ht)
    exact .ifEsc dC hb har (iharm (arm_typedX (P := P) hC hCk dC hb har ht)) hfl
  | ifAbort _ hfl ihc => exact fun ht => .ifAbort (ihc (cond_typedX ht)) hfl
  | callIndOk _ hres hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, _, hTF, hTM, _, _, _, _, hf⟩ := site_typedX (P := P) hC hCk dA ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChk hf)
    exact .callIndOk dA hres hfi hty hy hcall hvs
      (ihk (cont_typedX (P := P) hC hCk (.callIndOk dA hres hfi hty hy hcall hvs .nil) ht))
  | callIndRes _ hres iha => exact fun ht => .callIndRes (iha (args_typedX ht)) hres
  | callIndStop _ hres hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, _, hTF, hTM, _, _, _, _, hf⟩ := site_typedX (P := P) hC hCk dA ht
    exact .callIndStop dA hres hfi hty
      (typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChk hf)) hcall hfl
  | callRefOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨rest, hsite, hTF, hTM, -⟩ := site_typedX (P := P) hC hCk dA ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    exact .callRefOk dA hfi hty hy hcall hvs
      (ihk (cont_typedX (P := P) hC hCk (.callRefOk dA hfi hty hy hcall hvs .nil) ht))
  | callRefNull _ iha => exact fun ht => .callRefNull (iha (args_typedX ht))
  | callRefStop _ hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨rest, hsite, hTF, hTM, -⟩ := site_typedX (P := P) hC hCk dA ht
    exact .callRefStop dA hfi hty (typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)) hcall hfl
  | tail _ hres hfi hty hcall hfl iha =>
    exact fun ht => .tail (iha (args_typedX ht)) hres hfi hty hcall hfl
  | tailRes _ hres iha => exact fun ht => .tailRes (iha (args_typedX ht)) hres

end

end Silmaril.Wasm.Interp
