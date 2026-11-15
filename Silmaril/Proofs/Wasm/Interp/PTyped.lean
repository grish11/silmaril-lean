module

public import Silmaril.Proofs.Wasm.Interp.PDivCore
public import Silmaril.Proofs.Wasm.Interp.XNoOutcome
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Abstract.XRecursion.Thms

/-!
# Typed problems with exceptions and pending tail calls (F5, proofs)

`TypedP tags`: `TypedT` for the exception checker `ehExt tags`, with the tag invariants
(`TagsOk tags`): checked by `ehExt tags` in a checked store, the Core code typed in context, the
instance's types valid. The function types of the store come from the typing (`tyFuncs_of_ctx`).
Typing is carried along closed runs with pending tail calls as in `TypedT`, by the forward
simulation `evalOXP_closed_good` (`prefix_typedP`, `cont_typedP`, …); a `try_table` body is
typed inside its handler and label (`try_body_typedP`).

A typed call (`CallTypedP`): a checked call whose `call_ref` form is typed in context. Its body
is a typed problem (`callee_typedP`), and so is the call of the callee of a pending tail call at
the end of its body (`callTyped_tail`): Core makes it, from the typed call, by leaving the
body's label and the frame.

Facts read off typing: a typed `throw_ref` operand is null or an exception reference
(`throwRef_top`); a checked `throw` names a tag of the store with its fields (`tag_of_tagFields`).
The closure's answers keep the store's functions (`closedCallXP_funcsP`), and a checked call's
answer returns, traps or throws (`calleeP_flow`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP

variable {H : Type}

/-! ## Functions are kept -/

/-- `EvalOXP` keeps the store's functions when its oracle does. -/
theorem evalOXP_funcs {C : Abstract.CallRel H}
    (hC : ∀ s a args out, C s a args out → out.1.funcs = s.funcs) {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP C s f stk es r) : r.1.funcs = s.funcs := by
  induction h with
  | nil => rfl
  | argsAbort _ _ ih => exact ih
  | callOk _ _ _ hcall _ _ ih₁ ih₂ => exact ih₂.trans ((hC _ _ _ _ hcall).trans ih₁)
  | callTrap _ _ _ hcall ih => exact (hC _ _ _ _ hcall).trans ih
  | callThrow _ _ _ hcall ih => exact (hC _ _ _ _ hcall).trans ih
  | opOk _ _ hflat _ ih₁ ih₂ =>
    exact ih₂.trans ((Abstract.XRecursion.evalFlat_funcs hflat).trans ih₁)
  | opStop _ _ hflat _ ih => exact (Abstract.XRecursion.evalFlat_funcs hflat).trans ih
  | blockOk _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | blockBrk _ _ ih => exact ih
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | loopBack _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | loopBrk _ _ ih => exact ih
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ _ _ ih₁ ih₂ ih₃ => exact ih₃.trans (ih₂.trans ih₁)
  | ifBrk _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ifEsc _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ifAbort _ _ ih => exact ih
  | callIndOk _ _ _ _ _ hcall _ _ ih₁ ih₂ => exact ih₂.trans ((hC _ _ _ _ hcall).trans ih₁)
  | callIndRes _ _ ih => exact ih
  | callIndStop _ _ _ _ _ hcall _ ih => exact (hC _ _ _ _ hcall).trans ih
  | callRefOk _ _ _ _ hcall _ _ ih₁ ih₂ => exact ih₂.trans ((hC _ _ _ _ hcall).trans ih₁)
  | callRefNull _ ih => exact ih
  | callRefStop _ _ _ _ hcall _ ih => exact (hC _ _ _ _ hcall).trans ih
  | tail _ _ _ _ _ ih => exact ih
  | tailRes _ _ ih => exact ih
  | throw _ _ _ _ ih => exact ih
  | throwRefNull _ ih => exact ih
  | throwRefExn _ ih => exact ih
  | tryOk _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | tryBrk _ _ ih => exact ih
  | tryEsc _ _ _ _ ih => exact ih
  | tryCatch _ _ _ ih => exact ih
  | tryRethrow _ _ _ ih => exact ih

/-- The closure with pending tail calls keeps the store's functions. -/
theorem closedCallXP_funcsP :
    ∀ (s : Store H) a args out, closedCallXP s a args out → out.1.funcs = s.funcs := by
  have : (closedCallXP : Abstract.CallRel H) ≤ fun s _ _ out => out.1.funcs = s.funcs := by
    refine OrderHom.lfp_le _ ?_
    rintro s a args out ⟨fi, fn, ps, rs, f₂, s₁, o, -, -, -, d, hfr⟩
    have h₁ := evalOXP_funcs (fun _ _ _ _ h => h) d
    cases hfr with
    | flow => exact h₁
    | tail hcall _ => exact hcall.trans h₁
  exact fun s a args out h => this s a args out h

theorem wasmFuncsT_runP {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × POut} (d : EvalOXP closedCallXP s f stk es r) (hW : WasmFuncsT s) :
    WasmFuncsT r.1 :=
  fun a fi h => hW a fi (evalOXP_funcs closedCallXP_funcsP d ▸ h)

/-- **The closure answers a call** by a run of its body and leaving the frame. -/
theorem closedCallXP_of_body {s s₁ : Store H} {a : Nat} {args : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {f₂ : Frame} {o : POut}
    {out : Store H × Binaryen.Flow} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (d : EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₁, f₂, o))
    (hfr : FrameP closedCallXP (s₁, o) out) : closedCallXP s a args out := by
  rw [closedCallXP_fixpoint]
  exact ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩

/-- **A checked call's closed answer returns, traps or throws.** -/
theorem calleeP_flow {tags : List TagInst} {s s₂ : Store H} {a : Nat} {us : List Val}
    {fl : Binaryen.Flow} (hcc : CallChkP tags s a us) (h : closedCallXP s a us (s₂, fl)) :
    (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt := by
  obtain ⟨hS, hts, fi, ps, rs, hfi, hty, hn⟩ := hcc
  obtain ⟨-, hsnd⟩ := closedCallXP_sound (P := Pd) (host := noHostX) tags s a us (s₂, fl) h hts
  obtain ⟨⟨ob, -, hok, -⟩, -⟩ := hsnd {} fi ps rs (.callRefType fi.type) hS hfi hty hn trivial
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | t
  · exact .inl ⟨w, rfl⟩
  · exact .inl ⟨w, rfl⟩
  · obtain ⟨m, hm, -⟩ := hok
    simp at hm
  · exact .inl ⟨w, rfl⟩
  · exact .inr trivial
  · exact .inr trivial

/-! ## Typed problems -/

/-- The function types of a store whose configuration is typed in context. -/
theorem tyFuncs_of_ctx {s : Store H} {f : Frame} {c : List Admin}
    (h : Sim.ContextTyped ⟨s, f, c⟩) : TyFuncs s := by
  obtain ⟨-, -, -, hsok, -, -, -⟩ := Sim.ContextTyped.fragment_types h
  exact fun a fi hfi => PC.StoreOk.func_tyOk hsok hfi

/-- **A typed problem**: checked by `ehExt tags` in a checked store, its Core code typed in
context, with valid instance types, in a store with the tag invariants. -/
def TypedP (tags : List TagInst) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) : Prop :=
  ∃ (rest : List Admin) (labels : List Nat) (ret : Nat) (out : Option Nat),
    StoreChkE (ehExt tags) s.funcs ∧
    chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩ ∧
    TyTypes f.module ∧ TagsOk tags s

section Typed

variable {tags : List TagInst}

theorem TypedP.checked {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    (ht : TypedP tags s f stk es) : CheckedP tags s f stk es := by
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  exact ⟨labels, ret, out, hS, hc, hts⟩

/-- **A typed terminating prefix keeps the rest typed.** -/
theorem prefix_typedP {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es : List Binaryen.BExpr} {rest : List Admin} {labels : List Nat} {ret : Nat} {o : Option Nat}
    (d : EvalOXP closedCallXP s f stk es (s', f', .flow (.normal stk')))
    (hS : StoreChkE (ehExt tags) s.funcs)
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some o)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩)
    (hts : TagsOk tags s) :
    Sim.ContextTyped ⟨s', f', vals stk'.reverse ++ rest⟩ ∧ o = some stk'.length ∧
      EvalInvE (ehExt tags) s f (s', f', .trap) ∧ TagsOk tags s' := by
  obtain ⟨hrun, ho, hinv, hts'⟩ := prefix_runP (P := Pd) (host := noHostX) d hS hc hts
  exact ⟨Sim.ContextTyped.steps ht (Steps.append rest hrun), ho, hinv, hts'⟩

/-- **The continuation after a typed head is typed.** -/
theorem cont_typedP {e : Binaryen.BExpr} {es : List Binaryen.BExpr} {s s₂ : Store H}
    {f f₂ : Frame} {stk stk₂ : List Val}
    (d : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂)))
    (ht : TypedP tags s f stk (e :: es)) : TypedP tags s₂ f₂ stk₂ es := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  have h1' : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) [e] =
      some o := chk_consE.mpr ⟨o, h1, chkE_nil_selfP o⟩
  rw [code_consX] at hct
  obtain ⟨ht₂, ho, inv, hts₂⟩ := prefix_typedP d hS h1' hct hts
  subst ho
  exact ⟨rest, labels, ret, out, storeChk_inv inv hS, chk_inv inv h2,
    by simpa only [List.append_assoc] using ht₂, by rw [inv.2.1]; exact hTM, hts₂⟩

/-- The arguments of a typed operator are typed. -/
theorem args_typedP {i : Instr} {args es : List Binaryen.BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (ht : TypedP tags s f stk (.op i args :: es)) : TypedP tags s f stk args := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  refine ⟨.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, oa, hS, ha, ?_,
    hTM, hts⟩
  rw [code_op] at hct
  simpa only [List.append_assoc, List.cons_append] using hct

/-- **The site of an operator, after its typed arguments.** -/
theorem site_typedP {i : Instr} {args es : List Binaryen.BExpr} {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} (d : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal stk₁)))
    (ht : TypedP tags s f stk (.op i args :: es)) :
    ∃ rest, Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ ∧ TyFuncs s₁ ∧
      TyTypes f₁.module ∧ StoreChkE (ehExt tags) s₁.funcs ∧ TagsOk tags s₁ ∧ ∃ labels ret o,
        flatChkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, hf⟩ := chk1_opE h1
  rw [code_op] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args) ++
      (.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨ht₁, ho, inv, hts₁⟩ := prefix_typedP d hS ha hct' hts
  subst ho
  have ht₁' : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++
      .plain i :: (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.cons_append] using ht₁
  exact ⟨_, ht₁', tyFuncs_of_ctx ht₁', by rw [inv.2.1]; exact hTM, storeChk_inv inv hS, hts₁,
    labels, ret, o, flatChk_inv inv (hf _ rfl)⟩

/-- A block body of a typed problem is typed. -/
theorem block_body_typedP {bt : BlockType} {body es : List Binaryen.BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedP tags s f stk (.block bt body :: es)) : TypedP tags s f (stk.take np) body := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  rw [code_block] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := steps_enter (P := Pd) (host := noHostX) (s := s) (f := f) hp
    (step_block (B := Binaryen.BExpr.lowerList body) har) (expression (Binaryen.BExpr.lowerList es) ++ rest)
  have hin := Sim.ContextTyped.label (Sim.ContextTyped.steps hct' hst)
  refine ⟨[], nr :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', ?_, hTM, hts⟩
  simpa only [List.append_nil] using hin

/-- A loop body of a typed problem is typed. -/
theorem loop_body_typedP {bt : BlockType} {body es : List Binaryen.BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedP tags s f stk (.loop bt body :: es)) : TypedP tags s f (stk.take np) body := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  rw [code_loop] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := steps_enter (P := Pd) (host := noHostX) (s := s) (f := f) hp
    (step_loop (B := Binaryen.BExpr.lowerList body) har) (expression (Binaryen.BExpr.lowerList es) ++ rest)
  have hin := Sim.ContextTyped.label (Sim.ContextTyped.steps hct' hst)
  refine ⟨[], np :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', ?_, hTM, hts⟩
  simpa only [List.append_nil] using hin

/-- A `try_table` body of a typed problem is typed, inside its handler and label. -/
theorem try_body_typedP {bt : BlockType} {cs : List Catch} {body es : List Binaryen.BExpr}
    {s : Store H} {f : Frame} {stk : List Val} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (ht : TypedP tags s f stk (.tryTable bt cs body :: es)) : TypedP tags s f (stk.take np) body := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  rw [code_tryTable] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := steps_try_enter (P := Pd) (host := noHostX) (s := s) (f := f) (cs := cs)
    (B := Binaryen.BExpr.lowerList body) har hp (expression (Binaryen.BExpr.lowerList es) ++ rest)
  have hin := Sim.ContextTyped.handler (Sim.ContextTyped.steps hct' hst)
  have hin' : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ :=
    Sim.ContextTyped.label (n := nr) (cont := []) (vs := []) (rest := []) (by simpa [vals] using hin)
  refine ⟨[], nr :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', ?_, hTM, hts⟩
  simpa only [List.append_nil] using hin'

/-- **The next iteration of a typed loop whose body branched back is typed.** -/
theorem loop_back_typedP {bt : BlockType} {body es : List Binaryen.BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk vs : List Val} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (d : EvalOXP closedCallXP s f (stk.take np) body (s₁, f₁, .flow (.brk 0 vs)))
    (ht : TypedP tags s f stk (.loop bt body :: es)) :
    TypedP tags s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hb'' : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by rw [take_length_of_le hp]; exact hb'
  obtain ⟨ht₁, hA, hG⟩ := evalOXP_closed_good (P := Pd) (host := noHostX) d hts
  obtain ⟨hok, inv, -⟩ := hA hS hb''
  obtain ⟨n', hn', hnv⟩ := hok
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hn'
  subst hn'
  have hw₀ : WP Pd noHostX s f (xcode (stk.take np) body) (MatchP (s₁, f₁, .flow (.brk 0 vs))) :=
    hG hS hb''
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (wp_of_wpP (fun h => by cases h) hw₀)
  rw [code_loop] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  have hst := tg_loop_back (P := Pd) (host := noHostX)
    (rest := expression (Binaryen.BExpr.lowerList es) ++ rest) har hp hrun he hm hnv
  have hnew := Sim.ContextTyped.steps hct' hst.to_reflTransGen
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  refine ⟨rest, labels, ret, out, storeChk_inv inv hS, by rw [hlen]; exact chk_inv inv hc, ?_,
    by rw [inv.2.1]; exact hTM, ht₁⟩
  rw [code_loop]
  simpa only [List.append_assoc, List.cons_append] using hnew

/-- The condition of a typed `if` is typed. -/
theorem cond_typedP {bt : BlockType} {c t el es : List Binaryen.BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (ht : TypedP tags s f stk (.if_ bt c t el :: es)) : TypedP tags s f stk c := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  refine ⟨.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
    expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, oc, hS, hco, ?_, hTM, hts⟩
  rw [code_if] at hct
  simpa only [List.append_assoc, List.cons_append] using hct

/-- **The chosen arm of a typed `if`, after its typed condition, is typed.** -/
theorem arm_typedP {bt : BlockType} {c t el es : List Binaryen.BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool} {np nr : Nat}
    (d : EvalOXP closedCallXP s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))))
    (hbv : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (ht : TypedP tags s f stk (.if_ bt c t el :: es)) :
    TypedP tags s₁ f₁ (stk₁.take np) (if b then t else el) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨-, hA, -⟩ := evalOXP_closed_good (P := Pd) (host := noHostX) d hts
  obtain ⟨inv1, hp, hb, -⟩ := arity_if_pre (b := b) hS
    (fun hS' hc' => (arityE_of_arityP hA) hS' hc') har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq (chk_inv_endsAt inv1 hb)
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if] at hct
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c) ++
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.append_assoc, List.cons_append] using hct
  obtain ⟨htc, -, -, hts₁⟩ := prefix_typedP d hS hco hct' hts
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hbv
  let R := expression (Binaryen.BExpr.lowerList es) ++ rest
  have hif : Steps Pd noHostX ⟨s₁, f₁, vals (Val.i32 c₀ :: stk₁).reverse ++
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
      simpa using Relation.ReflTransGen.single (Step.ctx (P := Pd) (host := noHostX) stk₁.reverse R
        (Step.ifFalse (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
          (b₂ := Binaryen.BExpr.lowerList el)))
    · have h1 : (c₀ != 0) = true := by simpa using h0
      simp only [h1, ↓reduceIte]
      simpa using Relation.ReflTransGen.single (Step.ctx (P := Pd) (host := noHostX) stk₁.reverse R
        (Step.ifTrue (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
          (b₂ := Binaryen.BExpr.lowerList el) h0))
  have hst := steps_enter (P := Pd) (host := noHostX) (s := s₁) (f := f₁) hp
    (step_block (B := Binaryen.BExpr.lowerList (if (c₀ != 0) then t else el)) har) R
  have hin := Sim.ContextTyped.label (Sim.ContextTyped.steps (Sim.ContextTyped.steps htc hif) hst)
  refine ⟨[], nr :: labels, ret, ob, storeChk_inv inv1 hS,
    by rw [take_length_of_le hp]; exact hb', ?_, by rw [inv1.2.1]; exact hTM, hts₁⟩
  simpa only [List.append_nil, apply_ite Binaryen.BExpr.lowerList] using hin

end Typed

/-! ## Typed calls -/

/-- **A typed call**: a checked call whose `call_ref` form is typed in context. -/
def CallTypedP (tags : List TagInst) (s : Store H) (a : Nat) (args : List Val) : Prop :=
  CallChkP tags s a args ∧ ∃ (f : Frame) (c : Admin) (pre : List Val) (rest : List Admin),
    c.IsCallRef ∧ Sim.ContextTyped ⟨s, f, callCode pre args a c rest⟩

section Calls

variable {tags : List TagInst}

/-- **A typed call's body is a typed problem.** -/
theorem callee_typedP {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H} {fn : Func}
    (hct : CallTypedP tags s a args) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    TypedP tags s (Frame.forCall fi.module args fn.locals) [] (Binaryen.liftInstrs fn.body) := by
  obtain ⟨⟨hS, hts, fi', ps, rs, hfi', hty, hn⟩, f, c, pre, rest, hcr, hctx⟩ := hct
  rw [hfi] at hfi'; cases hfi'
  have e : callCode pre args a c rest =
      vals (pre ++ args).reverse.reverse ++ [.ref (.func a), c] ++ rest := by
    simp [callCode]
  rw [e] at hctx
  have hE := entry_of_ref_site (P := Pd) hctx hcr hfi hty (by simp; omega)
  have htk : ((pre ++ args).reverse.take ps.length).reverse = args := by
    rw [List.reverse_append, List.take_left' (by simp; omega), List.reverse_reverse]
  rw [htk] at hE
  have hct := hE fi fn hfi hcode
  obtain ⟨-, -, -, hsok, -, -, -⟩ := Sim.ContextTyped.fragment_types hct
  obtain ⟨ob, hb⟩ := body_chkP hS hfi hcode hty hn
  exact ⟨[], [rs.length], rs.length, ob, hS, hb,
    by simpa [vals, Binaryen.lowerList_liftInstrs] using hct, tyTypes_of_storeOkX hsok hfi hcode, hts⟩

/-- **The tail callee of a typed call's body is a typed call**: Core makes it from the typed call,
past the body's pending tail call. -/
theorem callTyped_tail {s s₁ : Store H} {f₂ : Frame} {a a' n : Nat} {args args' : List Val}
    {fi : FuncInst H} {fn : Func} (hct : CallTypedP tags s a args) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn)
    (hbody : EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₁, f₂, .tail a' args' n)) :
    CallTypedP tags s₁ a' args' := by
  obtain ⟨⟨hS, hts, fi', ps, rs, hfi', hty, hn⟩, f, c, pre, rest, hcr, hctx⟩ := hct
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨c', hc', htg, hcc'⟩ := call_tail_stepsP (P := Pd) (host := noHostX) hS hts hfi hcode hty
    hn hbody f hcr pre rest
  exact ⟨hcc', f, c', pre, rest, hc', Sim.ContextTyped.steps hctx htg.to_reflTransGen⟩

/-- A typed `call x` site makes a typed call. -/
theorem callTyped_call {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {x : FuncIdx} {a : Nat}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hsite : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk₁.length) (hS₁ : StoreChkE (ehExt tags) s₁.funcs) (hts₁ : TagsOk tags s₁) :
    CallTypedP tags s₁ a (stk₁.take ps.length).reverse := by
  obtain ⟨hx, hf'⟩ := func?_inv hfi
  have hst := Step.ctx (P := Pd) (host := noHostX) stk₁.reverse rest (Step.call (s := s₁) (f := f₁) hx hf')
  have e : vals stk₁.reverse ++ .plain (.call x) :: rest =
      vals stk₁.reverse ++ [.plain (.call x)] ++ rest := by simp
  rw [e] at hsite
  have h2 := Sim.ContextTyped.step hsite hst
  rw [callCode_split stk₁ ps.length] at h2
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  exact ⟨⟨hS₁, hts₁, fi, ps, rs, hf', hty, hlen⟩, f₁, .callRefType fi.type, _, rest, trivial, h2⟩

/-- A typed, resolved `call_indirect` site makes a typed call. -/
theorem callTyped_ind {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
    {ad : AddrType} {j : BitVec ad.intType.width} {fa : Nat} {rest : List Admin} {fi : FuncInst H}
    {ps rs : List Validation.CValType}
    (hsite : Sim.ContextTyped ⟨s₁, f₁, vals (.num ⟨.int ad.intType, j⟩ :: stk₁).reverse ++
      .plain (.callIndirect x y) :: rest⟩)
    (hres : Abstract.CallRes.IndRes s₁ f₁ x y ad j (some fa)) (hfi : s₁.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hS₁ : StoreChkE (ehExt tags) s₁.funcs) (hts₁ : TagsOk tags s₁) :
    CallTypedP tags s₁ fa (stk₁.take ps.length).reverse := by
  have hst := Steps.ctx (P := Pd) (host := noHostX) stk₁.reverse rest
    (Abstract.CallRes.steps_callIndirect_func hres)
  have e : vals (.num ⟨.int ad.intType, j⟩ :: stk₁).reverse ++ .plain (.callIndirect x y) :: rest =
      vals stk₁.reverse ++ [aconst ad j, .plain (.callIndirect x y)] ++ rest := by
    rw [List.reverse_cons, vals_append, Abstract.CallRes.aconst_eq]; simp
  rw [e] at hsite
  have h2 := Sim.ContextTyped.steps hsite hst
  rw [callCode_split stk₁ ps.length] at h2
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  exact ⟨⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hlen⟩, f₁, .plain (.callRef y), _, rest, trivial, h2⟩

/-- A typed `call_ref` site on a function reference makes a typed call. -/
theorem callTyped_ref {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {y : TypeIdx} {fa : Nat}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hsite : Sim.ContextTyped ⟨s₁, f₁, vals (.ref (.func fa) :: stk₁).reverse ++
      .plain (.callRef y) :: rest⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk₁.length) (hS₁ : StoreChkE (ehExt tags) s₁.funcs) (hts₁ : TagsOk tags s₁) :
    CallTypedP tags s₁ fa (stk₁.take ps.length).reverse := by
  have e : vals (.ref (.func fa) :: stk₁).reverse ++ .plain (.callRef y) :: rest =
      vals stk₁.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ rest := by simp [vals]; rfl
  rw [e, callCode_split stk₁ ps.length] at hsite
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  exact ⟨⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hlen⟩, f₁, .plain (.callRef y), _, rest, trivial, hsite⟩

end Calls

/-! ## Exceptions, read off typing and the check -/

open Silmaril.Wasm.Validation in
/-- `throw_ref` on a typed reference: null or an exception address (`throwRef_inv` without the
frame typing, which its proof does not use). -/
theorem throwRef_inv' {s : Store H} {Δ : TypeCtx} {r : Ref}
    (hv : ValTo s Δ (.ref r) (Ty.refT true (.abs .exn))) : r = .null ∨ ∃ a, r = .exn a := by
  obtain ⟨t₀, hv0, hc⟩ := hv
  have key := rtg_down (S := fun t : CValType => t = .botv ∨
      ∃ n h, t = .refv (.ref n h) ∧ exnDown h = true) (fun a b hab hb => by
      rcases hb with rfl | ⟨n, h, rfl, hd⟩
      · (cases hab; simp)
      · cases hab with
        | refv h' =>
          cases h' with
          | refNonNull hh => exact .inr ⟨_, _, rfl, (Sub.exn_aux hh).1 hd⟩
          | refNull hh => exact .inr ⟨_, _, rfl, (Sub.exn_aux hh).1 hd⟩
        | botv => exact .inl rfl) hc (.inr ⟨true, _, rfl, rfl⟩)
  rcases key with rfl | ⟨n, h, rfl, hd⟩
  · cases hv0
  · cases hv0 with
    | ref hr => exact RefOk.exn_inv hr _ _ rfl hd

open Silmaril.Wasm.Validation in
/-- **The operand of a typed `throw_ref`**: the top of the stack is a null or an exception
reference. -/
theorem throwRef_top {s : Store H} {f : Frame} {stk : List Val} {rest : List Admin}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain .throwRef :: rest⟩) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧ (r = .null ∨ ∃ a, r = .exn a) := by
  have typed : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain .throwRef]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using ht)
  obtain ⟨C, ts, xs, hs, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, hi, _⟩ :=
    AdminsOk.split hcode hC (vals stk.reverse) [.plain .throwRef] rfl (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi
  obtain ⟨t₁, hpar⟩ : ∃ t₁, it.params = t₁ ++ [.refT true (.abs .exn)] := by
    rcases ha.plain_cases with hinstr | ⟨-, t₁, t₂, xs', rfl, -⟩
    · generalize C.initLocals xs₁ = C₀ at hinstr
      cases hinstr with
      | throwRef _ => exact ⟨_, rfl⟩
      | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
        cases h
    · exact ⟨t₁, rfl⟩
  have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
  have h := hsub'.1
  simp only [hpar, ← List.append_assoc] at h
  obtain ⟨l', tr, rfl, -, hr⟩ := forall₂_lastR h
  simp only [List.nil_append] at hsub
  obtain ⟨p', pr, rfl, -, hs₁⟩ := forall₂_lastR hsub
  obtain ⟨vs', v, hve, -, hvr⟩ := forall₂_lastR hv
  have hstk : stk = v :: vs'.reverse := by
    have := congrArg List.reverse hve
    simpa using this
  rw [hΔ] at hr
  have hto : ValTo s C.toTypeCtx v (Ty.refT true (.abs .exn)) :=
    ⟨pr, hvr, (Relation.ReflTransGen.single hs₁).tail hr⟩
  obtain ⟨r, rfl⟩ := hto.ref
  exact ⟨r, vs'.reverse, hstk, throwRef_inv' hto⟩

/-- What the check of `throw x` says: the tag's field count, at most the stack height. -/
theorem throw_chk {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TagIdx} {o : Option Nat}
    (hf : flatChkE (ehExt tags) F mi nl ret labels h (.throw x) = some o) :
    ∃ p, tagFields tags mi x = some p ∧ p ≤ h := by
  cases htf : tagFields tags mi x with
  | none => simp [flatChkE, ehExt, htf, extStep] at hf
  | some p =>
    refine ⟨p, rfl, ?_⟩
    simp only [flatChkE, ehExt, htf, Option.map_some, extStep] at hf
    by_contra hlt
    simp [hlt] at hf

/-- **A checked `throw x` names a tag of the store**, of a function type with no results and
the checked field count. -/
theorem tag_of_tagFields {tags : List TagInst} {s : Store H} {f : Frame} {x : TagIdx} {p : Nat}
    (hT : s.tags = tags) (h : tagFields tags f.module x = some p) :
    ∃ (ta : Nat) (ti : TagInst) (ts : Validation.Ty (.list .val)), s.tag? f x = some (ta, ti) ∧
      Validation.Expand ti.type (.func ts .nil) ∧ ts.length = p := by
  simp only [tagFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ta, hta, ti, hti, h⟩ := h
  split at h
  · rename_i ps hft
    cases h
    unfold Validation.DefType.funcType? at hft
    split at hft
    · rename_i ps' rs' he
      obtain ⟨rfl, hrs⟩ := Prod.mk.inj (Option.some.inj hft)
      have hnil : rs' = .nil := by rw [← Validation.Ty.ofList_toList rs', hrs]; rfl
      subst hnil
      refine ⟨ta, ti, ps', ?_, Validation.Expand.iff.mpr he, by simp [Validation.Ty.length]⟩
      simp [Store.tag?, hta, hT, hti]
    · cases hft
  · cases h

end Silmaril.Wasm.Interp
