module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP.Glue

/-!
# Logged prefixes into a hole: reaches and divergence after a log (proofs)

`CtxRun T`: from checked code on a checked store with the tag invariants, a Core run with the
resolved log into a hole satisfying `T`, inside an active context. Its cases (`ctxRun_args`,
`ctxRun_block`, `ctxRun_head`, …) are the constructors shared by `ReachLXP`, `LogDivXP` and
`InfLXP`:

* `reachLXP_fwd`: a logged reach is a Core run to the reached call, in its `call_ref` form, a
  checked call (`CallChkP`);
* `logDivXP_fwd`: logged host-free divergence is a Core run to a checked problem that diverges
  host-free (`EvalDivXP`, `CheckedP`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP)
open Shape (SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

section Enter

variable {tags : List TagInst} {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
  {es body : List Binaryen.BExpr} {bt : BlockType} {np nr : Nat} {labels : List Nat} {ret : Nat}
  {out : Option Nat}

/-- **Entering a block**: the body's check, and the host-free entry into its label. -/
theorem block_enter (har : Binaryen.arity f bt = some (np, nr))
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.block bt body :: es) = some out) :
    (∃ ob, chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob) ∧
      Steps P NH ⟨s, f, xcode stk (.block bt body :: es)⟩
        (Sim.ActiveCtx.plug (.label nr [] (stk.drop np).reverse
          (expression (Binaryen.BExpr.lowerList es)) .hole) ⟨s, f, xcode (stk.take np) body⟩) := by
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hchk
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  refine ⟨⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  simp only [xcode, code_block, Sim.ActiveCtx.plug]
  exact steps_enter (P := P) (host := NH) hp (step_block har) _

/-- **Entering a loop**: the body's check, and the host-free entry into its label. -/
theorem loop_enter (har : Binaryen.arity f bt = some (np, nr))
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out) :
    (∃ ob, chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob) ∧
      Steps P NH ⟨s, f, xcode stk (.loop bt body :: es)⟩
        (Sim.ActiveCtx.plug (.label np [.loop bt (Binaryen.BExpr.lowerList body)]
          (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) .hole)
          ⟨s, f, xcode (stk.take np) body⟩) := by
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  refine ⟨⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  simp only [xcode, code_loop, Sim.ActiveCtx.plug]
  exact steps_enter (P := P) (host := NH) hp (step_loop har) _

/-- **Entering a `try_table`**: the body's check, and the host-free entry into its handler and
label. -/
theorem try_enter {cs : List Catch} (har : Binaryen.arity f bt = some (np, nr))
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.tryTable bt cs body :: es) = some out) :
    (∃ ob, chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob) ∧
      Steps P NH ⟨s, f, xcode stk (.tryTable bt cs body :: es)⟩
        (Sim.ActiveCtx.plug (.label nr [] [] [] (.handler nr cs (stk.drop np).reverse
          (expression (Binaryen.BExpr.lowerList es)) .hole)) ⟨s, f, xcode (stk.take np) body⟩) := by
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hchk
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  refine ⟨⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  simp only [xcode, code_tryTable, Sim.ActiveCtx.plug]
  simpa [vals] using steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp
    (B := Binaryen.BExpr.lowerList body) (expression (Binaryen.BExpr.lowerList es))

end Enter

section Calls

variable {tags : List TagInst} {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
  {args es : List Binaryen.BExpr} {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
  {labels : List Nat} {ret : Nat} {out : Option Nat} {a fa : Nat} {fi : FuncInst H}
  {ps rs : List Validation.CValType}

theorem vals_nil : vals ([] : List Val) = [] := rfl

theorem vals_split (stk₁ : List Val) (n : Nat) :
    vals stk₁.reverse = vals (stk₁.drop n).reverse ++ vals (stk₁.take n).reverse := by
  conv_lhs => rw [← List.take_append_drop n stk₁]
  simp [vals]

/-- **The arguments of `call x`, then its `call_ref` form on the callee**: a checked call. -/
theorem call_glue (hH : NativeHostSlice host) (hE : HostSliceE tags host) {x : FuncIdx}
    (h : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hc : Cons host q)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.call x) args :: es) = some out) :
    EvRun P host ⟨s, f, xcode stk (.op (.call x) args :: es)⟩ q
        ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse a
          (.callRefType fi.type) (expression (Binaryen.BExpr.lowerList es))⟩ ∧
      CallChkP tags s₁ a (stk₁.take ps.length).reverse := by
  obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨hrun, t₁, hA⟩ := normal_run (P := P) hH hE h hq hc hts hS ha
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS hA hfi hty hchk
  have hfa := Silmaril.Wasm.Interp.funcs_of_func? hfi
  have hfa' := hfi
  refine ⟨?_, storeChk_inv inv1 hS, t₁, fi, ps, rs, hfa, hty, take_rev_length hp⟩
  let E := expression (Binaryen.BExpr.lowerList es)
  have r1 := evRun_ctx [] (.plain (.call x) :: E) hrun
  rw [vals_nil, List.nil_append, List.nil_append] at r1
  have h₁ : Step P NH ⟨s₁, f₁, vals stk₁.reverse ++ (.plain (.call x) :: E)⟩
      ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse a
        (.callRefType fi.type) E⟩ := by
    have := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      ((stk₁.drop ps.length).reverse ++ (stk₁.take ps.length).reverse) E
      (Step.call (s := s₁) (f := f₁) (module_of_func? hfa') hfa)
    rw [vals_split stk₁ ps.length]
    simpa [Interp.callCode, vals, List.append_assoc] using this
  rw [show xcode stk (.op (.call x) args :: es) = xcode stk args ++ (.plain (.call x) :: E) from
    code_op stk _ args es]
  have := evRun_trans r1 (evRun_of_free (.single h₁))
  rwa [List.append_nil] at this

/-- **The arguments of a resolved `call_indirect` or of `call_ref` on a function reference, then
the `call_ref` form on the callee**: a checked call. -/
theorem ir_glue (hH : NativeHostSlice host) (hE : HostSliceE tags host) {top : Val} {i : Instr}
    {y : TypeIdx} (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (h : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal (top :: stk₁))))
    (hpre : Steps P NH ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hc : Cons host q)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op i args :: es) = some out) :
    EvRun P host ⟨s, f, xcode stk (.op i args :: es)⟩ q
        ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse fa
          (.plain (.callRef y)) (expression (Binaryen.BExpr.lowerList es))⟩ ∧
      CallChkP tags s₁ fa (stk₁.take ps.length).reverse := by
  obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨hrun, t₁, hA⟩ := normal_run (P := P) hH hE h hq hc hts hS ha
  obtain ⟨inv1, hp, -⟩ := arity_ir_preP hS hA hi hy hchk
  refine ⟨?_, storeChk_inv inv1 hS, t₁, fi, ps, rs, hfi, hty, take_rev_length hp⟩
  let E := expression (Binaryen.BExpr.lowerList es)
  have r1 := evRun_ctx [] (.plain i :: E) hrun
  rw [vals_nil, List.nil_append, List.nil_append] at r1
  have st₁ := Steps.ctx (P := P) (host := NH) stk₁.reverse E hpre
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  have e' : vals stk₁.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ E =
      Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse fa
        (.plain (.callRef y)) E := by
    rw [vals_split stk₁ ps.length]
    simp [Interp.callCode]
  rw [show xcode stk (.op i args :: es) = xcode stk args ++ (.plain i :: E) from
    code_op stk i args es, ← e']
  have st₁' : Steps P NH ⟨s₁, f₁, vals (top :: stk₁).reverse ++ .plain i :: E⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ E⟩ := by
    rw [e]; exact st₁
  have := evRun_trans r1 (evRun_of_free st₁')
  rwa [List.append_nil] at this

end Calls

/-! ## Runs into a hole -/

/-- **A Core run into a hole**: from checked code on a checked store with the tag invariants, a
Core run with the log `q` into a hole satisfying `T`, inside an active context. -/
def CtxRun (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (T : Config H → Prop) (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (q : List (Call (wasmHostSig H))) : Prop :=
  ∀ (labels : List Nat) (ret : Nat) (out : Option Nat), TagsOk tags s →
    StoreChkE (ehExt tags) s.funcs →
    chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    ∃ (E : Sim.ActiveCtx) (c : Config H), EvRun P host ⟨s, f, xcode stk es⟩ q (E.plug c) ∧ T c

section CtxRun

variable {tags : List TagInst} {T : Config H → Prop} {s s₁ s' : Store H} {f f₁ f' : Frame}
  {stk stk₁ stk' : List Val} {es args body : List Binaryen.BExpr} {l : List (OCall H)}
  {q q₁ q₂ : List (Call (wasmHostSig H))} {bt : BlockType} {np nr : Nat}

/-- A run into a hole, wrapped in an outer context after host-free steps. -/
theorem ctxRun_wrap {c₀ : Config H} {s₀ : Store H} {f₀ : Frame} {stk₀ : List Val}
    {es₀ : List Binaryen.BExpr} (O : Sim.ActiveCtx)
    (enter : Steps P NH c₀ (O.plug ⟨s₀, f₀, xcode stk₀ es₀⟩))
    (h : ∃ (E : Sim.ActiveCtx) (c : Config H), EvRun P host ⟨s₀, f₀, xcode stk₀ es₀⟩ q
      (E.plug c) ∧ T c) :
    ∃ (E : Sim.ActiveCtx) (c : Config H), EvRun P host c₀ q (E.plug c) ∧ T c := by
  obtain ⟨E, c, run, hT⟩ := h
  refine ⟨actComp E O, c, ?_, hT⟩
  rw [plug_actComp]
  simpa using evRun_trans (evRun_of_free enter) (evRun_plug O run)

theorem ctxRun_args {i : Instr} (ih : CtxRun tags P host T s f stk args q) :
    CtxRun tags P host T s f stk (.op i args :: es) q := by
  intro labels ret out hts hS hchk
  obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  refine ctxRun_wrap (.suffix (.plain i :: expression (Binaryen.BExpr.lowerList es)) .hole) ?_
    (ih _ _ _ hts hS ha)
  rw [show xcode stk (.op i args :: es) = _ from code_op stk i args es]
  exact .refl

theorem ctxRun_cond {c t el : List Binaryen.BExpr} (ih : CtxRun tags P host T s f stk c q) :
    CtxRun tags P host T s f stk (.if_ bt c t el :: es) q := by
  intro labels ret out hts hS hchk
  obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  refine ctxRun_wrap (.suffix (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
    (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)) .hole) ?_
    (ih _ _ _ hts hS hco)
  rw [show xcode stk (.if_ bt c t el :: es) = _ from code_if stk bt c t el es]
  exact .refl

theorem ctxRun_block (har : Binaryen.arity f bt = some (np, nr))
    (ih : CtxRun tags P host T s f (stk.take np) body q) :
    CtxRun tags P host T s f stk (.block bt body :: es) q := by
  intro labels ret out hts hS hchk
  obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
  exact ctxRun_wrap _ enter (ih _ _ _ hts hS hbc)

theorem ctxRun_loop (har : Binaryen.arity f bt = some (np, nr))
    (ih : CtxRun tags P host T s f (stk.take np) body q) :
    CtxRun tags P host T s f stk (.loop bt body :: es) q := by
  intro labels ret out hts hS hchk
  obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
  exact ctxRun_wrap _ enter (ih _ _ _ hts hS hbc)

theorem ctxRun_try {cs : List Catch} (har : Binaryen.arity f bt = some (np, nr))
    (ih : CtxRun tags P host T s f (stk.take np) body q) :
    CtxRun tags P host T s f stk (.tryTable bt cs body :: es) q := by
  intro labels ret out hts hS hchk
  obtain ⟨⟨ob, hbc⟩, enter⟩ := try_enter (P := P) har hchk
  exact ctxRun_wrap _ enter (ih _ _ _ hts hS hbc)

/-- A run then a run into a hole. -/
theorem ctxRun_pre {c₀ c₁ : Config H}
    (run : EvRun P host c₀ q₁ c₁)
    (h : ∃ (E : Sim.ActiveCtx) (c : Config H), EvRun P host c₁ q₂ (E.plug c) ∧ T c) :
    ∃ (E : Sim.ActiveCtx) (c : Config H), EvRun P host c₀ (q₁ ++ q₂) (E.plug c) ∧ T c := by
  obtain ⟨E, c, run', hT⟩ := h
  exact ⟨E, c, evRun_trans run run', hT⟩

theorem ctxRun_head (hH : NativeHostSlice host) (hE : HostSliceE tags host) {e : Binaryen.BExpr}
    (h : EvalLXPh s f stk [e] l (s', f', .flow (.normal stk')))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q₁) (hc : Cons host q₁)
    (ih : CtxRun tags P host T s' f' stk' es q₂) :
    CtxRun tags P host T s f stk (e :: es) (q₁ ++ q₂) := by
  intro labels ret out hts hS hchk
  obtain ⟨run, t', hS', hchk'⟩ := head_glue (P := P) hH hE h hq hc hts hS hchk
  exact ctxRun_pre run (ih _ _ _ t' hS' hchk')

theorem ctxRun_loopBack (hH : NativeHostSlice host) (hE : HostSliceE tags host) {vs : List Val}
    (har : Binaryen.arity f bt = some (np, nr))
    (h : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.brk 0 vs)))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q₁) (hc : Cons host q₁)
    (ih : CtxRun tags P host T s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) q₂) :
    CtxRun tags P host T s f stk (.loop bt body :: es) (q₁ ++ q₂) := by
  intro labels ret out hts hS hchk
  obtain ⟨⟨c₁, st, run⟩, t', hS', hchk'⟩ := loopBack_glue (P := P) hH hE har h hq hc hts hS hchk
  exact ctxRun_pre (.silent (.inl st) run) (ih _ _ _ t' hS' hchk')

theorem ctxRun_arm (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (h : EvalLXPh s f stk c l (s₁, f₁, .flow (.normal (cv :: stk₁))))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q₁) (hc : Cons host q₁)
    (ih : CtxRun tags P host T s₁ f₁ (stk₁.take np) (if b then t else el) q₂) :
    CtxRun tags P host T s f stk (.if_ bt c t el :: es) (q₁ ++ q₂) := by
  intro labels ret out hts hS hchk
  obtain ⟨t', hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hE h hb har hq hc hts hS hchk
  obtain ⟨E, c', run', hT⟩ := ih _ _ _ t' hS' hbc
  refine ⟨actComp E (.label nr [] (stk₁.drop np).reverse
    (expression (Binaryen.BExpr.lowerList es)) .hole), c', ?_, hT⟩
  rw [plug_actComp]
  exact evRun_trans run (evRun_plug _ run')

end CtxRun

/-! ## Reaches and divergence after a log -/

/-- The hole of a reached call `z`: its `call_ref` form, a checked call. -/
def CallHole (tags : List TagInst) (z : (wasmOShape H).self.Op) (c : Config H) : Prop :=
  ∃ (F : Frame) (pre : List Val) (c₀ : Admin) (rest : List Admin), c₀.IsCallRef ∧
    c = ⟨z.2.2, F, Interp.callCode pre z.2.1 z.1 c₀ rest⟩ ∧ CallChkP tags z.2.2 z.1 z.2.1

/-- The hole of host-free divergence: a checked problem diverging in the closed semantics. -/
def DivHole (tags : List TagInst) (c : Config H) : Prop :=
  ∃ (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr),
    c = ⟨s, f, xcode stk es⟩ ∧ EvalDivXP s f stk es ∧ CheckedP tags s f stk es

section Fwd

variable {tags : List TagInst} (hH : NativeHostSlice host) (hE : HostSliceE tags host)
include hH hE

/-- **A logged reach is a Core run to the reached call**, with exactly the events of its
resolved prefix, inside an active context; the reached call is checked. -/
theorem reachLXP_fwd {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {l : List (OCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXP s f stk es l z) :
    ∀ q, SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q → Cons host q →
      CtxRun tags P host (CallHole tags z) s f stk es q := by
  induction h with
  | call hargs hfi hty =>
    intro q hq hc labels ret out hts hS hchk
    obtain ⟨run, hcc⟩ := call_glue (P := P) hH hE hargs hfi hty hq hc hts hS hchk
    exact ⟨.hole, _, run, _, _, .callRefType _, _, trivial, rfl, hcc⟩
  | ind hargs hres hfi hty hy =>
    intro q hq hc labels ret out hts hS hchk
    obtain ⟨run, hcc⟩ := ir_glue (P := P) hH hE (.inl ⟨_, rfl⟩) hargs
      (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy hq hc hts hS hchk
    exact ⟨.hole, _, run, _, _, .plain (.callRef _), _, trivial, rfl, hcc⟩
  | ref hargs hfi hty hy =>
    intro q hq hc labels ret out hts hS hchk
    obtain ⟨run, hcc⟩ := ir_glue (P := P) hH hE (.inr rfl) hargs .refl hfi hty hy hq hc hts hS
      hchk
    exact ⟨.hole, _, run, _, _, .plain (.callRef _), _, trivial, rfl, hcc⟩
  | args _ ih => exact fun q hq hc => ctxRun_args (ih q hq hc)
  | callK hargs hfi hty _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_mid_log hq hc
    exact ctxRun_head hH hE (.callRet hargs hfi hty .nil) h₁ hc₁ (ih q₂ h₂ hc₂)
  | indK hargs hres hfi hty hy _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_mid_log hq hc
    exact ctxRun_head hH hE (.indRet hargs hres hfi hty hy .nil) h₁ hc₁ (ih q₂ h₂ hc₂)
  | refK hargs hfi hty hy _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_mid_log hq hc
    exact ctxRun_head hH hE (.refRet hargs hfi hty hy .nil) h₁ hc₁ (ih q₂ h₂ hc₂)
  | opK hi hargs hflat _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | block har _ ih => exact fun q hq hc => ctxRun_block har (ih q hq hc)
  | blockK har hbody hvs _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | loop har _ ih => exact fun q hq hc => ctxRun_loop har (ih q hq hc)
  | loopK har hbody _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | loopBack har hbody _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    exact ctxRun_loopBack hH hE har hbody h₁ hc₁ (ih q₂ h₂ hc₂)
  | cond _ ih => exact fun q hq hc => ctxRun_cond (ih q hq hc)
  | arm hcE hb har _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    exact ctxRun_arm hH hE hcE hb har h₁ hc₁ (ih q₂ h₂ hc₂)
  | ifK hcE hb har harm hvs _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | handler har _ ih => exact fun q hq hc => ctxRun_try har (ih q hq hc)
  | @tryK _ _ _ _ _ _ _ cs _ _ _ _ _ _ _ _ har hbody hvs _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.tryOk (cs := cs) har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)

/-- **Logged host-free divergence is a Core run to a host-free divergent problem**, with exactly
the events of its resolved log, inside an active context. -/
theorem logDivXP_fwd {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {l : List (OCall H)} (h : LogDivXP s f stk es l) :
    ∀ q, SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q → Cons host q →
      CtxRun tags P host (DivHole tags) s f stk es q := by
  induction h with
  | @div s f stk es hd =>
    intro q hq hc labels ret out hts hS hchk
    cases hq
    exact ⟨.hole, _, .refl _, s, f, stk, es, rfl, hd, labels, ret, out, hS, hchk, hts⟩
  | args _ ih => exact fun q hq hc => ctxRun_args (ih q hq hc)
  | callK hargs hfi hty _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_mid_log hq hc
    exact ctxRun_head hH hE (.callRet hargs hfi hty .nil) h₁ hc₁ (ih q₂ h₂ hc₂)
  | indK hargs hres hfi hty hy _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_mid_log hq hc
    exact ctxRun_head hH hE (.indRet hargs hres hfi hty hy .nil) h₁ hc₁ (ih q₂ h₂ hc₂)
  | refK hargs hfi hty hy _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_mid_log hq hc
    exact ctxRun_head hH hE (.refRet hargs hfi hty hy .nil) h₁ hc₁ (ih q₂ h₂ hc₂)
  | opK hi hargs hflat _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | block har _ ih => exact fun q hq hc => ctxRun_block har (ih q hq hc)
  | blockK har hbody hvs _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | loop har _ ih => exact fun q hq hc => ctxRun_loop har (ih q hq hc)
  | loopK har hbody _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | loopBack har hbody _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    exact ctxRun_loopBack hH hE har hbody h₁ hc₁ (ih q₂ h₂ hc₂)
  | cond _ ih => exact fun q hq hc => ctxRun_cond (ih q hq hc)
  | arm hcE hb har _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    exact ctxRun_arm hH hE hcE hb har h₁ hc₁ (ih q₂ h₂ hc₂)
  | ifK hcE hb har harm hvs _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)
  | handler har _ ih => exact fun q hq hc => ctxRun_try har (ih q hq hc)
  | @tryK _ _ _ _ _ _ _ cs _ _ _ _ _ _ _ har hbody hvs _ ih =>
    intro q hq hc
    obtain ⟨q₁, q₂, rfl, h₁, h₂, hc₁, hc₂⟩ := split_log hq hc
    have hE' := EvalLXPh.tryOk (cs := cs) har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact ctxRun_head hH hE hE' h₁ hc₁ (ih q₂ h₂ hc₂)

end Fwd

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP
