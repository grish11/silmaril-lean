module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.DivCall

/-!
# Divergence after a nonempty log: head trees (proofs)

The tools of the tree cases of the divergent backward simulation:

* `head_contra`: a head tree with a resolved logged run (`ResW`: by returning callees, or up to a
  trapping callee) whose log is a prefix of the events does not diverge alone after them: by
  `evalLXPh_res_evRun` it is a Core run to a final form (`noDiv_of_evRun`). Every finished end of
  a head tree diverging alone is ruled out this way;
* `head_cons`: a head tree run normally in front of a divergence (or a reach) of the trees after
  it is one of the trees with it in front (the `…K` constructors of `LogDivXP`, `ReachLXP`);
* `cont_typedH`, `site_factsH`: typing after a head tree and at an operator's site, from a logged
  run resolved against a host the log allows (`evalOXP_host_good`);
* the one-step facts of `if` and of entering a loop (`steps_if_arm`, `loop_step_unique`).
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

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H}

/-- **A resolution of a log**: by returning callees, or up to a trapping callee. -/
def ResW (l : List (OCall H)) (cs : List (Call (wasmHostSig H))) : Prop :=
  Shape.SubstPre Cl (l.map OCall.lift) cs ∨
    ∃ (l₁ l₂ : List (OCall H)) (g : Nat) (args : List Val) (s₁ : Store H) (b : List Val ⊕ Nat)
      (s₂ : Store H) (q₁ c₁ : List (Call (wasmHostSig H))),
      l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ ∧ Shape.SubstPre Cl (l₁.map OCall.lift) q₁ ∧
      (c₁, .trap) ∈ Shape.close wasmHOpenXP g s₁ args ∧ cs = q₁ ++ c₁

theorem resW_nil {l : List (OCall H)} {cs : List (Call (wasmHostSig H))} (h : ResW l cs) :
    ResW (l ++ []) cs := by simpa using h

theorem resW_prepend {l₀ l : List (OCall H)} {q₀ cs : List (Call (wasmHostSig H))}
    (h₀ : Shape.SubstPre Cl (l₀.map OCall.lift) q₀) (h : ResW l cs) : ResW (l₀ ++ l) (q₀ ++ cs) := by
  rcases h with h | ⟨l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, h₁, hc, rfl⟩
  · exact .inl (by rw [List.map_append]; exact substPre_append' h₀ h)
  · refine .inr ⟨l₀ ++ l₁, l₂, g, args, s₁, b, s₂, q₀ ++ q₁, c₁, by simp, ?_, hc, by simp⟩
    rw [List.map_append]
    exact substPre_append' h₀ h₁

theorem resW_of_back {l : List (OCall H)} {r : Store H × Frame × POut}
    {cs : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) cs ∨
      (r.2.2 = .flow .trap ∧ ∃ (l₁ l₂ : List (OCall H)) (g : Nat) (args : List Val)
        (s₁ : Store H) (b : List Val ⊕ Nat) (s₂ : Store H) (q₁ c₁ : List (Call (wasmHostSig H))),
        l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ ∧
        Shape.SubstPre (Shape.close wasmHOpenXP) (l₁.map OCall.lift) q₁ ∧
        (c₁, .trap) ∈ Shape.close wasmHOpenXP g s₁ args ∧ cs = q₁ ++ c₁)) : ResW l cs := by
  rcases h with h | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

/-- The head tree of a typed problem is a typed problem. -/
theorem typedP_head {s : Store H} {f : Frame} {stk : List Val} {e : BExpr} {es : List BExpr}
    (ht : TypedP tags s f stk (e :: es)) : TypedP tags s f stk [e] := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  refine ⟨expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, o, hS,
    chk_consE.mpr ⟨o, h1, chkE_nil_selfP o⟩, ?_, hTM, hts⟩
  rw [code_consX] at hct
  simpa only [List.append_assoc] using hct

/-- **A head tree with a resolved logged run does not diverge alone after its log.** -/
theorem head_contra (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs₁ cs₂ : List (Call (wasmHostSig H))}
    (ht : TypedP tags s f stk es) (hd : EvalLXPh s f stk es l r) (hres : ResW l cs₁)
    (hdv : EvDiv (profile o) host n ⟨s, f, xcode stk es⟩ (cs₁ ++ cs₂)) : False := by
  have hct := typedP_ctx' ht
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  have hcons := (consistent_append (evDiv_consistent hdv)).1
  obtain ⟨s', f', c', oc, hrun, he⟩ :=
    evalLXPh_res_evRun (P := profile o) hH hE hd hres hcons hts hS hc
  exact noDiv_of_evRun hT hrun (outcome_ends_stuck he s' f') hct hdv

/-- **A head tree run normally in front of the trees after it.** -/
theorem head_cons {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : BExpr}
    {l : List (OCall H)} (h : EvalLXPh s f stk [e] l (s₂, f₂, .flow (.normal stk₂)))
    (es : List BExpr) :
    (∀ l', LogDivXP s₂ f₂ stk₂ es l' → LogDivXP s f stk (e :: es) (l ++ l')) ∧
      (∀ l' z, ReachLXP s₂ f₂ stk₂ es l' z → ReachLXP s f stk (e :: es) (l ++ l') z) := by
  generalize hes : [e] = es₀ at h
  generalize hr : (s₂, f₂, POut.flow (.normal stk₂)) = r at h
  induction h generalizing e s₂ f₂ stk₂ with
  | argsAbort _ ho =>
    cases hr; exact (ho trivial).elim
  | callRet hargs hfi hty hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.callK hargs hfi hty h,
      fun l' z h => by simpa using ReachLXP.callK hargs hfi hty h⟩
  | opOk hi hargs hflat hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.opK hi hargs hflat h,
      fun l' z h => by simpa using ReachLXP.opK hi hargs hflat h⟩
  | blockOk har hbody hvs hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.blockK har hbody hvs h,
      fun l' z h => by simpa using ReachLXP.blockK har hbody hvs h⟩
  | blockEsc _ _ ho => cases hr; exact ho.elim
  | loopOk har hbody hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.loopK har hbody h,
      fun l' z h => by simpa using ReachLXP.loopK har hbody h⟩
  | loopBack har hbody hk _ ih₂ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    obtain ⟨hl, hrr⟩ := ih₂ rfl hr
    exact ⟨fun l' h => by simpa using LogDivXP.loopBack har hbody (hl l' h),
      fun l' z h => by simpa using ReachLXP.loopBack har hbody (hrr l' z h)⟩
  | loopEsc _ _ ho => cases hr; exact ho.elim
  | ifOk hc hb har harm hvs hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.ifK hc hb har harm hvs h,
      fun l' z h => by simpa using ReachLXP.ifK hc hb har harm hvs h⟩
  | ifEsc _ _ _ _ ho => cases hr; exact ho.elim
  | ifAbort _ ho => cases hr; exact (ho trivial).elim
  | indRet hargs hres hfi hty hy hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.indK hargs hres hfi hty hy h,
      fun l' z h => by simpa using ReachLXP.indK hargs hres hfi hty hy h⟩
  | refRet hargs hfi hty hy hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.refK hargs hfi hty hy h,
      fun l' z h => by simpa using ReachLXP.refK hargs hfi hty hy h⟩
  | tryOk har hbody hvs hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact ⟨fun l' h => by simpa using LogDivXP.tryK har hbody hvs h,
      fun l' z h => by simpa using ReachLXP.tryK har hbody hvs h⟩
  | tryEsc _ _ ho => cases hr; exact ho.elim
  | opStop _ _ _ hfl => cases hr; exact (hfl trivial).elim
  | nil => cases hes
  | _ => cases hr

/-- **The trees after a head tree run normally are typed.** -/
theorem cont_typedH (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : BExpr} {es : List BExpr}
    {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (ht : TypedP tags s f stk (e :: es))
    (hd : EvalLXPh s f stk [e] l (s₂, f₂, .flow (.normal stk₂)))
    (hq : Shape.SubstPre Cl (l.map OCall.lift) q) (hc : (coreHostRel host).Consistent q)
    (hst : Steps (profile o) host ⟨s, f, xcode stk (e :: es)⟩ ⟨s₂, f₂, xcode stk₂ es⟩) :
    TypedP tags s₂ f₂ stk₂ es := by
  obtain ⟨rest, labels, ret, out, hS, hck, hct, hTM, hts⟩ := ht
  obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hck
  have h1' : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) [e] =
      some o₁ := chk_consE.mpr ⟨o₁, h1, chkE_nil_selfP o₁⟩
  obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hc
  obtain ⟨t₂, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
    hev hts
  obtain ⟨hpo, hinv, -⟩ := hA hS h1'
  have hpo' : o₁ = some stk₂.length := hpo
  subst hpo'
  refine ⟨rest, labels, ret, out, storeChk_inv hinv hS, chk_inv hinv h2, ?_,
    by rw [hinv.2.1]; exact hTM, t₂⟩
  exact ContextTyped.steps_typed hT hct (Steps.append rest hst)

/-- **The facts at an operator's site**, after its arguments ran normally. -/
theorem site_factsH (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr} {args es : List BExpr}
    {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (ht : TypedP tags s f stk (.op i args :: es))
    (hd : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
    (hq : Shape.SubstPre Cl (l.map OCall.lift) q) (hc : (coreHostRel host).Consistent q)
    (hst : Steps (profile o) host ⟨s, f, xcode stk args⟩ ⟨s₁, f₁, vals stk₁.reverse⟩) :
    ∃ rest, Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ ∧
      Abstract.CallXT.TyFuncs s₁ ∧ Abstract.CallXT.TyTypes f₁.module ∧
      StoreChkE (ehExt tags) s₁.funcs ∧ TagsOk tags s₁ ∧ ∃ labels ret o',
        flatChkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i =
          some o' := by
  obtain ⟨rest, labels, ret, out, hS, hck, hct, hTM, hts⟩ := ht
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hc
  obtain ⟨t₁, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
    hev hts
  obtain ⟨hf, inv⟩ := arity_args hS (arityE_of_arityP hA) h1
  rw [code_op] at hct
  have hct' : Sim.ContextTyped ⟨s, f, xcode stk args ++
      (.plain i :: expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [xcode, List.append_assoc, List.cons_append] using hct
  have ht₁ := ContextTyped.steps_typed hT hct' (Steps.append _ hst)
  have ht₁' : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++
      .plain i :: (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ := by
    simpa only [List.cons_append] using ht₁
  exact ⟨_, ht₁', tyFuncs_of_ctx ht₁', by rw [inv.2.1]; exact hTM, storeChk_inv inv hS, t₁,
    labels, ret, o₁, hf⟩

/-! ## One-step facts -/

/-- `if` steps, host-free, to the block of its chosen arm. -/
theorem steps_if_arm {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cv : Val}
    {b : Bool} {t el : List BExpr} {rest : List Admin}
    (hb : Binaryen.truthy cv = some b) :
    Steps (profile o) NH ⟨s, f, vals (cv :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩
      ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest =
      vals stk.reverse ++ [constI32 c₀,
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ rest := by
    simp [vals, constI32]
  rw [e]
  refine .single ?_
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

/-- **Entering a loop is the only step of a loop under values.** -/
theorem loop_step_unique {P : Numerics.Profile} {s : Store H} {f : Frame} {stk : List Val}
    {bt : BlockType} {B : List Instr} {np nr : Nat} {rest : List Admin} {c₁ : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (h : Step P host ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩ c₁) :
    c₁ = ⟨s, f, vals (stk.drop np).reverse ++
      [.label np [.loop bt B] (vals (stk.take np).reverse ++ expression B)] ++ rest⟩ := by
  rcases c₁ with ⟨s', f', es'⟩
  rcases Sim.Step.split_head (a := .plain (.loop bt B)) rfl h with
      ⟨ws, us, is', hsplit, hst, rfl⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
  · obtain ⟨ws', vs, t₁, t₂, rfl, hbt, hvl, hc⟩ := Step.loop_vals_inv hst
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    obtain ⟨t₁', t₂', hbt', hl₁, -⟩ := blockType_of_arity har
    rw [hbt] at hbt'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbt'
    obtain ⟨rfl, rfl⟩ := hbt'
    have e : stk.reverse = (stk.drop np).reverse ++ (stk.take np).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [e, ← List.append_assoc] at hsplit
    have hlen : vs.length = (stk.take np).reverse.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨h₁, rfl⟩ := List.append_inj' hsplit hlen.symm
    rw [hl₁, h₁]
    simp
  · cases hx
  · cases hx

/-! ## Sizes -/

theorem size_args {i : Instr} {args es : List BExpr} :
    sizeOf args < sizeOf (BExpr.op i args :: es) := by
  simp only [List.cons.sizeOf_spec, BExpr.op.sizeOf_spec]; omega

theorem size_block {bt : BlockType} {body es : List BExpr} :
    sizeOf body < sizeOf (BExpr.block bt body :: es) := by
  simp only [List.cons.sizeOf_spec, BExpr.block.sizeOf_spec]; omega

theorem size_loop {bt : BlockType} {body es : List BExpr} :
    sizeOf body < sizeOf (BExpr.loop bt body :: es) := by
  simp only [List.cons.sizeOf_spec, BExpr.loop.sizeOf_spec]; omega

theorem size_try {bt : BlockType} {cs : List Catch} {body es : List BExpr} :
    sizeOf body < sizeOf (BExpr.tryTable bt cs body :: es) := by
  simp only [List.cons.sizeOf_spec, BExpr.tryTable.sizeOf_spec]; omega

theorem size_cond {bt : BlockType} {c t el es : List BExpr} :
    sizeOf c < sizeOf (BExpr.if_ bt c t el :: es) := by
  simp only [List.cons.sizeOf_spec, BExpr.if_.sizeOf_spec]; omega

theorem size_arm {bt : BlockType} {c t el es : List BExpr} (b : Bool) :
    sizeOf (if b then t else el) < sizeOf (BExpr.if_ bt c t el :: es) := by
  cases b <;> simp only [List.cons.sizeOf_spec, BExpr.if_.sizeOf_spec, Bool.false_eq_true,
    ↓reduceIte] <;> omega

theorem size_tail {e : BExpr} {es : List BExpr} : sizeOf es < sizeOf (e :: es) := by
  simp only [List.cons.sizeOf_spec]; omega

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
