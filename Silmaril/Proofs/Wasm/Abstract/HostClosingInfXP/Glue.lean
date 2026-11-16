module

public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Interp.PProgress.Thms

/-!
# Logged canonical prefixes as Core runs (proofs)

The pieces of a logged canonical prefix as Core runs with exactly their resolved log, from the
logged forward simulation `evalLXPh_evRun` (`Silmaril.Wasm.Abstract.HostClosingXP.Thms`):

* `hEvStep_plug`, `evRun_plug`, `coreInf_plug`: labelled steps, runs and productive runs lift
  through every active context (`Sim.ActiveCtx`: sequences, labels, handlers, frames);
  `actComp` nests contexts;
* `head_glue`: a head tree run to completion is a Core run to the code of the remaining trees,
  the check carried along;
* `loopBack_glue`: a loop iteration branching back is a Core run back to the loop, its first step
  host-free (entering the loop);
* `arm_glue`: an `if` condition, then the chosen arm's label;
* `block_enter`, `loop_enter`, `try_enter`: entering a body, host-free;
* `call_glue`, `ind_glue`, `ref_glue`: the arguments of a call, then its `call_ref` form on the
  callee, a checked call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP)
open Shape (SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- The empty host: host-free steps. -/
abbrev NH : HostSemantics H := fun _ _ _ _ => False

/-- The host answers of a log are allowed. -/
abbrev Cons (host : HostSemantics H) (q : List (Call (wasmHostSig H))) : Prop :=
  (coreHostRel host).Consistent q

theorem cons_append {q₁ q₂ : List (Call (wasmHostSig H))} :
    Cons host (q₁ ++ q₂) ↔ Cons host q₁ ∧ Cons host q₂ :=
  List.forall_mem_append

theorem substPre_append {sh : Silmaril.Games.Abstract.Shape} {c : sh.ClosedMod}
    {u v : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} :
    SubstPre c (u ++ v) q ↔ ∃ q₁ q₂, q = q₁ ++ q₂ ∧ SubstPre c u q₁ ∧ SubstPre c v q₂ := by
  induction u generalizing q with
  | nil => exact ⟨fun h => ⟨[], q, rfl, .nil, h⟩, fun ⟨q₁, q₂, e, h₁, h₂⟩ => by
      cases h₁; simpa [e] using h₂⟩
  | cons z u ih =>
    constructor
    · intro h
      cases h with
      | ext h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .ext h₁, h₂⟩
      | int hm h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .int hm h₁, h₂⟩
    · rintro ⟨q₁, q₂, rfl, h₁, h₂⟩
      cases h₁ with
      | ext h₁ => exact .ext (ih.2 ⟨_, _, rfl, h₁, h₂⟩)
      | int hm h₁ =>
        rw [List.append_assoc]
        exact SubstPre.int hm (ih.2 ⟨_, _, rfl, h₁, h₂⟩)

/-- A resolved log split at an append, with its consistency. -/
theorem split_log {la lb : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (hq : SubstPre (Shape.close wasmHOpenXP) ((la ++ lb).map OCall.lift) q) (hc : Cons host q) :
    ∃ q₁ q₂, q = q₁ ++ q₂ ∧ SubstPre (Shape.close wasmHOpenXP) (la.map OCall.lift) q₁ ∧
      SubstPre (Shape.close wasmHOpenXP) (lb.map OCall.lift) q₂ ∧ Cons host q₁ ∧ Cons host q₂ := by
  rw [List.map_append] at hq
  obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
  rw [cons_append] at hc
  exact ⟨q₁, q₂, rfl, h₁, h₂, hc.1, hc.2⟩

/-- A resolved log with one call in the middle, split before the rest. -/
theorem split_mid_log {la lb : List (OCall H)} {z : OCall H} {q : List (Call (wasmHostSig H))}
    (hq : SubstPre (Shape.close wasmHOpenXP) ((la ++ z :: lb).map OCall.lift) q)
    (hc : Cons host q) :
    ∃ q₁ q₂, q = q₁ ++ q₂ ∧ SubstPre (Shape.close wasmHOpenXP) ((la ++ [z]).map OCall.lift) q₁ ∧
      SubstPre (Shape.close wasmHOpenXP) (lb.map OCall.lift) q₂ ∧ Cons host q₁ ∧
      Cons host q₂ := by
  rw [show la ++ z :: lb = (la ++ [z]) ++ lb by simp] at hq
  exact split_log hq hc

/-! ## Contexts -/

theorem decompose?_handler_some {s : Store H} {n : Nat} {cs : List Catch} {b : List Admin}
    {E : SingleThreaded.Ctx} {a : Nat} {hh : H} {us : List Val}
    (hd : SingleThreaded.decompose? s b = some (E, a, hh, us)) :
    SingleThreaded.decompose? s [.handler n cs b] = some (.handler [] n cs E [], a, hh, us) := by
  have hs : SingleThreaded.splitVals [Admin.handler n cs b] = ([], [.handler n cs b]) := by
    simp [SingleThreaded.splitVals, Admin.val?]
  rw [SingleThreaded.decompose?_of_split hs, SingleThreaded.decompHead_handler, hd]
  rfl

/-- **A labelled step lifts through a handler**, with the same label. -/
theorem hEvStep_handler {s s' : Store H} {f f' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat) (cs : List Catch)
    (h : HEvStep P host ⟨s, f, b⟩ l ⟨s', f', b'⟩) :
    HEvStep P host ⟨s, f, [.handler n cs b]⟩ l ⟨s', f', [.handler n cs b']⟩ := by
  cases l with
  | none =>
    rcases h with h | ⟨hc, E, a, hh, us, hd, hdiv⟩
    · exact .inl (Step.ctxtHandler h)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact .inr ⟨rfl, _, a, hh, us, decompose?_handler_some hd, hdiv⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hans, hc⟩ := h
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨_, a, decompose?_handler_some hd, hs, hans, by simp [SingleThreaded.Ctx.fill, vals]⟩

/-- **A labelled step lifts through an active context**, with the same label. -/
theorem hEvStep_plug (E : Sim.ActiveCtx) {c c' : Config H} {l : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c l c') : HEvStep P host (E.plug c) l (E.plug c') := by
  induction E generalizing c c' with
  | hole => exact h
  | suffix rest E ih =>
    rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
    exact ih (by simpa [vals] using hEvStep_ctx [] rest h)
  | label n cont vs rest E ih =>
    rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
    exact ih (hEvStep_ctx vs rest (hEvStep_label n cont h))
  | handler n cs vs rest E ih =>
    rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
    exact ih (hEvStep_ctx vs rest (hEvStep_handler n cs h))
  | frame n g vs rest E ih =>
    rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
    exact ih (hEvStep_ctx vs rest (hEvStep_frame n h))

/-- A labelled run inside an active context. -/
theorem evRun_plug (E : Sim.ActiveCtx) {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : EvRun P host (E.plug c) cs (E.plug c') :=
  evRun_wrap E.plug (fun _ _ _ h => hEvStep_plug E h) h

/-- A productive run inside an active context. -/
theorem coreInf_plug (E : Sim.ActiveCtx) {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) : CoreInf P host (E.plug c) ω :=
  coreInf_wrap E.plug (fun _ _ _ h => hEvStep_plug E h) h

/-- `actComp E O`: the context `E` inside the context `O`. -/
def actComp : Sim.ActiveCtx → Sim.ActiveCtx → Sim.ActiveCtx
  | .hole, O => O
  | .suffix rest E, O => .suffix rest (actComp E O)
  | .label n cont vs rest E, O => .label n cont vs rest (actComp E O)
  | .handler n cs vs rest E, O => .handler n cs vs rest (actComp E O)
  | .frame n g vs rest E, O => .frame n g vs rest (actComp E O)

theorem plug_actComp (E O : Sim.ActiveCtx) (c : Config H) :
    (actComp E O).plug c = O.plug (E.plug c) := by
  induction E generalizing c with
  | hole => rfl
  | suffix rest E ih => exact ih _
  | label n cont vs rest E ih => exact ih _
  | handler n cs vs rest E ih => exact ih _
  | frame n g vs rest E ih => exact ih _

/-! ## Glue -/

section Glue

variable {tags : List TagInst} {s s₁ s' : Store H} {f f₁ f' : Frame}
  {stk stk₁ stk' : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
  {q : List (Call (wasmHostSig H))} {labels : List Nat} {ret : Nat} {out : Option Nat}

theorem chkE_nil' {F : List (FuncInst H)} {mi : ModuleInst} {nl : Nat} (o : Option Nat) :
    chkE (ehExt tags) F mi nl ret labels o [] = some o := by
  cases o <;> simp

/-- The resolved log of a logged run with a consistent resolution: an oracle run, the tag
invariants and arity facts after it, and its logged Core run to a final form. -/
theorem full_run (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {es : List Binaryen.BExpr} {r : Store H × Frame × POut}
    (h : EvalLXPh s f stk es l r) (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q)
    (hc : Cons host q) (hts : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
      ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChkE (ehExt tags) s.funcs →
        chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
          some out →
        ∃ (s₂ : Store H) (f₂ : Frame) (c' : List Admin) (o : Outcome),
          EvRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ q
            ⟨s₂, f₂, c'⟩ ∧ o.Ends c' ∧ MatchP r s₂ f₂ o := by
  obtain ⟨d, cl⟩ := evalLXPh_evRun (P := P) (tags := tags) hH hE h hq hc
  obtain ⟨t₁, hA, -⟩ := evalOXP_host_good (P := P) hH hE d hts
  exact ⟨t₁, hA, fun hS hchk => cl hts hS hchk⟩

/-- A logged run to a normal flow: its Core run ends at the values. -/
theorem normal_run (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {es : List Binaryen.BExpr}
    (h : EvalLXPh s f stk es l (s', f', .flow (.normal stk')))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hc : Cons host q)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out) :
    EvRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ q
        ⟨s', f', vals stk'.reverse⟩ ∧ TagsOk tags s' ∧
      ArityGoodE (ehExt tags) s f stk es (s', f', .normal stk') true := by
  obtain ⟨t₁, hA, cl⟩ := full_run (P := P) hH hE h hq hc hts
  obtain ⟨s₂, f₂, c', o, hrun, he, hm⟩ := cl hS hchk
  rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hfm⟩ | ⟨hf, -⟩
  · rw [ends_normal hfm he] at hrun
    exact ⟨hrun, t₁, arityE_of_arityP hA⟩
  · cases hf

/-- **A head tree run to completion** is a logged Core run to the code of the remaining trees,
the invariants and the check carried along. -/
theorem head_glue (hH : NativeHostSlice host) (hE : HostSliceE tags host) {e : Binaryen.BExpr}
    (h : EvalLXPh s f stk [e] l (s', f', .flow (.normal stk')))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hc : Cons host q)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (e :: es) = some out) :
    EvRun P host ⟨s, f, xcode stk (e :: es)⟩ q ⟨s', f', xcode stk' es⟩ ∧ TagsOk tags s' ∧
      StoreChkE (ehExt tags) s'.funcs ∧
      chkE (ehExt tags) s'.funcs f'.module f'.locals.length ret labels (some stk'.length) es =
        some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hchk
  have h1' : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      [e] = some o := chk_consE.mpr ⟨o, h1, chkE_nil' o⟩
  obtain ⟨hrun, t₁, hA⟩ := normal_run (P := P) hH hE h hq hc hts hS h1'
  obtain ⟨hok, inv⟩ := hA hS h1'
  have hok' : o = some stk'.length := hok
  subst hok'
  refine ⟨?_, t₁, storeChk_inv inv hS, chk_inv inv h2⟩
  have := evRun_ctx [] (expression (Binaryen.BExpr.lowerList es)) hrun
  simpa [xcode, code_cons, expression, List.append_assoc, vals] using this

/-- **A loop iteration branching back to the loop**, as a logged Core run to the loop again,
its first step entering the loop host-free. -/
theorem loopBack_glue (hH : NativeHostSlice host) (hE : HostSliceE tags host) {bt : BlockType}
    {body : List Binaryen.BExpr} {np nr : Nat} {vs : List Val}
    (har : Binaryen.arity f bt = some (np, nr))
    (h : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.brk 0 vs)))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hc : Cons host q)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out) :
    (∃ c₁, Step P NH ⟨s, f, xcode stk (.loop bt body :: es)⟩ c₁ ∧
      EvRun P host c₁ q ⟨s₁, f₁, xcode (vs.take np ++ stk.drop np) (.loop bt body :: es)⟩) ∧
      TagsOk tags s₁ ∧ StoreChkE (ehExt tags) s₁.funcs ∧
      chkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
  obtain ⟨t₁, hA, cl⟩ := full_run (P := P) hH hE h hq hc hts
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
  obtain ⟨_, _, hbc, hok, inv1⟩ := body_facts hS (arityE_of_arityP hA) hb (take_length_of_le hp)
  obtain ⟨m, hm', hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm'
    exact hm' ▸ hle
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  refine ⟨?_, t₁, storeChk_inv inv1 hS, by rw [hlen]; exact chk_inv inv1 hchk⟩
  obtain ⟨s₂, f₂, c', o, hrun, he, hm⟩ := cl hS hbc
  rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hfm⟩ | ⟨hf, -⟩
  swap; · cases hf
  have st := step_enter (P := P) (host := NH) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) (expression (Binaryen.BExpr.lowerList es))
  have inner := evRun_ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
    (evRun_label np [.loop bt (Binaryen.BExpr.lowerList body)] hrun)
  have exit := exit_br0 (P := P) (host := NH) (s₁ := s₂) (f₁ := f₂)
    (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hfm hnp
    (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
  have e : vals (vs.take np ++ stk.drop np).reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es) =
      vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
        expression [.loop bt (Binaryen.BExpr.lowerList body)] ++
        expression (Binaryen.BExpr.lowerList es) := by
    simp [expression]
  refine ⟨⟨s, f, vals (stk.drop np).reverse ++ [.label np [.loop bt (Binaryen.BExpr.lowerList body)]
    (vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body))] ++
    expression (Binaryen.BExpr.lowerList es)⟩, ?_, ?_⟩
  · simpa only [xcode, code_loop] using st
  · simp only [xcode, code_loop]
    rw [e]
    simpa using evRun_trans inner (evRun_of_free exit)

theorem step_if_arm {stk : List Val} {bt : BlockType} {t el : List Binaryen.BExpr} {cv : Val}
    {b : Bool} {rest : List Admin} (hb : Binaryen.truthy cv = some b) :
    Step P NH ⟨s, f, vals (cv :: stk).reverse ++
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
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

/-- **An `if` condition, then the chosen arm's label**, as a logged Core run. -/
theorem arm_glue (hH : NativeHostSlice host) (hE : HostSliceE tags host) {bt : BlockType}
    {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {np nr : Nat}
    (h : EvalLXPh s f stk c l (s₁, f₁, .flow (.normal (cv :: stk₁))))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hc : Cons host q)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.if_ bt c t el :: es) = some out) :
    TagsOk tags s₁ ∧ StoreChkE (ehExt tags) s₁.funcs ∧
      (∃ ob, chkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
        (some (stk₁.take np).length) (if b then t else el) = some ob) ∧
      EvRun P host ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ q
        (Sim.ActiveCtx.plug (.label nr [] (stk₁.drop np).reverse
          (expression (Binaryen.BExpr.lowerList es)) .hole)
          ⟨s₁, f₁, xcode (stk₁.take np) (if b then t else el)⟩) := by
  obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  obtain ⟨hrun, t₁, hA⟩ := normal_run (P := P) hH hE h hq hc hts hS hco
  obtain ⟨inv1, hp, hbarm, -⟩ := arity_if_pre (b := b) hS hA har hchk
  replace hbarm := chk_inv_endsAt inv1 hbarm
  obtain ⟨ob, hb', -⟩ := endsAt_eq hbarm
  refine ⟨t₁, storeChk_inv inv1 hS, ⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  have r1 := evRun_ctx [] (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
    (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)) hrun
  have st := step_if_arm (P := P) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t) (el := el)
    (rest := expression (Binaryen.BExpr.lowerList es)) hb
  have enter := steps_enter (P := P) (host := NH) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (step_block har)
    (expression (Binaryen.BExpr.lowerList es))
  simp only [xcode, code_if, Sim.ActiveCtx.plug]
  simpa [vals] using evRun_trans r1 (evRun_of_free (Relation.ReflTransGen.head st enter))

end Glue

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP
