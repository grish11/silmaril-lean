module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Reach

/-!
# Closed reaches of a host call are Core runs to a host call (proofs)

On checked code (`Interp.CheckedP`, `Interp.CallChkP`), a reach of a host call (`HReach`,
`HCallReach`) is a Core run, under any host and profile and in any active context, to a
configuration at a host call (`decompose?`): `hreach_core_both`. Each constructor takes the steps
of the forward divergence simulation `Interp.progressP` for the matching unfolding of
`XDivergeP.DivStepXP`/`CallStepXP` (entering a block, loop, `try_table` or callee; running a head
tree, a loop iteration or a condition to completion; a pending tail call made at the frame); a
call to a host function is at a host call (`decompose?_redex`), and an active context around code
at a host call is at that host call (`decompose?_plug`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Binaryen (BExpr liftInstrs truthy)

variable {H : Type}

/-! ## Contexts at a host call -/

theorem decompose?_handler_some' {s : Store H} {n : Nat} {cs : List Catch} {b : List Admin}
    {E : Ctx} {a : Nat} {hh : H} {us : List Val} (hd : decompose? s b = some (E, a, hh, us)) :
    decompose? s [.handler n cs b] = some (.handler [] n cs E [], a, hh, us) := by
  have hs : splitVals [Admin.handler n cs b] = ([], [.handler n cs b]) := by
    simp [splitVals, Admin.val?]
  rw [decompose?_of_split hs, decompHead_handler, hd]
  rfl

/-- **An active context around code at a host call is at a host call.** -/
theorem decompose?_plug (E : Sim.ActiveCtx) {c : Config H}
    (hd : (decompose? c.store c.code).isSome) :
    (decompose? (E.plug c).store (E.plug c).code).isSome := by
  induction E generalizing c with
  | hole => exact hd
  | suffix rest E ih =>
    apply ih
    obtain ⟨⟨E', a, hh, us⟩, h⟩ := Option.isSome_iff_exists.mp hd
    have := decompose?_wrap (s := c.store) [] rest h
    simp only [vals, List.map_nil, List.nil_append] at this
    show (decompose? c.store (c.code ++ rest)).isSome
    rw [this]; rfl
  | label n cont vs rest E ih =>
    apply ih
    obtain ⟨⟨E', a, hh, us⟩, h⟩ := Option.isSome_iff_exists.mp hd
    have := decompose?_wrap (s := c.store) vs rest
      (Silmaril.Wasm.Abstract.decompose?_label_some (n := n) (cont := cont) h)
    show (decompose? c.store (vals vs ++ [.label n cont c.code] ++ rest)).isSome
    rw [this]; rfl
  | handler n cs vs rest E ih =>
    apply ih
    obtain ⟨⟨E', a, hh, us⟩, h⟩ := Option.isSome_iff_exists.mp hd
    have := decompose?_wrap (s := c.store) vs rest (decompose?_handler_some' (n := n) (cs := cs) h)
    show (decompose? c.store (vals vs ++ [.handler n cs c.code] ++ rest)).isSome
    rw [this]; rfl
  | frame n f vs rest E ih =>
    apply ih
    obtain ⟨⟨E', a, hh, us⟩, h⟩ := Option.isSome_iff_exists.mp hd
    have := decompose?_wrap (s := c.store) vs rest
      (Silmaril.Wasm.Abstract.decompose?_frame_some (n := n) (F := c.frame) h)
    show (decompose? c.store (vals vs ++ [.frame n c.frame c.code] ++ rest)).isSome
    rw [this]; rfl

/-! ## Reaches are Core runs to a host call -/

section Core

variable {P : Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}

/-- The Core run of a reaching problem, in any active context. -/
def ReachRun (tags : List TagInst) (P : Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) : Prop :=
  CheckedP tags s f stk es → ∀ E : Sim.ActiveCtx, ∃ T : Config H,
    Steps P host (E.plug ⟨s, f, xcode stk es⟩) T ∧ (decompose? T.store T.code).isSome

/-- The Core run of a reaching call, from its `call_ref` form, in any active context. -/
def CallReachRun (tags : List TagInst) (P : Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (a : Nat) (args : List Val) : Prop :=
  CallChkP tags s a args → ∀ (E : Sim.ActiveCtx) (f : Frame) (pre : List Val) (cr : Admin)
    (rest : List Admin), cr.IsCallRef → ∃ T : Config H,
    Steps P host (E.plug ⟨s, f, Interp.callCode pre args a cr rest⟩) T ∧
      (decompose? T.store T.code).isSome

theorem reachRun_of_steps {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List BExpr} {E E' : Sim.ActiveCtx}
    (hst : Steps P host (E.plug ⟨s, f, xcode stk es⟩) (E'.plug ⟨s', f', xcode stk' es'⟩))
    (hc : CheckedP tags s' f' stk' es') (h : ReachRun tags P host s' f' stk' es') :
    ∃ T : Config H, Steps P host (E.plug ⟨s, f, xcode stk es⟩) T ∧
      (decompose? T.store T.code).isSome := by
  obtain ⟨T, hT, hd⟩ := h hc E'
  exact ⟨T, hst.trans hT, hd⟩

variable {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {es args : List BExpr}

theorem run_args {i : Instr} (ih : ReachRun tags P host s f stk args) :
    ReachRun tags P host s f stk (.op i args :: es) := fun hc E => by
  have e : E.plug ⟨s, f, xcode stk (.op i args :: es)⟩ =
      (Sim.ActiveCtx.suffix (.plain i :: expression (Binaryen.BExpr.lowerList es)) E).plug
        ⟨s, f, xcode stk args⟩ := by
    simp only [Sim.ActiveCtx.plug, xcode, code_op]
  rw [e]
  exact ih (args_chkP hc) _

theorem run_cont {s₂ : Store H} {f₂ : Frame} {stk₂ : List Val} {e : BExpr}
    (d : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂)))
    (ih : ReachRun tags P host s₂ f₂ stk₂ es) : ReachRun tags P host s f stk (e :: es) :=
  fun hc E => by
    obtain ⟨hst, hc₂⟩ := head_stepsP (P := P) (host := host) d hc
    exact reachRun_of_steps (E' := E) (plug_stepsP E hst) hc₂ ih

theorem run_callee {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hargs : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal stk₁)))
    (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (ih : CallReachRun tags P host s₁ a (stk₁.take ps.length).reverse) :
    ReachRun tags P host s f stk (.op (.call x) args :: es) := fun hc E => by
  obtain ⟨hpre, hS₁, hts₁, labels, ret, o, hf⟩ := site_runP (P := P) (host := host) hargs hc
  obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
  rw [callArity_eq hfi hty, Option.some.injEq, Prod.mk.injEq] at hpq
  obtain ⟨rfl, rfl⟩ := hpq
  obtain ⟨hx, hf'⟩ := func?_inv hfi
  have hcl : Steps P host ⟨s, f, xcode stk (.op (.call x) args :: es)⟩
      ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse a
        (.callRefType fi.type) (expression (Binaryen.BExpr.lowerList es))⟩ := by
    have h₁ := Steps.append (.plain (.call x) :: expression (Binaryen.BExpr.lowerList es)) hpre
    rw [xcode, code_op, ← callCode_split]
    refine h₁.tail ?_
    simpa using Step.ctx (P := P) (host := host) stk₁.reverse
      (expression (Binaryen.BExpr.lowerList es)) (Step.call hx hf')
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  obtain ⟨T, hT, hd⟩ := ih ⟨hS₁, hts₁, fi, ps, rs, funcs_of_func? hfi, hty, hlen⟩
    E f₁ _ (.callRefType fi.type) _ trivial
  exact ⟨T, (plug_stepsP E hcl).trans hT, hd⟩

theorem run_callInd {x : TableIdx} {y : TypeIdx} {ad : AddrType} {i : BitVec ad.intType.width}
    {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hargs : EvalOXP closedCallXP s f stk args
      (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
    (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s₁ f₁ x y ad i (some fa))
    (hfi : s₁.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (ih : CallReachRun tags P host s₁ fa (stk₁.take ps.length).reverse) :
    ReachRun tags P host s f stk (.op (.callIndirect x y) args :: es) := fun hc E => by
  obtain ⟨hpre, hS₁, hts₁, labels, ret, o, hf⟩ := site_runP (P := P) (host := host) hargs hc
  rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
  obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf
  simp only [List.length_cons] at hp
  have hcl : Steps P host ⟨s, f, xcode stk (.op (.callIndirect x y) args :: es)⟩
      ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse fa
        (.plain (.callRef y)) (expression (Binaryen.BExpr.lowerList es))⟩ := by
    have h₁ := Steps.append (.plain (.callIndirect x y) ::
      expression (Binaryen.BExpr.lowerList es)) hpre
    rw [xcode, code_op, ← callCode_split]
    refine h₁.trans ?_
    have e : vals (Val.num ⟨.int ad.intType, i⟩ :: stk₁).reverse ++
        .plain (.callIndirect x y) :: expression (Binaryen.BExpr.lowerList es) =
        vals stk₁.reverse ++ [aconst ad i, .plain (.callIndirect x y)] ++
          expression (Binaryen.BExpr.lowerList es) := by
      rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]; simp
    rw [e]
    exact Steps.ctx (P := P) (host := host) stk₁.reverse _
      (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  obtain ⟨T, hT, hd⟩ := ih ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hlen⟩
    E f₁ _ (.plain (.callRef y)) _ trivial
  exact ⟨T, (plug_stepsP E hcl).trans hT, hd⟩

theorem run_callRef {y : TypeIdx} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hargs : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (ih : CallReachRun tags P host s₁ fa (stk₁.take ps.length).reverse) :
    ReachRun tags P host s f stk (.op (.callRef y) args :: es) := fun hc E => by
  obtain ⟨hpre, hS₁, hts₁, labels, ret, o, hf⟩ := site_runP (P := P) (host := host) hargs hc
  rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
  obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf
  simp only [List.length_cons] at hp
  have hcl : Steps P host ⟨s, f, xcode stk (.op (.callRef y) args :: es)⟩
      ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse fa
        (.plain (.callRef y)) (expression (Binaryen.BExpr.lowerList es))⟩ := by
    have h₁ := Steps.append (.plain (.callRef y) :: expression (Binaryen.BExpr.lowerList es)) hpre
    rw [xcode, code_op, ← callCode_split]
    simpa [vals, Val.toAdmin] using h₁
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  obtain ⟨T, hT, hd⟩ := ih ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hlen⟩
    E f₁ _ (.plain (.callRef y)) _ trivial
  exact ⟨T, (plug_stepsP E hcl).trans hT, hd⟩

theorem run_cond {bt : BlockType} {c t el : List BExpr} (ih : ReachRun tags P host s f stk c) :
    ReachRun tags P host s f stk (.if_ bt c t el :: es) := fun hc E => by
  have e : E.plug ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ =
      (Sim.ActiveCtx.suffix (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
        (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)) E).plug
        ⟨s, f, xcode stk c⟩ := by
    simp only [Sim.ActiveCtx.plug, xcode, code_if]
  rw [e]
  exact ih (cond_chkP hc) _

theorem run_block {bt : BlockType} {body : List BExpr} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr)) (ih : ReachRun tags P host s f (stk.take np) body) :
    ReachRun tags P host s f stk (.block bt body :: es) := fun hc E => by
  obtain ⟨hp, hcb⟩ := block_chkP har hc
  have st := step_enter (P := P) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_block har)
    (expression (Binaryen.BExpr.lowerList es))
  have e : E.plug ⟨s, f, xcode stk (.block bt body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [xcode, code_block]
  refine reachRun_of_steps (E' := .label nr [] (stk.drop np).reverse
    (expression (Binaryen.BExpr.lowerList es)) E) ?_ hcb ih
  rw [e]
  simpa [Sim.ActiveCtx.plug, xcode] using Relation.ReflTransGen.single (E.step st)

theorem run_loop {bt : BlockType} {body : List BExpr} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr)) (ih : ReachRun tags P host s f (stk.take np) body) :
    ReachRun tags P host s f stk (.loop bt body :: es) := fun hc E => by
  obtain ⟨hp, hcb⟩ := loop_chkP har hc
  have st := step_enter (P := P) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har)
    (expression (Binaryen.BExpr.lowerList es))
  have e : E.plug ⟨s, f, xcode stk (.loop bt body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [xcode, code_loop]
  refine reachRun_of_steps (E' := .label np [.loop bt (Binaryen.BExpr.lowerList body)]
    (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) E) ?_ hcb ih
  rw [e]
  simpa [Sim.ActiveCtx.plug, xcode] using Relation.ReflTransGen.single (E.step st)

theorem run_try {bt : BlockType} {cs : List Catch} {body : List BExpr} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr)) (ih : ReachRun tags P host s f (stk.take np) body) :
    ReachRun tags P host s f stk (.tryTable bt cs body :: es) := fun hc E => by
  obtain ⟨hp, hcb⟩ := try_chkP har hc
  have hlen : (stk.take np).reverse.length = np := by
    simp only [List.length_reverse, List.length_take]; omega
  have st : Step P host ⟨s, f, vals stk.reverse ++
      .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩
      ⟨s, f, vals (stk.drop np).reverse ++ [.handler nr cs [.label nr []
        (vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body))]] ++
          expression (Binaryen.BExpr.lowerList es)⟩ := by
    have e : vals stk.reverse ++ .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es) =
        vals (stk.drop np).reverse ++ (vals (stk.take np).reverse ++
          [.plain (.tryTable bt cs (Binaryen.BExpr.lowerList body))]) ++
            expression (Binaryen.BExpr.lowerList es) := by
      rw [rev_take_drop stk np]; simp
    rw [e]
    exact Step.ctx _ _ (step_try har _ hlen)
  have e : E.plug ⟨s, f, xcode stk (.tryTable bt cs body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
      .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [xcode, code_tryTable]
  refine reachRun_of_steps (E' := .label nr [] [] []
    (.handler nr cs (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) E)) ?_ hcb ih
  rw [e]
  simpa [Sim.ActiveCtx.plug, xcode, vals] using Relation.ReflTransGen.single (E.step st)

theorem run_loopBack {vs : List Val} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (hbody : EvalOXP closedCallXP s f (stk.take np) body (s₁, f₁, .flow (.brk 0 vs)))
    (ih : ReachRun tags P host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es)) :
    ReachRun tags P host s f stk (.loop bt body :: es) := fun hc E => by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := id hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hck
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hb'' : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by rw [take_length_of_le hp]; exact hb'
  obtain ⟨ht₁, hA, hG⟩ := evalOXP_closed_good (P := P) (host := host) hbody hts
  obtain ⟨hok, inv, -⟩ := hA hS hb''
  obtain ⟨n', hn', hnv⟩ := hok
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hn'
  subst hn'
  have hw₀ : WP P host s f (xcode (stk.take np) body) (MatchP (s₁, f₁, .flow (.brk 0 vs))) :=
    hG hS hb''
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (wp_of_wpP (fun h => by cases h) hw₀)
  have hst := tg_loop_back (P := P) (host := host)
    (rest := expression (Binaryen.BExpr.lowerList es)) har hp hrun he hm hnv
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  have e : ∀ st', xcode st' (.loop bt body :: es) = vals st'.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es) :=
    fun st' => by rw [xcode, code_loop]
  refine reachRun_of_steps (E' := E) ?_ ⟨labels, ret, out, storeChk_inv inv hS,
    by rw [hlen]; exact chk_inv inv hck, ht₁⟩ ih
  rw [e, e]
  exact (plug_transGenP E hst).to_reflTransGen

theorem run_arm {cv : Val} {b : Bool} {bt : BlockType} {c t el : List BExpr} {np nr : Nat}
    (hcnd : EvalOXP closedCallXP s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))))
    (hb : truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (ih : ReachRun tags P host s₁ f₁ (stk₁.take np) (if b then t else el)) :
    ReachRun tags P host s f stk (.if_ bt c t el :: es) := fun hc E => by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := id hc
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  obtain ⟨hpre, -, -, hts₁⟩ := prefix_runP (P := P) (host := host) hcnd hS hco hts
  obtain ⟨-, hA, -⟩ := evalOXP_closed_good (P := P) (host := host) hcnd hts
  obtain ⟨inv1, hp, hbr, -⟩ := arity_if_pre (b := b) hS
    (fun hS' hc' => (arityE_of_arityP hA) hS' hc') har hck
  obtain ⟨ob, hob, -⟩ := endsAt_eq (chk_inv_endsAt inv1 hbr)
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  let R := expression (Binaryen.BExpr.lowerList es)
  have hif : Step P host ⟨s₁, f₁, vals (Val.i32 c₀ :: stk₁).reverse ++
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
      simpa using Step.ctx (P := P) (host := host) stk₁.reverse R
        (Step.ifFalse (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
          (b₂ := Binaryen.BExpr.lowerList el))
    · have h1 : (c₀ != 0) = true := by simpa using h0
      simp only [h1, ↓reduceIte]
      simpa using Step.ctx (P := P) (host := host) stk₁.reverse R
        (Step.ifTrue (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
          (b₂ := Binaryen.BExpr.lowerList el) h0)
  have hst := step_enter (P := P) (host := host) (s := s₁) (f := f₁) hp
    (step_block (B := Binaryen.BExpr.lowerList (if (c₀ != 0) then t else el)) har) R
  have e : E.plug ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ =
      E.plug ⟨s, f, xcode stk c ++ (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
        (Binaryen.BExpr.lowerList el)) :: R)⟩ := by
    rw [xcode, code_if]
  refine reachRun_of_steps (E' := .label nr [] (stk₁.drop np).reverse R E) ?_
    ⟨nr :: labels, ret, ob, storeChk_inv inv1 hS, by rw [take_length_of_le hp]; exact hob, hts₁⟩ ih
  rw [e]
  have h₁ := plug_stepsP (P := P) (host := host) E (Steps.append (.plain (.if_ bt
    (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R) hpre)
  refine h₁.trans ((Relation.ReflTransGen.single (E.step hif)).tail ?_)
  simpa [Sim.ActiveCtx.plug, xcode] using E.step hst

theorem run_host {a : Nat} {as : List Val} {fi : FuncInst H} {hh : H}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) :
    CallReachRun tags P host s a as := fun hcc E f pre cr rest hcr => by
  obtain ⟨-, -, fi', ps, rs, hfi', hty, hn⟩ := hcc
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨ps', rs', hex, hpl, -⟩ := expand_of_funcType hty
  refine ⟨_, .refl, decompose?_plug E ?_⟩
  have hn' : as.length = ps'.length := by rw [hn, ← hpl]
  have := decompose?_wrap (s := s) pre rest (decompose?_redex (vs := as) hcr hfi hex hn' hcode)
  show (decompose? s (Interp.callCode pre as a cr rest)).isSome
  simp only [Interp.callCode]
  rw [this]; rfl

theorem run_body {a : Nat} {as : List Val} {fi : FuncInst H} {fn : Func}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (ih : ReachRun tags P host s (Frame.forCall fi.module as fn.locals) [] (liftInstrs fn.body)) :
    CallReachRun tags P host s a as := fun hcc E f pre cr rest hcr => by
  obtain ⟨hS, hts, fi', ps, rs, hfi', hty, hn⟩ := hcc
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨ob, hob⟩ := body_chkP hS hfi hcode hty hn
  obtain ⟨T, hT, hd⟩ := ih ⟨[rs.length], rs.length, ob, hS, hob, hts⟩
    (calleeCtx E rs.length f pre rest)
  rw [calleeCtx_plug] at hT
  exact ⟨T, Relation.ReflTransGen.head (E.step (enter_callP (P := P) (host := host) (f := f)
    (pre := pre) (rest := rest) hcr hfi hcode hty hn)) hT, hd⟩

theorem run_frameTail {a a' n : Nat} {as as' : List Val} {fi : FuncInst H} {fn : Func}
    {f₂ : Frame} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hbody : EvalOXP closedCallXP s (Frame.forCall fi.module as fn.locals) []
      (liftInstrs fn.body) (s₁, f₂, .tail a' as' n))
    (ih : CallReachRun tags P host s₁ a' as') : CallReachRun tags P host s a as :=
  fun hcc E f pre cr rest hcr => by
    obtain ⟨hS, hts, fi', ps, rs, hfi', hty, hn⟩ := hcc
    rw [hfi] at hfi'; cases hfi'
    obtain ⟨c', hc', htg, hcc'⟩ := call_tail_stepsP (P := P) (host := host) hS hts hfi hcode hty
      hn hbody f hcr pre rest
    obtain ⟨T, hT, hd⟩ := ih hcc' E f pre c' rest hc'
    exact ⟨T, (plug_transGenP E htg).to_reflTransGen.trans hT, hd⟩

/-- **Reaches of checked problems and calls are Core runs to a host call**, in any context. -/
theorem hreach_core_both :
    (∀ s f stk es, HReach s f stk es → ReachRun tags P host s f stk es) ∧
      (∀ s a as, HCallReach s a as → CallReachRun tags P host s a as) := by
  refine ⟨fun s f stk es h => ?_, fun s a as h => ?_⟩
  · exact HReach.rec (motive_1 := fun s f stk es _ => ReachRun tags P host s f stk es)
      (motive_2 := fun s a as _ => CallReachRun tags P host s a as)
      (fun _ ih => run_args ih) (fun hd _ ih => run_cont hd ih)
      (fun hargs hfi hty _ ih => run_callee hargs hfi hty ih)
      (fun hargs hres hfi hty hy _ ih => run_callInd hargs hres hfi hty hy ih)
      (fun hargs hfi hty hy _ ih => run_callRef hargs hfi hty hy ih)
      (fun har _ ih => run_block har ih) (fun har _ ih => run_loop har ih)
      (fun har hbody _ ih => run_loopBack har hbody ih) (fun _ ih => run_cond ih)
      (fun hc hb har _ ih => run_arm hc hb har ih) (fun har _ ih => run_try har ih)
      (fun hfi hcode => run_host hfi hcode) (fun hfi hcode _ ih => run_body hfi hcode ih)
      (fun hfi hcode hbody _ ih => run_frameTail hfi hcode hbody ih) h
  · exact HCallReach.rec (motive_1 := fun s f stk es _ => ReachRun tags P host s f stk es)
      (motive_2 := fun s a as _ => CallReachRun tags P host s a as)
      (fun _ ih => run_args ih) (fun hd _ ih => run_cont hd ih)
      (fun hargs hfi hty _ ih => run_callee hargs hfi hty ih)
      (fun hargs hres hfi hty hy _ ih => run_callInd hargs hres hfi hty hy ih)
      (fun hargs hfi hty hy _ ih => run_callRef hargs hfi hty hy ih)
      (fun har _ ih => run_block har ih) (fun har _ ih => run_loop har ih)
      (fun har hbody _ ih => run_loopBack har hbody ih) (fun _ ih => run_cond ih)
      (fun hc hb har _ ih => run_arm hc hb har ih) (fun har _ ih => run_try har ih)
      (fun hfi hcode => run_host hfi hcode) (fun hfi hcode _ ih => run_body hfi hcode ih)
      (fun hfi hcode hbody _ ih => run_frameTail hfi hcode hbody ih) h

end Core

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
