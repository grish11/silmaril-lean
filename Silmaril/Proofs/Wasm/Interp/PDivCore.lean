module

public import Silmaril.Proofs.Wasm.Interp.PendClose
public import Silmaril.Proofs.Wasm.Interp.XDivCore
public import Silmaril.Wasm.Abstract.XDivergeP.Thms

/-!
# Divergence with exceptions and pending tail calls is Core 3.0 divergence (F5, proofs)

A problem of `ehExt tags`-checked code in a store with the tag invariants (`CheckedP`) that
diverges coinductively (`XDivergeP.EvalDivXP`) diverges in Core 3.0, in any evaluation context,
at every profile and host (`diverges_of_evalDivXP`); a diverging call (`XDivergeP.FunDivXP`)
diverges from its `call_ref` form (`diverges_of_funDivXP`), so a diverging invocation does
(`invoke_diverges_of_funDivXP`).

No typing is needed: the closed semantics with pending tail calls carries its own arity
premises, and its runs are Core runs on checked code (`evalOXP_closed_good`). The coinductive
invariant (`GoodDP`) has two kinds of states:

* a diverging problem plugged in a context (`progressP`, by strong induction on the size of the
  trees: every unfolding either takes a Core step — entering a block, a loop, a `try_table`
  (its handler and label) or a callee, or running a tree whose code is not already a value — or
  continues with strictly smaller trees);
* a diverging call in its `call_ref` form, below values and before code (`callState_adv`): one
  step enters the callee's frame; the body diverges, or it runs to its pending tail call, which
  leaves the body's label and then the frame (`return_call_ref-label`,
  `return_call_ref-frame-addr`), making the tail callee's call in the caller's frame: a call state
  again (`call_tail_stepsP`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- A checked problem: `ehExt tags`-checked code in a checked store with the tag invariants. -/
def CheckedP (tags : List TagInst) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) : Prop :=
  ∃ (labels : List Nat) (ret : Nat) (out : Option Nat), StoreChkE (ehExt tags) s.funcs ∧
    chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    TagsOk tags s

/-- A checked call: a checked store with the tag invariants, and a function at `a` whose
parameters are the arguments. -/
def CallChkP (tags : List TagInst) (s : Store H) (a : Nat) (args : List Val) : Prop :=
  StoreChkE (ehExt tags) s.funcs ∧ TagsOk tags s ∧
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ args.length = ps.length

/-- The code of a call in its `call_ref` form, below values `pre` and before code `rest`. -/
abbrev callCode (pre args : List Val) (a : Nat) (c : Admin) (rest : List Admin) : List Admin :=
  vals pre ++ (vals args ++ [.ref (.func a), c]) ++ rest

theorem plug_stepsP (E : Sim.ActiveCtx) {c c' : Config H} (h : Steps P host c c') :
    Steps P host (E.plug c) (E.plug c') := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (E.step st)

theorem plug_transGenP (E : Sim.ActiveCtx) {c c' : Config H}
    (h : Relation.TransGen (Step P host) c c') :
    Relation.TransGen (Step P host) (E.plug c) (E.plug c') := by
  induction h with
  | single st => exact .single (E.step st)
  | tail _ st ih => exact ih.tail (E.step st)

theorem chkE_nil_selfP {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} (o : Option Nat) : chkE ext F mi nl ret labels o [] = some o := by
  cases o <;> rfl

/-- On the instructions other than `throw` and `throw_ref`, the flat check of `ehExt` is that of
`tExt`. -/
theorem flatChkE_ehExt_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {h : Nat} {i : Instr} (h₁ : ∀ x, i ≠ .throw x)
    (h₂ : i ≠ .throwRef) :
    flatChkE (ehExt tags) F mi nl ret labels h i = flatChkE tExt F mi nl ret labels h i := by
  cases i <;> first | rfl | exact absurd rfl (h₁ _) | exact absurd rfl h₂

theorem callCode_split (stk : List Val) (k a : Nat) (c : Admin) (R : List Admin) :
    vals stk.reverse ++ [.ref (.func a), c] ++ R =
      callCode (stk.drop k).reverse (stk.take k).reverse a c R := by
  rw [rev_take_drop stk k]; simp [callCode]

/-! ## Terminating parts -/

section Runs

variable {tags : List TagInst}

/-- **A checked terminating prefix**: its Core run, and the invariants after it. -/
theorem prefix_runP {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
    {es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (d : EvalOXP closedCallXP s f stk es (s₁, f₁, .flow (.normal stk₁)))
    (hS : StoreChkE (ehExt tags) s.funcs)
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out)
    (hts : TagsOk tags s) :
    Steps P host ⟨s, f, xcode stk es⟩ ⟨s₁, f₁, vals stk₁.reverse⟩ ∧ out = some stk₁.length ∧
      EvalInvE (ehExt tags) s f (s₁, f₁, .trap) ∧ TagsOk tags s₁ := by
  obtain ⟨ht₁, hA, hG⟩ := evalOXP_closed_good (P := P) (host := host) d hts
  obtain ⟨hok, hinv, -⟩ := hA hS hc
  have hw₀ : WP P host s f (xcode stk es) (MatchP (s₁, f₁, .flow (.normal stk₁))) := hG hS hc
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (wp_of_wpP (fun h => by cases h) hw₀)
  have hc' := ends_normal hm he
  subst hc'
  exact ⟨hrun, hok, hinv, ht₁⟩

/-- **A head tree that runs normally**: Core runs the problem to the rest, checked. -/
theorem head_stepsP {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : Binaryen.BExpr}
    {es : List Binaryen.BExpr} (d : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂)))
    (hc : CheckedP tags s f stk (e :: es)) :
    Steps P host ⟨s, f, xcode stk (e :: es)⟩ ⟨s₂, f₂, xcode stk₂ es⟩ ∧ CheckedP tags s₂ f₂ stk₂ es := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hck
  have h1' : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) [e] =
      some o := chk_consE.mpr ⟨o, h1, chkE_nil_selfP o⟩
  obtain ⟨hrun, rfl, hinv, hts₂⟩ := prefix_runP (P := P) (host := host) d hS h1' hts
  refine ⟨?_, labels, ret, out, storeChk_inv hinv hS, chk_inv hinv h2, hts₂⟩
  have := Steps.append (expression (Binaryen.BExpr.lowerList es)) hrun
  simpa [xcode, expression, List.append_assoc] using this

/-- The arguments of a checked operator are checked. -/
theorem args_chkP {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} (hc : CheckedP tags s f stk (.op i args :: es)) :
    CheckedP tags s f stk args := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  exact ⟨labels, ret, oa, hS, ha, hts⟩

/-- The condition of a checked `if` is checked. -/
theorem cond_chkP {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {c t el es : List Binaryen.BExpr} (hc : CheckedP tags s f stk (.if_ bt c t el :: es)) :
    CheckedP tags s f stk c := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  exact ⟨labels, ret, oc, hS, hco, hts⟩

/-- The body of a checked block. -/
theorem block_chkP {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {body es : List Binaryen.BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hc : CheckedP tags s f stk (.block bt body :: es)) :
    np ≤ stk.length ∧ CheckedP tags s f (stk.take np) body := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hck
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  exact ⟨hp, nr :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', hts⟩

/-- The body of a checked loop. -/
theorem loop_chkP {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {body es : List Binaryen.BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hc : CheckedP tags s f stk (.loop bt body :: es)) :
    np ≤ stk.length ∧ CheckedP tags s f (stk.take np) body := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hck
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  exact ⟨hp, np :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', hts⟩

/-- The body of a checked `try_table`. -/
theorem try_chkP {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
    {body es : List Binaryen.BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hc : CheckedP tags s f stk (.tryTable bt cs body :: es)) :
    np ≤ stk.length ∧ CheckedP tags s f (stk.take np) body := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hck
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  exact ⟨hp, nr :: labels, ret, ob, hS, by rw [take_length_of_le hp]; exact hb', hts⟩

/-- **The site of an operator, after its checked arguments**: the Core run of the arguments,
the flat check there, and the invariants. -/
theorem site_runP {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
    {args es : List Binaryen.BExpr}
    (d : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal stk₁)))
    (hc : CheckedP tags s f stk (.op i args :: es)) :
    Steps P host ⟨s, f, xcode stk args⟩ ⟨s₁, f₁, vals stk₁.reverse⟩ ∧
      StoreChkE (ehExt tags) s₁.funcs ∧ TagsOk tags s₁ ∧ ∃ labels ret o,
        flatChkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o := by
  obtain ⟨labels, ret, out, hS, hck, hts⟩ := hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oa, ha, hf⟩ := chk1_opE h1
  obtain ⟨hrun, rfl, hinv, hts₁⟩ := prefix_runP (P := P) (host := host) d hS ha hts
  exact ⟨hrun, storeChk_inv hinv hS, hts₁, labels, ret, o, flatChk_inv hinv (hf _ rfl)⟩

end Runs

/-! ## Calls -/

section Calls

variable {tags : List TagInst}

/-- **Entering a callee** from its `call_ref` form. -/
theorem enter_callP {s : Store H} {f : Frame} {pre args : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    (hcr : c.IsCallRef) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : args.length = ps.length) :
    Step P host ⟨s, f, callCode pre args a c rest⟩
      ⟨s, f, vals pre ++ [.frame rs.length (Frame.forCall fi.module args fn.locals)
        [.label rs.length [] (expression fn.body)]] ++ rest⟩ := by
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : args.length = ps'.length := by omega
  rw [← hrl]
  exact Step.ctx pre rest (Step.callRefFunc hcr hfi hex hn' hcode)

/-- The check of a callee body. -/
theorem body_chkP {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hS : StoreChkE (ehExt tags) s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : args.length = ps.length) :
    ∃ ob, chkE (ehExt tags) s.funcs (Frame.forCall fi.module args fn.locals).module
      (Frame.forCall fi.module args fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
  obtain ⟨ob, hb, -⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hlen : (Frame.forCall fi.module args fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hn
  exact ⟨ob, by rw [hlen]; exact hb⟩

/-- **A callee body ending in a pending tail call**: from the call's `call_ref` form, Core enters
the callee, runs its body to the pending tail call, leaves the body's label and the frame, and
makes the tail callee's call in the caller's frame. -/
theorem call_tail_stepsP {s s₁ : Store H} {f₂ : Frame} {a a' n : Nat} {args args' : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : args.length = ps.length)
    (hbody : EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₁, f₂, .tail a' args' n))
    (f : Frame) {c : Admin} (hcr : c.IsCallRef) (pre : List Val) (rest : List Admin) :
    ∃ c', c'.IsCallRef ∧ Relation.TransGen (Step P host) ⟨s, f, callCode pre args a c rest⟩
      ⟨s₁, f, callCode pre args' a' c' rest⟩ ∧ CallChkP tags s₁ a' args' := by
  obtain ⟨ht₁, hA, hCore⟩ := evalOXP_closed_good (P := P) (host := host) hbody hts
  obtain ⟨ob, hb'⟩ := body_chkP hS hfi hcode hty hn
  obtain ⟨-, hinv, hw⟩ := hA hS hb'
  have hwb := hCore hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, -⟩ := hw a' args' n rfl
  obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
  have hargs' : args'.length = ps₂'.length := by omega
  obtain ⟨vs₁, c', rest₀, hrun, hc'⟩ := run_of_wpP_tail hwb
  have enter := enter_callP (P := P) (host := host) (f := f) (pre := pre) (rest := rest) hcr hfi
    hcode hty hn
  have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
    (Steps.label rs.length [] (show Steps P host
      ⟨s, Frame.forCall fi.module args fn.locals, expression fn.body⟩
      ⟨s₁, f₂, vals (vs₁ ++ args') ++ .ref (.func a') :: c' :: rest₀⟩ from by simpa [vals] using hrun))
  have exit := frame_tail_exit (P := P) (host := host) (s := s₁) (f := f) (k := rs.length)
    (F := f₂) (vs₁ := vs₁) (rest := rest₀) hc' hfi₂ hex₂ hargs'
  refine ⟨c'.retToCallIn f₂.module, isCallRef_retToCallIn hc' _, ?_, hinv.1.2.1 hS, ht₁, fi₂, ps₂,
    rs₂, hfi₂, hty₂, hargs⟩
  exact Relation.TransGen.head' enter (Steps.ctx pre rest (inner.trans exit))

end Calls

/-! ## Progress -/

/-- **The coinductive invariant**: a diverging checked problem in a context, or a diverging
checked call in its `call_ref` form, in a context. -/
def GoodDP (tags : List TagInst) (c : Config H) : Prop :=
  (∃ (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) (E : Sim.ActiveCtx),
    c = E.plug ⟨s, f, xcode stk es⟩ ∧ EvalDivXP s f stk es ∧ CheckedP tags s f stk es) ∨
  (∃ (s : Store H) (f : Frame) (pre args : List Val) (a : Nat) (c₀ : Admin) (rest : List Admin)
    (E : Sim.ActiveCtx), c = E.plug ⟨s, f, callCode pre args a c₀ rest⟩ ∧ c₀.IsCallRef ∧
      FunDivXP s a args ∧ CallChkP tags s a args)

/-- At least one Core step to a good state. -/
def AdvP (tags : List TagInst) (P : Numerics.Profile) (host : HostSemantics H) (c : Config H) :
    Prop :=
  ∃ c', Relation.TransGen (Step P host) c c' ∧ GoodDP tags c'

theorem AdvP.of_steps {tags : List TagInst} {c c' : Config H} (h : Steps P host c c')
    (ha : AdvP tags P host c') : AdvP tags P host c := by
  obtain ⟨c'', h', hg⟩ := ha
  exact ⟨c'', Relation.TransGen.trans_right h h', hg⟩

/-- **A diverging call advances**: one step into the callee, and on to a diverging body or, past
the body's pending tail call, to the diverging tail callee's call. -/
theorem callState_adv {tags : List TagInst} {s : Store H} {f : Frame} {pre args : List Val}
    {a : Nat} {c : Admin} {rest : List Admin} (E : Sim.ActiveCtx) (hcr : c.IsCallRef)
    (hd : FunDivXP s a args) (hcc : CallChkP tags s a args) :
    AdvP tags P host (E.plug ⟨s, f, callCode pre args a c rest⟩) := by
  obtain ⟨hS, hts, fi, ps, rs, hfi, hty, hn⟩ := hcc
  rcases funDivXP_iff_step.1 hd with ⟨hfi', hcode, hb⟩ | ⟨hfi', hcode, hbody, hb⟩
  · rw [hfi] at hfi'; cases hfi'
    obtain ⟨ob, hob⟩ := body_chkP hS hfi hcode hty hn
    refine ⟨_, plug_transGenP E (.single (enter_callP (P := P) (host := host) (f := f) (pre := pre)
      (rest := rest) hcr hfi hcode hty hn)), .inl ⟨_, _, [], _, calleeCtx E rs.length f pre rest,
        (calleeCtx_plug E rs.length f _ pre rest s _).symm, hb, [rs.length], rs.length, ob, hS,
        hob, hts⟩⟩
  · rw [hfi] at hfi'; cases hfi'
    obtain ⟨c', hc', htg, hcc'⟩ := call_tail_stepsP (P := P) (host := host) hS hts hfi hcode hty hn
      hbody f hcr pre rest
    exact ⟨_, plug_transGenP E htg, .inr ⟨_, f, pre, _, _, c', rest, E, rfl, hc', hb, hcc'⟩⟩

/-- **Progress**: a checked, diverging problem in any context advances. -/
theorem progressP {tags : List TagInst} : ∀ (n : Nat) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr}, sizeOf es = n → EvalDivXP s f stk es → CheckedP tags s f stk es →
    ∀ E : Sim.ActiveCtx, AdvP tags P host (E.plug ⟨s, f, xcode stk es⟩) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f stk es hn hd hc E
  cases evalDivXP_iff_step.1 hd with
  | @args _ _ _ i args es h =>
    have e : E.plug ⟨s, f, xcode stk (.op i args :: es)⟩ =
        (Sim.ActiveCtx.suffix (.plain i :: expression (Binaryen.BExpr.lowerList es)) E).plug
          ⟨s, f, xcode stk args⟩ := by
      simp only [Sim.ActiveCtx.plug, xcode, code_op]
    rw [e]
    exact ih (sizeOf args) (by rw [← hn]; simp; omega) rfl h (args_chkP hc) _
  | @cont _ s₂ _ f₂ _ stk₂ e es d hk =>
    obtain ⟨hst, hc₂⟩ := head_stepsP (P := P) (host := host) d hc
    rcases Relation.ReflTransGen.cases_head hst with heq | ⟨c, st, rest⟩
    · rw [heq]
      exact ih (sizeOf es) (by rw [← hn]; simp) rfl hk hc₂ E
    · exact ⟨_, plug_transGenP E (Relation.TransGen.head' st rest), .inl ⟨_, _, _, _, E, rfl, hk, hc₂⟩⟩
  | @callee _ s₁ _ f₁ _ stk₁ x args es a fi ps rs hargs hfi hty h =>
    obtain ⟨hpre, hS₁, hts₁, labels, ret, o, hf⟩ := site_runP (P := P) (host := host) hargs hc
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    rw [callArity_eq hfi hty, Option.some.injEq, Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    obtain ⟨hx, hf'⟩ := func?_inv hfi
    let R := expression (Binaryen.BExpr.lowerList es)
    have hcl : Steps P host ⟨s, f, xcode stk (.op (.call x) args :: es)⟩
        ⟨s₁, f₁, callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse a
          (.callRefType fi.type) R⟩ := by
      have h₁ := Steps.append (.plain (.call x) :: R) hpre
      rw [xcode, code_op, ← callCode_split]
      refine h₁.tail ?_
      simpa using Step.ctx (P := P) (host := host) stk₁.reverse R (Step.call hx hf')
    have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
      simp only [List.length_reverse, List.length_take]; omega
    exact AdvP.of_steps (plug_stepsP E hcl) (callState_adv E trivial h
      ⟨hS₁, hts₁, fi, ps, rs, funcs_of_func? hfi, hty, hlen⟩)
  | @callIndCallee _ s₁ _ f₁ _ stk₁ x y args es ad i fa fi ps rs hargs hres hfi hty hy h =>
    obtain ⟨hpre, hS₁, hts₁, labels, ret, o, hf⟩ := site_runP (P := P) (host := host) hargs hc
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
    obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf
    simp only [List.length_cons] at hp
    let R := expression (Binaryen.BExpr.lowerList es)
    have hcl : Steps P host ⟨s, f, xcode stk (.op (.callIndirect x y) args :: es)⟩
        ⟨s₁, f₁, callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse fa
          (.plain (.callRef y)) R⟩ := by
      have h₁ := Steps.append (.plain (.callIndirect x y) :: R) hpre
      rw [xcode, code_op, ← callCode_split]
      refine h₁.trans ?_
      have e : vals (Val.num ⟨.int ad.intType, i⟩ :: stk₁).reverse ++ .plain (.callIndirect x y) :: R =
          vals stk₁.reverse ++ [aconst ad i, .plain (.callIndirect x y)] ++ R := by
        rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]; simp
      rw [e]
      exact Steps.ctx (P := P) (host := host) stk₁.reverse R
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
    have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
      simp only [List.length_reverse, List.length_take]; omega
    exact AdvP.of_steps (plug_stepsP E hcl) (callState_adv E trivial h
      ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hlen⟩)
  | @callRefCallee _ s₁ _ f₁ _ stk₁ y args es fa fi ps rs hargs hfi hty hy h =>
    obtain ⟨hpre, hS₁, hts₁, labels, ret, o, hf⟩ := site_runP (P := P) (host := host) hargs hc
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf
    simp only [List.length_cons] at hp
    let R := expression (Binaryen.BExpr.lowerList es)
    have hcl : Steps P host ⟨s, f, xcode stk (.op (.callRef y) args :: es)⟩
        ⟨s₁, f₁, callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse fa
          (.plain (.callRef y)) R⟩ := by
      have h₁ := Steps.append (.plain (.callRef y) :: R) hpre
      rw [xcode, code_op, ← callCode_split]
      simpa [vals, Val.toAdmin] using h₁
    have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
      simp only [List.length_reverse, List.length_take]; omega
    exact AdvP.of_steps (plug_stepsP E hcl) (callState_adv E trivial h
      ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hlen⟩)
  | @cond _ _ _ bt c t el es h =>
    have e : E.plug ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ =
        (Sim.ActiveCtx.suffix (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
          (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)) E).plug
          ⟨s, f, xcode stk c⟩ := by
      simp only [Sim.ActiveCtx.plug, xcode, code_if]
    rw [e]
    exact ih (sizeOf c) (by rw [← hn]; simp; omega) rfl h (cond_chkP hc) _
  | @block _ _ _ bt body es np nr har h =>
    obtain ⟨hp, hcb⟩ := block_chkP har hc
    have st := step_enter (P := P) (host := host) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (step_block har) (expression (Binaryen.BExpr.lowerList es))
    refine ⟨_, ?_, .inl ⟨s, f, stk.take np, body, .label nr [] (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es)) E, rfl, h, hcb⟩⟩
    have e : E.plug ⟨s, f, xcode stk (.block bt body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [xcode, code_block]
    rw [e]
    simpa [Sim.ActiveCtx.plug, xcode] using Relation.TransGen.single (E.step st)
  | @loop _ _ _ bt body es np nr har h =>
    obtain ⟨hp, hcb⟩ := loop_chkP har hc
    have st := step_enter (P := P) (host := host) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (step_loop har) (expression (Binaryen.BExpr.lowerList es))
    refine ⟨_, ?_, .inl ⟨s, f, stk.take np, body, .label np [.loop bt (Binaryen.BExpr.lowerList body)]
      (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) E, rfl, h, hcb⟩⟩
    have e : E.plug ⟨s, f, xcode stk (.loop bt body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
        .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [xcode, code_loop]
    rw [e]
    simpa [Sim.ActiveCtx.plug, xcode] using Relation.TransGen.single (E.step st)
  | @try_ _ _ _ bt cs body es np nr har h =>
    obtain ⟨hp, hcb⟩ := try_chkP har hc
    let R := expression (Binaryen.BExpr.lowerList es)
    have hlen : (stk.take np).reverse.length = np := by
      simp only [List.length_reverse, List.length_take]; omega
    have st : Step P host ⟨s, f, vals stk.reverse ++
        .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) :: R⟩
        ⟨s, f, vals (stk.drop np).reverse ++ [.handler nr cs [.label nr []
          (vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body))]] ++ R⟩ := by
      have e : vals stk.reverse ++ .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) :: R =
          vals (stk.drop np).reverse ++ (vals (stk.take np).reverse ++
            [.plain (.tryTable bt cs (Binaryen.BExpr.lowerList body))]) ++ R := by
        rw [rev_take_drop stk np]; simp
      rw [e]
      exact Step.ctx _ R (step_try har _ hlen)
    refine ⟨_, ?_, .inl ⟨s, f, stk.take np, body, .label nr [] [] []
      (.handler nr cs (stk.drop np).reverse R E), rfl, h, hcb⟩⟩
    have e : E.plug ⟨s, f, xcode stk (.tryTable bt cs body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
        .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) :: R⟩ := by
      rw [xcode, code_tryTable]
    rw [e]
    simpa [Sim.ActiveCtx.plug, xcode, vals] using Relation.TransGen.single (E.step st)
  | @loopBack _ s₁ _ f₁ _ vs bt body es np nr har hbody hk =>
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
    refine ⟨_, ?_, .inl ⟨_, _, _, _, E, rfl, hk, labels, ret, out, storeChk_inv inv hS,
      by rw [hlen]; exact chk_inv inv hck, ht₁⟩⟩
    have e : ∀ st', xcode st' (.loop bt body :: es) = vals st'.reverse ++
        .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es) :=
      fun st' => by rw [xcode, code_loop]
    rw [e, e]
    exact plug_transGenP E hst
  | @arm _ s₁ _ f₁ _ stk₁ cv b bt c t el es np nr hcnd hb har h =>
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
    refine ⟨_, ?_, .inl ⟨s₁, f₁, stk₁.take np, (if (c₀ != 0) then t else el),
      .label nr [] (stk₁.drop np).reverse R E, rfl, h, nr :: labels, ret, ob,
      storeChk_inv inv1 hS, by rw [take_length_of_le hp]; exact hob, hts₁⟩⟩
    have e : E.plug ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ =
        E.plug ⟨s, f, xcode stk c ++ (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
          (Binaryen.BExpr.lowerList el)) :: R)⟩ := by
      rw [xcode, code_if]
    rw [e]
    have h₁ := plug_stepsP (P := P) (host := host) E (Steps.append (.plain (.if_ bt
      (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R) hpre)
    have h₂ : Relation.TransGen (Step P host) (E.plug ⟨s₁, f₁, vals (Val.i32 c₀ :: stk₁).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R⟩)
        ((Sim.ActiveCtx.label nr [] (stk₁.drop np).reverse R E).plug
          ⟨s₁, f₁, xcode (stk₁.take np) (if (c₀ != 0) then t else el)⟩) := by
      refine (Relation.TransGen.single (E.step hif)).tail ?_
      simpa [Sim.ActiveCtx.plug, xcode] using E.step hst
    exact Relation.TransGen.trans_right h₁ h₂

/-- Every good state advances. -/
theorem goodDP_adv {tags : List TagInst} {c : Config H} (hg : GoodDP tags c) : AdvP tags P host c := by
  rcases hg with ⟨s, f, stk, es, E, rfl, hd, hc⟩ | ⟨s, f, pre, args, a, c₀, rest, E, rfl, hcr, hd, hcc⟩
  · exact progressP _ rfl hd hc E
  · exact callState_adv E hcr hd hcc

/-- From a good state, Core diverges. -/
theorem diverges_of_goodDP {tags : List TagInst} {c : Config H} (hg : GoodDP tags c) :
    Diverges P host c := by
  refine InfiniteTrace.coinduct (fun c => ∃ g, GoodDP tags g ∧ Relation.ReflTransGen (Step P host) c g)
    ?_ ⟨c, hg, .refl⟩
  rintro c ⟨g, hg, hp⟩
  rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨c₁, hstep, hp'⟩
  · obtain ⟨c', hc', hg'⟩ := goodDP_adv (P := P) (host := host) hg
    obtain ⟨c₁, hstep, hp'⟩ := Relation.TransGen.head'_iff.mp hc'
    exact ⟨c₁, hstep, c', hg', hp'⟩
  · exact ⟨c₁, hstep, g, hg, hp'⟩

/-- **Divergence with pending tail calls is Core 3.0 divergence**, for checked problems, in any
context, at every profile and host. -/
theorem diverges_of_evalDivXP {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (hd : EvalDivXP s f stk es) (hc : CheckedP tags s f stk es)
    (E : Sim.ActiveCtx) : Diverges P host (E.plug ⟨s, f, xcode stk es⟩) :=
  diverges_of_goodDP (.inl ⟨s, f, stk, es, E, rfl, hd, hc⟩)

/-- **A diverging call diverges in Core 3.0** from its `call_ref` form, in any context. -/
theorem diverges_of_funDivXP {tags : List TagInst} {s : Store H} {f : Frame} {pre args : List Val}
    {a : Nat} {c : Admin} {rest : List Admin} (hd : FunDivXP s a args) (hcc : CallChkP tags s a args)
    (hcr : c.IsCallRef) (E : Sim.ActiveCtx) :
    Diverges P host (E.plug ⟨s, f, callCode pre args a c rest⟩) :=
  diverges_of_goodDP (.inr ⟨s, f, pre, args, a, c, rest, E, rfl, hcr, hd, hcc⟩)

/-- **A diverging invocation diverges in Core 3.0**, on an `ehExt tags`-checked store with the
tag invariants, at every profile and host. -/
theorem invoke_diverges_of_funDivXP {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hd : FunDivXP s a vs) : Diverges P host (invoke s a vs) := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  have hD := diverges_of_funDivXP (P := P) (host := host) (f := {}) (pre := []) (rest := [])
    (c := .callRefType fi.type) hd ⟨hS, hts, fi, _, _, hfi, hty, hvs.length_eq⟩ trivial .hole
  simpa [invoke, hfi, Sim.ActiveCtx.plug, callCode, vals] using hD

end Silmaril.Wasm.Interp
