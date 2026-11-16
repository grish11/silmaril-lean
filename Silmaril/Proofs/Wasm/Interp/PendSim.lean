module

public import Silmaril.Proofs.Wasm.Interp.EHSim
public import Silmaril.Wasm.Abstract.CallXP.Defs

/-!
# Forward simulation with pending tail calls (F5, proofs)

Every `CallXP.EvalOXP C` run of `ehExt tags`-checked code is a Core 3.0 run with exceptions on
(`evalOXP_goodP`), for **all** call forms: direct, indirect and reference calls, and the three
tail call forms. A body result is a flow or a pending tail call (`CallXP.POut`), so the Core
postcondition is `MatchP`:

* a flow `fl` is matched as `Match` does, or, for a trap, it may be Core's pending **null** tail
  call (`Outcome.tailNull`), which traps only when the frame is left
  (`return_call_ref-frame-null`); the two are kept apart;
* a pending tail call `tail a args n` is Core's pending tail call `Outcome.tail (vs₁ ++ args) a c`
  (`c` a `RETURN_CALL_REF` form), in the same store and frame. It leaves every label
  (`return_call_ref-label`) and every handler (`return_call_ref-handler`, `handler_step_tail`)
  untouched; the frame (`PendClose`) is where it is made.

The arity side (`ArityGoodP`) checks a pending tail call against the function's result arity
(`POutOk`) and records the callee's facts (`TailWF`: its instance and type at the address, and
its parameter count matching the arguments), which the frame needs to make the call.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## The postcondition and the invariants -/

/-- **The Core postcondition of a body result with pending tail calls.** A flow is matched as by
`Match`; a trap may also be Core's pending null tail call (which traps only at the frame). A
pending tail call is Core's pending tail call of the same callee on the same arguments (on top
of any values `vs₁`), in the same store and frame. -/
def MatchP (r : Store H × Frame × POut) : Post H := fun s f o =>
  match r.2.2 with
  | .flow fl => Match (r.1, r.2.1, fl) s f o ∨
      (fl = .trap ∧ ∃ vs c, o = .tailNull vs c ∧ c.IsReturnCallRef ∧ s = r.1 ∧ f = r.2.1)
  | .tail a args _ =>
      ∃ vs₁ c, o = .tail (vs₁ ++ args) a c ∧ c.IsReturnCallRef ∧ s = r.1 ∧ f = r.2.1

/-- What the arity check says about a body result: a flow as `FlowOkE`, a pending tail call
returns the function's own result arity. -/
def POutOk (eh : Bool) (labels : List Nat) (ret : Nat) (out : Option Nat) : POut → Prop
  | .flow fl => FlowOkE eh labels ret out fl
  | .tail _ _ n => n = ret

/-- **The callee of a pending tail call is well formed**: it is a function instance of the
result's store, of a type whose parameters are the arguments and whose results are `n`. -/
def TailWF (r : Store H × Frame × POut) : Prop :=
  ∀ a args n, r.2.2 = .tail a args n → ∃ (fi : FuncInst H) (ps rs : List Validation.CValType),
    r.1.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    args.length = ps.length ∧ rs.length = n

/-- The arity invariant of an `EvalOXP` run (`ArityGoodE` with `POutOk` and `TailWF`). The
store and frame invariants (`EvalInvE`) do not read the flow. -/
def ArityGoodP (ext : ExtArity H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) (r : Store H × Frame × POut) (eh : Bool := false) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChkE ext s.funcs →
    chkE ext s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    POutOk eh labels ret out r.2.2 ∧ EvalInvE ext s f (r.1, r.2.1, .trap) ∧ TailWF r

/-- **The Core-run invariant with pending tail calls**: `CoreGoodQ` with the constant
postcondition `MatchP r` (its flow argument is unused). -/
abbrev CoreGoodP (ext : ExtArity H) (P : Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) (r : Store H × Frame × POut) : Prop :=
  CoreGoodQ ext P host (fun _ _ => MatchP r) s f stk es (r.1, r.2.1, .trap)

/-- **A sound call oracle in every `call_ref` form**, for the checker `ext` and exception
capability `eh` (`OracleSoundT`, generalised). -/
def OracleSoundTE (ext : ExtArity H) (P : Numerics.Profile) (host : HostSemantics H)
    (C : Abstract.CallRel H) (eh : Bool := false) : Prop :=
  ∀ (s s₂ : Store H) (f : Frame) (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType)
    (us : List Val) (fl : Binaryen.Flow) (c : Admin),
    StoreChkE ext s.funcs → s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length → c.IsCallRef → C s a us (s₂, fl) →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOkE eh [rs.length] rs.length ob fl ∧
        FuncsGoodE ext s.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₂, f, vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₂, f, [.trap]⟩)

theorem OracleSoundTE.soundE {ext : ExtArity H} {C : Abstract.CallRel H} {eh : Bool}
    (hC : OracleSoundTE ext P host C eh) : OracleSoundE ext P host C eh :=
  fun s s₂ f a fi ps rs us fl hS hfi hty hn hcall =>
    hC s s₂ f a fi ps rs us fl (.callRefType fi.type) hS hfi hty hn trivial hcall

/-! ## `MatchP` and runs -/

section Runs

set_option linter.unusedSectionVars false

variable {s s₁ : Store H} {f f₁ : Frame}

theorem matchP_flow_iff {fl : Binaryen.Flow} {s' : Store H} {f' : Frame} {o : Outcome} :
    MatchP (s₁, f₁, .flow fl) s' f' o ↔ Match (s₁, f₁, fl) s' f' o ∨
      (fl = .trap ∧ ∃ vs c, o = .tailNull vs c ∧ c.IsReturnCallRef ∧ s' = s₁ ∧ f' = f₁) :=
  Iff.rfl

theorem matchP_tail_iff {a n : Nat} {args : List Val} {s' : Store H} {f' : Frame} {o : Outcome} :
    MatchP (s₁, f₁, .tail a args n) s' f' o ↔
      ∃ vs₁ c, o = .tail (vs₁ ++ args) a c ∧ c.IsReturnCallRef ∧ s' = s₁ ∧ f' = f₁ :=
  Iff.rfl

/-- `Match ≤ MatchP`. -/
theorem wpP_of_wp {c : List Admin} {fl : Binaryen.Flow} (h : WP P host s f c (Match (s₁, f₁, fl))) :
    WP P host s f c (MatchP (s₁, f₁, .flow fl)) :=
  WP.mono h fun _ _ _ hm => .inl hm

/-- Off a trap, `MatchP` is `Match`. -/
theorem wp_of_wpP {c : List Admin} {fl : Binaryen.Flow} (hfl : fl ≠ .trap)
    (h : WP P host s f c (MatchP (s₁, f₁, .flow fl))) : WP P host s f c (Match (s₁, f₁, fl)) :=
  WP.mono h fun _ _ _ hm => by
    rcases matchP_flow_iff.mp hm with hm | ⟨ht, -⟩
    · exact hm
    · exact absurd ht hfl

/-- A `WP` for `MatchP` of a flow: the matched run, or a run to a pending null tail call of a
trapping result. -/
theorem run_of_wpP_flow {c : List Admin} {fl : Binaryen.Flow}
    (h : WP P host s f c (MatchP (s₁, f₁, .flow fl))) :
    (∃ c' o, Steps P host ⟨s, f, c⟩ ⟨s₁, f₁, c'⟩ ∧ o.Ends c' ∧ FlowMatch fl o) ∨
      (fl = .trap ∧ ∃ vs c' rest, Steps P host ⟨s, f, c⟩
        ⟨s₁, f₁, vals vs ++ .ref .null :: c' :: rest⟩ ∧ c'.IsReturnCallRef) := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  rcases matchP_flow_iff.mp hq with ⟨rfl, rfl, hm⟩ | ⟨ht, vs, c₀, rfl, hc, rfl, rfl⟩
  · exact .inl ⟨c', o, hs, he, hm⟩
  · obtain ⟨-, rest, rfl⟩ := he
    exact .inr ⟨ht, vs, c₀, rest, hs, hc⟩

/-- A `WP` for `MatchP` of a pending tail call: a run to Core's pending tail call. -/
theorem run_of_wpP_tail {c : List Admin} {a n : Nat} {args : List Val}
    (h : WP P host s f c (MatchP (s₁, f₁, .tail a args n))) :
    ∃ vs₁ c' rest, Steps P host ⟨s, f, c⟩
      ⟨s₁, f₁, vals (vs₁ ++ args) ++ .ref (.func a) :: c' :: rest⟩ ∧ c'.IsReturnCallRef := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  obtain ⟨vs₁, c₀, rfl, hc, rfl, rfl⟩ := matchP_tail_iff.mp hq
  obtain ⟨-, rest, rfl⟩ := he
  exact ⟨vs₁, c₀, rest, hs, hc⟩

/-- **A pending tail call is a final form for `MatchP`**, in a value prefix and before code. -/
theorem wp_tailP {a n : Nat} {vs₁ args : List Val} {c : Admin} (hc : c.IsReturnCallRef)
    (pre : List Val) (rest rest' : List Admin) :
    WP P host s₁ f₁ (vals pre ++ (vals (vs₁ ++ args) ++ .ref (.func a) :: c :: rest) ++ rest')
      (MatchP (s₁, f₁, .tail a args n)) :=
  ⟨s₁, f₁, _, .tail (pre ++ vs₁ ++ args) a c, .refl, ⟨hc, rest ++ rest', by simp⟩,
    matchP_tail_iff.mpr ⟨pre ++ vs₁, c, by simp, hc, rfl, rfl⟩⟩

/-- **A pending null tail call is a final form for `MatchP` of a trap.** -/
theorem wp_tailNullP {vs : List Val} {c : Admin} (hc : c.IsReturnCallRef) (pre : List Val)
    (rest rest' : List Admin) :
    WP P host s₁ f₁ (vals pre ++ (vals vs ++ .ref .null :: c :: rest) ++ rest')
      (MatchP (s₁, f₁, .flow .trap)) :=
  ⟨s₁, f₁, _, .tailNull (pre ++ vs) c, .refl, ⟨hc, rest ++ rest', by simp⟩,
    matchP_flow_iff.mpr (.inr ⟨rfl, _, c, rfl, hc, rfl, rfl⟩)⟩

/-- **A handler around a pending tail call steps to it** (`return_call_ref-handler`). -/
theorem handler_step_tail {k : Nat} {cs : List Catch} {vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) :
    Step P host ⟨s, f, [.handler k cs (vals vs ++ .ref (.func a) :: c :: rest)]⟩
      ⟨s, f, vals vs ++ .ref (.func a) :: c :: []⟩ := by
  have := Step.returnCallRefHandler (P := P) (host := host) (s := s) (f := f) (k := k)
    (cs := cs) (vs := vs ++ [.ref (.func a)]) (rest := rest) hc
  simpa [vals, Val.toAdmin] using this

/-- **A handler around a pending null tail call steps to it** (`return_call_ref-handler`). -/
theorem handler_step_tailNull {k : Nat} {cs : List Catch} {vs : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) :
    Step P host ⟨s, f, [.handler k cs (vals vs ++ .ref .null :: c :: rest)]⟩
      ⟨s, f, vals vs ++ .ref .null :: c :: []⟩ := by
  have := Step.returnCallRefHandler (P := P) (host := host) (s := s) (f := f) (k := k)
    (cs := cs) (vs := vs ++ [.ref .null]) (rest := rest) hc
  simpa [vals, Val.toAdmin] using this

/-- **A sequence whose first part ends abruptly**, for `MatchP`. -/
theorem wp_append_abruptP {c rest : List Admin} {o : POut}
    (h : WP P host s f c (MatchP (s₁, f₁, o))) (hn : ¬ o.IsNormal) :
    WP P host s f (c ++ rest) (MatchP (s₁, f₁, o)) := by
  cases o with
  | flow fl =>
    rcases run_of_wpP_flow h with ⟨c', o, hst, he, hm⟩ | ⟨rfl, vs, c', rest₀, hst, hc⟩
    · exact wpP_of_wp (wp_append_abrupt' ⟨_, _, c', o, hst, he, rfl, rfl, hm⟩ hn)
    · have hw := wp_tailNullP (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (vs := vs) hc []
        rest₀ rest
      exact WP.steps (Steps.append rest hst) (by simpa [vals] using hw)
  | tail a args n =>
    obtain ⟨vs₁, c', rest₀, hst, hc⟩ := run_of_wpP_tail h
    have hw := wp_tailP (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (a := a) (n := n) (vs₁ := vs₁)
      (args := args) hc []
      rest₀ rest
    exact WP.steps (Steps.append rest hst) (by simpa [vals] using hw)

/-- **Leaving a label by an escaping result**, for `MatchP`: a flow as `exit_abrupt`, a
pending (null) tail call by `return_call_ref-label`. -/
theorem wp_label_escP {code body rest : List Admin} {pre : List Val} {k : Nat}
    {cont : List Instr} {o : POut}
    (enter : Steps P host ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.label k cont body] ++ rest⟩)
    (hb : WP P host s f body (MatchP (s₁, f₁, o))) (ho : o.Escapes) :
    WP P host s f code (MatchP (s₁, f₁, o)) := by
  cases o with
  | flow fl =>
    rcases run_of_wpP_flow hb with ⟨c', o, hrun, he, hm⟩ | ⟨rfl, vs, c', rest₀, hrun, hc⟩
    · have inner := Steps.ctx (P := P) (host := host) pre rest (Steps.label k cont hrun)
      exact wpP_of_wp (WP.steps (enter.trans inner) (exit_abrupt he hm (.inr ⟨ho, rfl⟩) pre rest))
    · have inner := Steps.ctx (P := P) (host := host) pre rest (Steps.label k cont hrun)
      have out := Steps.ctx (P := P) (host := host) pre rest
        (.single (label_step_tailNull (s := s₁) (f := f₁) (k := k) (cont := cont) (vs := vs)
          (rest := rest₀) hc))
      exact WP.steps (enter.trans (inner.trans out)) (wp_tailNullP hc pre [] rest)
  | tail a args n =>
    obtain ⟨vs₁, c', rest₀, hrun, hc⟩ := run_of_wpP_tail hb
    have inner := Steps.ctx (P := P) (host := host) pre rest (Steps.label k cont hrun)
    have out := Steps.ctx (P := P) (host := host) pre rest
      (.single (label_step_tail (s := s₁) (f := f₁) (k := k) (cont := cont) (vs := vs₁ ++ args)
        (a := a) (rest := rest₀) hc))
    exact WP.steps (enter.trans (inner.trans out)) (wp_tailP hc pre [] rest)

variable {stk : List Val} {bt : BlockType} {B : List Instr} {np nr : Nat} {cs : List Catch}

/-- **Leaving a `try_table` by an escaping result other than a throw**, for `MatchP`: a flow
leaves the label and passes the handler; a pending (null) tail call leaves the label by
`return_call_ref-label` and the handler by `return_call_ref-handler`. -/
theorem wp_try_escP {o : POut} {rest : List Admin} (har : Binaryen.arity f bt = some (np, nr))
    (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B) (MatchP (s₁, f₁, o)))
    (ho : o.Escapes) (hnt : o.NotThrow) :
    WP P host s f (vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest) (MatchP (s₁, f₁, o)) := by
  have enter := steps_try_enter (P := P) (host := host) (s := s) (cs := cs) (B := B) har hp rest
  cases o with
  | flow fl =>
    rcases run_of_wpP_flow hb with ⟨c', o, hrun, he, hm⟩ | ⟨rfl, vs, c', rest₀, hrun, hc⟩
    · have hn : ¬ fl.IsNormal := by
        cases fl <;> simp_all [POut.Escapes, Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]
      have hnt' : ∀ a, fl ≠ .throw a := by
        rintro a rfl
        exact hnt
      obtain ⟨c₁, o₁, hst₁, he₁, hm₁⟩ := label_step_abrupt (P := P) (host := host) (s₁ := s₁)
        (f₁ := f₁) (n := nr) (cont := []) he hm (.inr ⟨ho, rfl⟩)
      obtain ⟨c₂, o₂, hst₂, he₂, hm₂⟩ := handler_step_abrupt (P := P) (host := host) (s := s₁)
        (f := f₁) (n := nr) (cs := cs) he₁ hm₁ hn hnt'
      have hout : Steps P host ⟨s₁, f₁, [.handler nr cs [.label nr [] c']]⟩ ⟨s₁, f₁, c₂⟩ :=
        (Steps.handler (Relation.ReflTransGen.single hst₁)).tail hst₂
      exact wpP_of_wp (WP.steps (enter.trans ((steps_try_body hrun).trans
        (Steps.ctx (stk.drop np).reverse _ hout))) (wp_abrupt he₂ hm₂ hn _ _))
    · have hout : Steps P host
          ⟨s₁, f₁, [.handler nr cs [.label nr [] (vals vs ++ .ref .null :: c' :: rest₀)]]⟩
          ⟨s₁, f₁, vals vs ++ .ref .null :: c' :: []⟩ :=
        (Steps.handler (Relation.ReflTransGen.single (label_step_tailNull hc))).tail
          (handler_step_tailNull hc)
      exact WP.steps (enter.trans ((steps_try_body hrun).trans
        (Steps.ctx (stk.drop np).reverse rest hout))) (wp_tailNullP hc _ [] rest)
  | tail a args n =>
    obtain ⟨vs₁, c', rest₀, hrun, hc⟩ := run_of_wpP_tail hb
    have hout : Steps P host
        ⟨s₁, f₁, [.handler nr cs [.label nr [] (vals (vs₁ ++ args) ++ .ref (.func a) :: c' :: rest₀)]]⟩
        ⟨s₁, f₁, vals (vs₁ ++ args) ++ .ref (.func a) :: c' :: []⟩ :=
      (Steps.handler (Relation.ReflTransGen.single (label_step_tail hc))).tail
        (handler_step_tail hc)
    exact WP.steps (enter.trans ((steps_try_body hrun).trans
      (Steps.ctx (stk.drop np).reverse rest hout))) (wp_tailP hc _ [] rest)

end Runs

/-! ## The arity side -/

section Arity

set_option linter.unusedSectionVars false

variable {ext : ExtArity H} [ExtStable ext] {eh : Bool}
  {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × POut} {o : POut}

theorem tailWF_flow : TailWF (s, f, POut.flow fl) := fun _ _ _ h => by cases h

theorem arityE_of_arityP (h : ArityGoodP ext s f stk es (s₁, f₁, .flow fl) eh) :
    ArityGoodE ext s f stk es (s₁, f₁, fl) eh :=
  fun hS hc => ⟨(h hS hc).1, (h hS hc).2.1⟩

theorem arityP_of_arityE (h : ArityGoodE ext s f stk es (s₁, f₁, fl) eh) :
    ArityGoodP ext s f stk es (s₁, f₁, .flow fl) eh :=
  fun hS hc => ⟨(h hS hc).1, (h hS hc).2, tailWF_flow⟩

theorem POutOk.abrupt {labels : List Nat} {ret : Nat} {ob ob' : Option Nat}
    (h : POutOk eh labels ret ob o) (hn : ¬ o.IsNormal) : POutOk eh labels ret ob' o := by
  cases o with
  | flow fl => exact FlowOkE.abrupt h hn
  | tail => exact h

theorem POutOk.escape {labels : List Nat} {ret n : Nat} {ob ob' : Option Nat}
    (h : POutOk eh (n :: labels) ret ob o) (he : o.Escapes) : POutOk eh labels ret ob' o := by
  cases o with
  | flow fl => exact FlowOkE.escape h he
  | tail => exact h

/-- The continuation of a run, from the checked height it starts at. -/
theorem arityP_cont {labels : List Nat} {ret n : Nat} {out : Option Nat} {stk' : List Val}
    (hS : StoreChkE ext s.funcs) (inv1 : EvalInvE ext s f (s₁, f₁, fl))
    (h2 : chkE ext s.funcs f.module f.locals.length ret labels (some n) es = some out)
    (hn : stk'.length = n) (ihk : ArityGoodP ext s₁ f₁ stk' es r eh) :
    POutOk eh labels ret out r.2.2 ∧ EvalInvE ext s f (r.1, r.2.1, .trap) ∧ TailWF r := by
  have h2' := chk_inv inv1 h2
  rw [← hn] at h2'
  obtain ⟨hok, inv2, hw⟩ := ihk (storeChk_inv inv1 hS) h2'
  exact ⟨hok, inv1.trans inv2, hw⟩

/-- A checked body run, under `ArityGoodP`. -/
theorem arityP_body {L : List Nat} {ret n₀ nr : Nat} {stk₀ : List Val} (hS : StoreChkE ext s.funcs)
    (hb : endsAt (chkE ext s.funcs f.module f.locals.length ret L (some n₀) body) nr = true)
    (hlen : stk₀.length = n₀) (ihb : ArityGoodP ext s f stk₀ body r eh) :
    ∃ ob, POutOk eh L ret ob r.2.2 ∧ EvalInvE ext s f (r.1, r.2.1, .trap) ∧ TailWF r := by
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  exact ⟨ob, ihb hS (hlen ▸ hb')⟩

theorem arityP_argsAbort (iha : ArityGoodP ext s f stk args (s₁, f₁, o) eh) (ho : ¬ o.IsNormal) :
    ArityGoodP ext s f stk (.op i args :: es) (s₁, f₁, o) eh := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨hok, hinv, hw⟩ := iha hS ha
  exact ⟨hok.abrupt ho, hinv, hw⟩

theorem arityP_opOk (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) eh)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ihk : ArityGoodP ext s₂ f₂ stk₂ es r eh) : ArityGoodP ext s f stk (.op i args :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨ho, inv2⟩ := flat_normal (ext := ext) hflat (flatChk_of_evalFlat hflat hf)
  subst ho
  exact arityP_cont hS (inv1.trans inv2) h2 rfl ihk

theorem arityP_callOk {C : Abstract.CallRel H} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hC : OracleSoundE ext P host C eh)
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) eh) (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : ArityGoodP ext s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r eh) :
    ArityGoodP ext s f stk (.op (.call x) args :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE ext s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  exact arityP_cont hS inv2 h2
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk

variable {bt : BlockType} {np nr : Nat}

theorem arityP_blockOk (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl) eh) (hvs : fl.blockVals = some vs)
    (ihk : ArityGoodP ext s₁ f₁ (vs.take nr ++ stk.drop np) es r eh) :
    ArityGoodP ext s f stk (.block bt body :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨ob, hob, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  have hnr := blockVals_length hok hob hvs
  exact arityP_cont hS inv1 h2
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk

theorem arityP_blockEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodP ext s f (stk.take np) body (s₁, f₁, o) eh) (ho : o.Escapes) :
    ArityGoodP ext s f stk (.block bt body :: es) (s₁, f₁, o) eh := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hok, inv1, hw⟩ := arityP_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.escape ho, inv1, hw⟩

theorem arityP_loopOk (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .normal vs) eh)
    (ihk : ArityGoodP ext s₁ f₁ (vs.take nr ++ stk.drop np) es r eh) :
    ArityGoodP ext s f stk (.loop bt body :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  obtain ⟨ob, hob, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  have hnr := (length_of_ends hok hob).ge
  exact arityP_cont hS inv1 h2
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk

theorem arityP_loopBack (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .brk 0 vs) eh)
    (ihk : ArityGoodP ext s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r eh) :
    ArityGoodP ext s f stk (.loop bt body :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  obtain ⟨m, hm, hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle
  exact arityP_cont hS inv1 hc
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk

theorem arityP_loopEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodP ext s f (stk.take np) body (s₁, f₁, o) eh) (ho : o.Escapes) :
    ArityGoodP ext s f stk (.loop bt body :: es) (s₁, f₁, o) eh := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hok, inv1, hw⟩ := arityP_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.escape ho, inv1, hw⟩

theorem arityP_ifOk {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (ihc : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)) eh)
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : ArityGoodE ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) eh)
    (hvs : fl.blockVals = some vs) (ihk : ArityGoodP ext s₂ f₂ (vs.take nr ++ stk₁.drop np) es r eh) :
    ArityGoodP ext s f stk (.if_ bt c t el :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hb, h2⟩ := arity_if_pre (b := b) hS ihc har hc
  replace hb := chk_inv_endsAt inv1 hb
  replace h2 := chk_inv inv1 h2
  obtain ⟨ob, hob, hok, inv2⟩ :=
    arity_body (storeChk_inv inv1 hS) hb (take_length_of_le hp) iharm
  have hnr := blockVals_length hok hob hvs
  obtain ⟨hok', inv3, hw⟩ := arityP_cont (storeChk_inv inv1 hS) inv2 h2
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk
  exact ⟨hok', inv1.trans inv3, hw⟩

theorem arityP_ifEsc {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (ihc : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)) eh)
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : ArityGoodP ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, o) eh)
    (ho : o.Escapes) :
    ArityGoodP ext s f stk (.if_ bt c t el :: es) (s₂, f₂, o) eh := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hb, -⟩ := arity_if_pre (b := b) hS ihc har hc
  replace hb := chk_inv_endsAt inv1 hb
  obtain ⟨ob, hok, inv2, hw⟩ := arityP_body (storeChk_inv inv1 hS) hb (take_length_of_le hp) iharm
  exact ⟨hok.escape ho, inv1.trans inv2, hw⟩

theorem arityP_ifAbort {c t el : List Binaryen.BExpr}
    (ihc : ArityGoodP ext s f stk c (s₁, f₁, o) eh) (ho : ¬ o.IsNormal) :
    ArityGoodP ext s f stk (.if_ bt c t el :: es) (s₁, f₁, o) eh := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  obtain ⟨hok, inv1, hw⟩ := ihc hS hco
  exact ⟨hok.abrupt ho, inv1, hw⟩

/-- An operator stopping by a trap after its arguments, in the same store. -/
theorem arityE_opTrap (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) eh) :
    ArityGoodE ext s f stk (.op i args :: es) (s₁, f₁, .trap) eh := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨-, inv1⟩ := arity_args hS iha h1
  exact ⟨trivial, inv1⟩

end Arity

/-! ## The arity side of `try_table` and of the extended call forms -/

section ArityEH

set_option linter.unusedSectionVars false

variable {tags : List TagInst} {eh : Bool} {C : Abstract.CallRel H}
  {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × POut} {o : POut} {bt : BlockType} {cs : List Catch} {np nr : Nat}
  {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {y : TypeIdx}

theorem arityP_tryOk (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) eh)
    (hvs : fl.blockVals = some vs)
    (ihk : ArityGoodP (ehExt tags) s₁ f₁ (vs.take nr ++ stk.drop np) es r eh) :
    ArityGoodP (ehExt tags) s f stk (.tryTable bt cs body :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, h2⟩ := arity_try_pre har hc
  obtain ⟨ob, hob, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  have hnr := blockVals_length hok hob hvs
  exact arityP_cont hS inv1 h2
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk

theorem arityP_tryEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodP (ehExt tags) s f (stk.take np) body (s₁, f₁, o) eh) (ho : o.Escapes) :
    ArityGoodP (ehExt tags) s f stk (.tryTable bt cs body :: es) (s₁, f₁, o) eh := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨ob, hok, inv1, hw⟩ := arityP_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.escape ho, inv1, hw⟩

/-- On the extended call forms, the exception checker checks as the tail checker. -/
theorem flatChkE_ehExt_xcall {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} (hi : isXCall i = true) :
    flatChkE (ehExt tags) F mi nl ret labels h i = flatChkE tExt F mi nl ret labels h i := by
  cases i <;> first | rfl | simp [isXCall] at hi

/-- The pre-call facts of an indirect or reference call, exception checker. -/
theorem arity_ir_preP {top : Val} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hS : StoreChkE (ehExt tags) s.funcs)
    (iha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) eh)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op i args :: es) = some out) :
    EvalInvE (ehExt tags) s f (s₁, f₁, .normal (top :: stk₁)) ∧ ps.length ≤ stk₁.length ∧
      chkE (ehExt tags) s.funcs f.module f.locals.length ret labels
        (some (stk₁.length - ps.length + rs.length)) es = some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  rw [flatChkE_ehExt_xcall (by rcases hi with ⟨x, rfl⟩ | rfl <;> rfl)] at hf
  obtain ⟨hp, rfl⟩ := flatChk_irT hi hy hf
  simp only [List.length_cons] at hp h2
  refine ⟨inv1, by omega, ?_⟩
  have : stk₁.length + 1 - (ps.length + 1) + rs.length = stk₁.length - ps.length + rs.length := by
    omega
  rwa [this] at h2

theorem arityP_irOk {top : Val} (hC : OracleSoundTE (ehExt tags) P host C eh)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (iha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) eh)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : ArityGoodP (ehExt tags) s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r eh) :
    ArityGoodP (ehExt tags) s f stk (.op i args :: es) r eh := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_preP hS iha hi hy hc
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := hC s₁ s₂ f₁ fa fi ps rs _ fl (.callRefType fi.type)
    (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) trivial hcall
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE (ehExt tags) s f
      (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  exact arityP_cont hS inv2 h2
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega) ihk

theorem arityE_irStop {top : Val} (hC : OracleSoundTE (ehExt tags) P host C eh)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (iha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) eh)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
    ArityGoodE (ehExt tags) s f stk (.op i args :: es) (s₂, f₁, fl) eh := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_preP hS iha hi hy hc
  obtain ⟨⟨_, _, hok, hfuncs⟩, -, -⟩ := hC s₁ s₂ f₁ fa fi ps rs _ fl (.callRefType fi.type)
    (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) trivial hcall
  refine ⟨?_, inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  cases fl with
  | trap => trivial
  | throw t => exact FlowOkE.throw_any hok
  | _ => exact absurd hfl id

/-- The pre-call facts of a resolved tail call, exception checker. -/
theorem tail_preP {labels : List Nat} {ret : Nat} {out : Option Nat} {stk' : List Val}
    (hS : StoreChkE (ehExt tags) s.funcs)
    (iha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) eh)
    (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk'))) (hfi : s₁.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length))
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op i args :: es) = some out) :
    EvalInvE (ehExt tags) s f (s₁, f₁, .normal stk₁) ∧ ps.length + tailPop i ≤ stk₁.length ∧
      rs.length = ret := by
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  rw [flatChkE_ehExt_xcall (tailRes_isXCall hres)] at hf
  obtain ⟨hp, hr, -⟩ := flatChk_tailForm (tExt_tail hres hfi hty hy) hf
  exact ⟨inv1, hp, hr⟩

/-- **A resolved tail call**: the pending tail call returns the function's arity, and its callee
is well formed. -/
theorem arityP_tail (iha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) eh)
    (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length)) :
    ArityGoodP (ehExt tags) s f stk (.op i args :: es)
      (s₁, f₁, .tail fa ((stk₁.drop (tailPop i)).take ps.length).reverse rs.length) eh := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hret⟩ := tail_preP hS iha hres hfi hty hy hc
  refine ⟨hret, inv1, ?_⟩
  intro a' args' n' h
  cases h
  exact ⟨fi, ps, rs, hfi, hty,
    by simp only [List.length_reverse, List.length_take, List.length_drop]; omega, rfl⟩

end ArityEH

/-! ## The Core side -/

section Core

set_option linter.unusedSectionVars false

variable {ext : ExtArity H} [ExtStable ext] {eh : Bool} {C : Abstract.CallRel H}
  {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × POut} {o : POut} {bt : BlockType} {np nr : Nat}

theorem coreP_of_coreE (h : CoreGoodE ext P host s f stk es (s₁, f₁, fl)) :
    CoreGoodP ext P host s f stk es (s₁, f₁, .flow fl) :=
  fun hS hc => wpP_of_wp (h hS hc)

theorem coreE_of_coreP (hfl : fl ≠ .trap) (h : CoreGoodP ext P host s f stk es (s₁, f₁, .flow fl)) :
    CoreGoodE ext P host s f stk es (s₁, f₁, fl) :=
  fun hS hc => wp_of_wpP hfl (h hS hc)

theorem ne_trap_of_blockVals (hvs : fl.blockVals = some vs) : fl ≠ .trap := by
  rintro rfl
  cases hvs

theorem coreP_argsAbort (iha : CoreGoodP ext P host s f stk args (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
    CoreGoodP ext P host s f stk (.op i args :: es) (s₁, f₁, o) := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  exact wp_append_abruptP (iha hS ha) ho

theorem coreP_blockEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreGoodP ext P host s f (stk.take np) body (s₁, f₁, o)) (ho : o.Escapes) :
    CoreGoodP ext P host s f stk (.block bt body :: es) (s₁, f₁, o) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE ext s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_block]
  exact wp_label_escP (steps_enter (P := P) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_block har) _) (ihb hS hbc) ho

theorem coreP_loopEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreGoodP ext P host s f (stk.take np) body (s₁, f₁, o)) (ho : o.Escapes) :
    CoreGoodP ext P host s f stk (.loop bt body :: es) (s₁, f₁, o) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE ext s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_loop]
  exact wp_label_escP (steps_enter (P := P) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) _) (ihb hS hbc) ho

theorem coreP_ifEsc {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)) eh)
    (ihc : CoreGoodE ext P host s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : CoreGoodP ext P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, o))
    (ho : o.Escapes) :
    CoreGoodP ext P host s f stk (.if_ bt c t el :: es) (s₂, f₂, o) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hbarm, -⟩ := arity_if_pre (b := b) hS hcond har hc
  replace hbarm := chk_inv_endsAt inv1 hbarm
  obtain ⟨ob, hb', -⟩ := endsAt_eq hbarm
  have hbc : chkE ext s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [take_length_of_le hp]; exact hb'
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  have hwb := wp_label_escP (steps_enter (P := P) (host := host) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (step_block har)
    (expression (Binaryen.BExpr.lowerList es))) (iharm (storeChk_inv inv1 hS) hbc) ho
  rw [code_if]
  exact wp_append_normal (ihc hS hco) (wp_if_arm hb hwb)

theorem coreP_ifAbort {c t el : List Binaryen.BExpr}
    (ihc : CoreGoodP ext P host s f stk c (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
    CoreGoodP ext P host s f stk (.if_ bt c t el :: es) (s₁, f₁, o) := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if]
  exact wp_append_abruptP (ihc hS hco) ho

/-- **An oracle call under any postcondition**, any checker and exception capability. -/
theorem coreOQ_callOkE {M : Nat → Store H × Frame × Binaryen.Flow → Post H}
    {r' : Store H × Frame × Binaryen.Flow} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hC : OracleSoundE ext P host C eh)
    (aha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) eh)
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodQ ext P host M s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r') :
    CoreGoodQ ext P host M s f stk (.op (.call x) args :: es) r' := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, hret, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE ext s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE ext s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have st := steps_oracle_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi (hret vs hvs)
  rw [code_op]
  refine wp_append_normal (iha hS ha) (WP.steps st ?_)
  simpa [vals, List.reverse_append, List.append_assoc] using hk

/-- An indirect or reference call that traps before any call (unresolved callee, null
reference), any checker. -/
theorem coreE_irTrap {top : Val}
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩ ⟨s₁, f₁, [.trap]⟩) :
    CoreGoodE ext P host s f stk (.op i args :: es) (s₁, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine ⟨s₁, f₁, [.trap], .trap, st₁.trans ?_, rfl, rfl, rfl, trivial⟩
  simpa using steps_trap (P := P) (host := host) s₁ f₁ stk₁.reverse E

/-- **A resolved tail call ends the body in Core's pending tail call**: `return_call`,
`return_call_indirect` and `return_call_ref` run to `REF.FUNC_ADDR fa; RETURN_CALL_REF`, with the
arguments on top; nothing is answered here. -/
theorem coreP_tail {fa n m : Nat}
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i)))) :
    CoreGoodP ext P host s f stk (.op i args :: es)
      (s₁, f₁, .tail fa ((stk₁.drop (tailPop i)).take n).reverse m) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨c, hcr, -, hpre⟩ := tailRes_steps (P := P) (host := host) hres
  let E := expression (Binaryen.BExpr.lowerList es)
  have st := Steps.ctx (P := P) (host := host) (stk₁.drop (tailPop i)).reverse E hpre
  have e : vals stk₁.reverse ++ .plain i :: E = vals (stk₁.drop (tailPop i)).reverse ++
      (vals (stk₁.take (tailPop i)).reverse ++ [.plain i]) ++ E := by
    rw [rev_take_drop stk₁ (tailPop i)]; simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine WP.steps st ?_
  have hw := wp_tailP (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (a := fa) (n := m)
    (vs₁ := ((stk₁.drop (tailPop i)).drop n).reverse)
    (args := ((stk₁.drop (tailPop i)).take n).reverse) hcr [] [] E
  rw [← rev_take_drop] at hw
  simpa using hw

/-- **An unresolved tail call traps**: at once, or on null as Core's pending null tail call. -/
theorem coreP_tailRes (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hres : TailRes s₁ f₁ i stk₁ none) :
    CoreGoodP ext P host s f stk (.op i args :: es) (s₁, f₁, .flow .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  cases hres with
  | @indirectTrap x y ad j stk hres' =>
    have e : vals (Val.num ⟨.int ad.intType, j⟩ :: stk).reverse ++
        .plain (.returnCallIndirect x y) :: E =
        vals stk.reverse ++ [aconst ad j, .plain (.returnCallIndirect x y)] ++ E := by
      rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]
      simp
    rw [e]
    rcases Silmaril.Wasm.Abstract.CallRes.steps_returnCallIndirect_trap (P := P) (host := host)
      hres' with st | st
    · have st₁ := Steps.ctx (P := P) (host := host) stk.reverse E st
      refine wpP_of_wp ⟨s₁, f₁, [.trap], .trap, st₁.trans ?_, rfl, rfl, rfl, trivial⟩
      simpa using steps_trap (P := P) (host := host) s₁ f₁ stk.reverse E
    · have st₁ := Steps.ctx (P := P) (host := host) stk.reverse E st
      refine WP.steps st₁ ?_
      have hw := wp_tailNullP (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (vs := stk.reverse)
        (c := .plain (.returnCallRef y)) trivial [] E []
      simpa [vals] using hw
  | @refNull y stk =>
    have hw := wp_tailNullP (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (vs := stk.reverse)
      (c := .plain (.returnCallRef y)) trivial [] E []
    simpa [vals, Val.toAdmin] using hw

end Core

section CoreEH

set_option linter.unusedSectionVars false

variable {tags : List TagInst} {eh : Bool} {C : Abstract.CallRel H}
  {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {o : POut} {bt : BlockType} {cs : List Catch} {np nr : Nat}
  {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {y : TypeIdx}

theorem coreP_tryEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreGoodP (ehExt tags) P host s f (stk.take np) body (s₁, f₁, o)) (ho : o.Escapes)
    (hnt : o.NotThrow) :
    CoreGoodP (ehExt tags) P host s f stk (.tryTable bt cs body :: es) (s₁, f₁, o) := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_tryTable]
  exact wp_try_escP har hp (ihb hS hbc) ho hnt

/-- An indirect or reference call: the callee answered, the continuation runs. -/
theorem coreP_irOk {top : Val} {M : Nat → Store H × Frame × Binaryen.Flow → Post H}
    {r' : Store H × Frame × Binaryen.Flow} (hC : OracleSoundTE (ehExt tags) P host C eh)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) eh)
    (iha : CoreGoodE (ehExt tags) P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodQ (ehExt tags) P host M s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r') :
    CoreGoodQ (ehExt tags) P host M s f stk (.op i args :: es) r' := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_preP hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, hret, -⟩ := hC s₁ s₂ f₁ fa fi ps rs _ fl (.plain (.callRef y))
    (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) trivial hcall
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE (ehExt tags) s f
      (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE (ehExt tags) s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have st₂ := steps_oracle_irT (rest := E) (hret vs hvs)
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine WP.steps (st₁.trans st₂) ?_
  simpa [vals, List.reverse_append, List.append_assoc] using hk

/-- An indirect or reference call whose callee traps or throws. -/
theorem coreE_irStop {top : Val} (hC : OracleSoundTE (ehExt tags) P host C eh)
    (hT : OracleThrowsE (ehExt tags) P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) eh)
    (iha : CoreGoodE (ehExt tags) P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
    CoreGoodE (ehExt tags) P host s f stk (.op i args :: es) (s₂, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_preP hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  cases fl with
  | trap =>
    obtain ⟨-, -, htr⟩ := hC s₁ s₂ f₁ fa fi ps rs _ .trap (.plain (.callRef y))
      (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) trivial hcall
    have st₂ := steps_oracle_irT (rest := E) (htr rfl)
    refine ⟨s₂, f₁, [.trap], .trap, (st₁.trans st₂).trans ?_, rfl, rfl, rfl, trivial⟩
    simpa using steps_trap (P := P) (host := host) s₂ f₁ (stk₁.drop ps.length).reverse E
  | throw t =>
    have hth := hT s₁ s₂ f₁ fa fi ps rs _ t (.plain (.callRef y)) (storeChk_inv inv1 hS) hfi hty
      (take_rev_length hp) trivial hcall
    have st₂ := steps_oracle_irT (rest := E) hth
    exact WP.steps (st₁.trans st₂) (wp_throwing ⟨rfl, rfl, rfl⟩)
  | _ => exact absurd hfl id

end CoreEH

/-! ## The continuation cases, for `CoreGoodP` -/

section CoreCont

set_option linter.unusedSectionVars false

variable {tags : List TagInst} {ext : ExtArity H} [ExtStable ext] {eh : Bool}
  {C : Abstract.CallRel H} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × POut} {bt : BlockType} {cs : List Catch} {np nr : Nat}

theorem coreP_opOk (hargs : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) eh)
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁)) (hi : ∀ x, i ≠ .call x)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ihk : CoreGoodP ext P host s₂ f₂ stk₂ es r) :
    CoreGoodP ext P host s f stk (.op i args :: es) r :=
  core_opOk (M := fun _ _ => MatchP r) (r := (r.1, r.2.1, .trap)) hargs iha hi hflat ihk

theorem coreP_callOk {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hC : OracleSoundE ext P host C eh)
    (aha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) eh)
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodP ext P host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodP ext P host s f stk (.op (.call x) args :: es) r :=
  coreOQ_callOkE (M := fun _ _ => MatchP r) (r' := (r.1, r.2.1, .trap)) hC aha iha hfi hty hcall hvs ihk

theorem coreP_blockOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl) eh)
    (ihb : CoreGoodE ext P host s f (stk.take np) body (s₁, f₁, fl)) (hvs : fl.blockVals = some vs)
    (ihk : CoreGoodP ext P host s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    CoreGoodP ext P host s f stk (.block bt body :: es) r :=
  core_blockOk (M := fun _ _ => MatchP r) (r := (r.1, r.2.1, .trap)) har hbody ihb hvs ihk

theorem coreP_loopOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .normal vs) eh)
    (ihb : CoreGoodE ext P host s f (stk.take np) body (s₁, f₁, .normal vs))
    (ihk : CoreGoodP ext P host s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    CoreGoodP ext P host s f stk (.loop bt body :: es) r :=
  core_loopOk (M := fun _ _ => MatchP r) (r := (r.1, r.2.1, .trap)) har hbody ihb ihk

theorem coreP_loopBack (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .brk 0 vs) eh)
    (ihb : CoreGoodE ext P host s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ihk : CoreGoodP ext P host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
    CoreGoodP ext P host s f stk (.loop bt body :: es) r :=
  core_loopBack (M := fun _ _ => MatchP r) (r := (r.1, r.2.1, .trap)) har hbody ihb ihk

theorem coreP_ifOk {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)) eh)
    (ihc : CoreGoodE ext P host s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : ArityGoodE ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) eh)
    (iharm : CoreGoodE ext P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hvs : fl.blockVals = some vs)
    (ihk : CoreGoodP ext P host s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
    CoreGoodP ext P host s f stk (.if_ bt c t el :: es) r :=
  core_ifOk (M := fun _ _ => MatchP r) (r := (r.1, r.2.1, .trap)) hcond ihc hb har harm iharm hvs ihk

theorem coreP_tryOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) eh)
    (ihb : CoreGoodE (ehExt tags) P host s f (stk.take np) body (s₁, f₁, fl))
    (hvs : fl.blockVals = some vs)
    (ihk : CoreGoodP (ehExt tags) P host s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    CoreGoodP (ehExt tags) P host s f stk (.tryTable bt cs body :: es) r :=
  core_tryOk (M := fun _ _ => MatchP r) (r := (r.1, r.2.1, .trap)) har hbody ihb hvs ihk

theorem coreP_irOkP {top : Val} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    {y : TypeIdx} (hC : OracleSoundTE (ehExt tags) P host C eh)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) eh)
    (iha : CoreGoodE (ehExt tags) P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodP (ehExt tags) P host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodP (ehExt tags) P host s f stk (.op i args :: es) r :=
  coreP_irOk (M := fun _ _ => MatchP r) (r' := (r.1, r.2.1, .trap)) hC hi aha iha hpre hfi hty hy hcall hvs ihk

end CoreCont

/-! ## The simulation -/

/-- **Forward simulation with pending tail calls**: with the exception checker `ehExt tags` and
exceptions on, every `EvalOXP C` run of checked code, all call forms included, is a Core 3.0 run
under `MatchP`, with the arity invariants and the tag invariants. A resolved tail call ends the
run in Core's pending tail call, which passes every label and handler; an unresolved one traps
(on null, as Core's pending null tail call). The oracle is sound in every `call_ref` form
(`OracleSoundTE`), its callees may throw (`OracleThrowsE`) and it keeps the tag invariants. -/
theorem evalOXP_goodP {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : OracleSoundTE (ehExt tags) P host C true) (hT : OracleThrowsE (ehExt tags) P host C)
    (hG : OracleTagsE tags C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP C s f stk es r) :
    TagsOk tags s →
      TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
        CoreGoodP (ehExt tags) P host s f stk es r := by
  have hE := hC.soundE
  induction h with
  | nil => exact fun hts => ⟨hts, arityP_of_arityE arity_nil, coreP_of_coreE core_nil⟩
  | argsAbort _ ho iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_argsAbort aa ho, coreP_argsAbort ca ho⟩
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    obtain ⟨tk, ak, ck⟩ := ihk (hG _ _ _ _ _ hcall ta)
    exact ⟨tk, arityP_callOk hE (arityE_of_arityP aa) hfi hty hcall hvs ak,
      coreP_callOk hE (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca) hfi hty hcall hvs ck⟩
  | callTrap _ hfi hty hcall iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨hG _ _ _ _ _ hcall ta,
      arityP_of_arityE (arityO_callTrap hE (arityE_of_arityP aa) hfi hty hcall),
      coreP_of_coreE (coreO_callTrap hE (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca) hfi hty
        hcall)⟩
  | callThrow _ hfi hty hcall iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨hG _ _ _ _ _ hcall ta,
      arityP_of_arityE (arityO_callThrow hE (arityE_of_arityP aa) hfi hty hcall),
      coreP_of_coreE (coreO_callThrowE hT (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca) hfi hty
        hcall)⟩
  | opOk hi _ hflat _ iha ihk =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    obtain ⟨tk, ak, ck⟩ := ihk (ta.evalFlat hflat)
    exact ⟨tk, arityP_opOk (arityE_of_arityP aa) hflat ak,
      coreP_opOk (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca) hi hflat ck⟩
  | opStop _ _ hflat hfl iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta.evalFlat hflat, arityP_of_arityE (arity_opStop (arityE_of_arityP aa) hflat hfl),
      coreP_of_coreE (core_opStop (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca) hflat hfl)⟩
  | blockOk har _ hvs _ ihb ihk =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    obtain ⟨tk, ak, ck⟩ := ihk tb
    exact ⟨tk, arityP_blockOk har (arityE_of_arityP ab) hvs ak,
      coreP_blockOk har (arityE_of_arityP ab) (coreE_of_coreP (ne_trap_of_blockVals hvs) cb) hvs ck⟩
  | blockBrk har _ ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_of_arityE (arity_blockBrk har (arityE_of_arityP ab)),
      coreP_of_coreE (core_blockAbrupt har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb)
        (.inl ⟨_, _, rfl, rfl⟩))⟩
  | blockEsc har _ ho ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_blockEsc har ab ho, coreP_blockEsc har cb ho⟩
  | loopOk har _ _ ihb ihk =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    obtain ⟨tk, ak, ck⟩ := ihk tb
    exact ⟨tk, arityP_loopOk har (arityE_of_arityP ab) ak,
      coreP_loopOk har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb) ck⟩
  | loopBack har _ _ ihb ihk =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    obtain ⟨tk, ak, ck⟩ := ihk tb
    exact ⟨tk, arityP_loopBack har (arityE_of_arityP ab) ak,
      coreP_loopBack har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb) ck⟩
  | loopBrk har _ ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_of_arityE (arity_loopBrk har (arityE_of_arityP ab)),
      coreP_of_coreE (core_loopAbrupt har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb)
        (.inl ⟨_, _, rfl, rfl⟩))⟩
  | loopEsc har _ ho ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_loopEsc har ab ho, coreP_loopEsc har cb ho⟩
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    intro hts
    obtain ⟨tc, ac, cc⟩ := ihc hts
    obtain ⟨tm, am, cm⟩ := iharm tc
    obtain ⟨tk, ak, ck⟩ := ihk tm
    exact ⟨tk, arityP_ifOk (arityE_of_arityP ac) har (arityE_of_arityP am) hvs ak,
      coreP_ifOk (arityE_of_arityP ac) (coreE_of_coreP (by nofun) cc) hb har (arityE_of_arityP am)
        (coreE_of_coreP (ne_trap_of_blockVals hvs) cm) hvs ck⟩
  | ifBrk _ hb har _ ihc iharm =>
    intro hts
    obtain ⟨tc, ac, cc⟩ := ihc hts
    obtain ⟨tm, am, cm⟩ := iharm tc
    exact ⟨tm, arityP_of_arityE (arity_ifBrk (arityE_of_arityP ac) har (arityE_of_arityP am)),
      coreP_of_coreE (core_ifAbrupt (arityE_of_arityP ac) (coreE_of_coreP (by nofun) cc) hb har
        (arityE_of_arityP am) (coreE_of_coreP (by nofun) cm) (.inl ⟨_, _, rfl, rfl⟩))⟩
  | ifEsc _ hb har _ ho ihc iharm =>
    intro hts
    obtain ⟨tc, ac, cc⟩ := ihc hts
    obtain ⟨tm, am, cm⟩ := iharm tc
    exact ⟨tm, arityP_ifEsc (arityE_of_arityP ac) har am ho,
      coreP_ifEsc (arityE_of_arityP ac) (coreE_of_coreP (by nofun) cc) hb har cm ho⟩
  | ifAbort _ ho ihc =>
    intro hts
    obtain ⟨tc, ac, cc⟩ := ihc hts
    exact ⟨tc, arityP_ifAbort ac ho, coreP_ifAbort cc ho⟩
  | callIndOk _ hres hfi hty hy hcall hvs _ iha ihk =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    obtain ⟨tk, ak, ck⟩ := ihk (hG _ _ _ _ _ hcall ta)
    exact ⟨tk, arityP_irOk hC (.inl ⟨_, rfl⟩) (arityE_of_arityP aa) hfi hty hy hcall hvs ak,
      coreP_irOkP hC (.inl ⟨_, rfl⟩) (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca)
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy hcall hvs ck⟩
  | callIndRes _ hres iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_of_arityE (arityE_opTrap (arityE_of_arityP aa)),
      coreP_of_coreE (coreE_irTrap (coreE_of_coreP (by nofun) ca)
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_trap hres))⟩
  | callIndStop _ hres hfi hty hy hcall hfl iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨hG _ _ _ _ _ hcall ta,
      arityP_of_arityE (arityE_irStop hC (.inl ⟨_, rfl⟩) (arityE_of_arityP aa) hfi hty hy hcall
        hfl),
      coreP_of_coreE (coreE_irStop hC hT (.inl ⟨_, rfl⟩) (arityE_of_arityP aa)
        (coreE_of_coreP (by nofun) ca) (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
        hfi hty hy hcall hfl)⟩
  | callRefOk _ hfi hty hy hcall hvs _ iha ihk =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    obtain ⟨tk, ak, ck⟩ := ihk (hG _ _ _ _ _ hcall ta)
    exact ⟨tk, arityP_irOk hC (.inr rfl) (arityE_of_arityP aa) hfi hty hy hcall hvs ak,
      coreP_irOkP hC (.inr rfl) (arityE_of_arityP aa) (coreE_of_coreP (by nofun) ca) .refl hfi hty hy
        hcall hvs ck⟩
  | callRefNull _ iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_of_arityE (arityE_opTrap (arityE_of_arityP aa)),
      coreP_of_coreE (coreE_irTrap (coreE_of_coreP (by nofun) ca)
        (.single (Step.callRefNull (c := .plain (.callRef _)) trivial)))⟩
  | callRefStop _ hfi hty hy hcall hfl iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨hG _ _ _ _ _ hcall ta,
      arityP_of_arityE (arityE_irStop hC (.inr rfl) (arityE_of_arityP aa) hfi hty hy hcall hfl),
      coreP_of_coreE (coreE_irStop hC hT (.inr rfl) (arityE_of_arityP aa)
        (coreE_of_coreP (by nofun) ca) .refl hfi hty hy hcall hfl)⟩
  | tail _ hres hfi hty hy iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_tail (arityE_of_arityP aa) hres hfi hty hy,
      coreP_tail (coreE_of_coreP (by nofun) ca) hres⟩
  | tailRes _ hres iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_of_arityE (arityE_opTrap (arityE_of_arityP aa)),
      coreP_tailRes (coreE_of_coreP (by nofun) ca) hres⟩
  | throw _ ht he hn iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨tagsOk_throw ta ht he (by simp only [List.length_reverse, List.length_take]; omega),
      arityP_of_arityE (arityE_opStop (arityE_of_arityP aa) rfl (.inr ⟨_, rfl⟩)),
      coreP_of_coreE (core_throw (coreE_of_coreP (by nofun) ca) ht he hn)⟩
  | throwRefNull _ iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_of_arityE (arityE_opStop (arityE_of_arityP aa) rfl (.inl rfl)),
      coreP_of_coreE (core_throwRefNull (coreE_of_coreP (by nofun) ca))⟩
  | throwRefExn _ iha =>
    intro hts
    obtain ⟨ta, aa, ca⟩ := iha hts
    exact ⟨ta, arityP_of_arityE (arityE_opStop (arityE_of_arityP aa) rfl (.inr ⟨_, rfl⟩)),
      coreP_of_coreE (core_throwRefExn (coreE_of_coreP (by nofun) ca))⟩
  | tryOk har _ hvs _ ihb ihk =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    obtain ⟨tk, ak, ck⟩ := ihk tb
    exact ⟨tk, arityP_tryOk har (arityE_of_arityP ab) hvs ak,
      coreP_tryOk har (arityE_of_arityP ab) (coreE_of_coreP (ne_trap_of_blockVals hvs) cb) hvs ck⟩
  | tryBrk har _ ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_of_arityE (arity_tryBrk har (arityE_of_arityP ab)),
      coreP_of_coreE (core_tryAbrupt har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb)
        (.inl ⟨_, _, rfl, rfl⟩) (fun _ h => by cases h))⟩
  | tryEsc har _ ho hnt ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_tryEsc har ab ho, coreP_tryEsc har cb ho hnt⟩
  | tryCatch har _ hc ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_of_arityE (arity_tryCatch tb har (arityE_of_arityP ab) hc),
      coreP_of_coreE (core_tryCatch har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb) hc)⟩
  | tryRethrow har _ hc ihb =>
    intro hts
    obtain ⟨tb, ab, cb⟩ := ihb hts
    exact ⟨tb, arityP_of_arityE (arity_tryRethrow har (arityE_of_arityP ab)),
      coreP_of_coreE (core_tryRethrow har (arityE_of_arityP ab) (coreE_of_coreP (by nofun) cb) hc)⟩

end Silmaril.Wasm.Interp
