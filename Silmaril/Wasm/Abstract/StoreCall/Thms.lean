module

public import Silmaril.Wasm.Abstract.StoreCall.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Wasm.Abstract.Oracle.Thms
public import Silmaril.Wasm.Abstract.Decomp.Thms
public import Silmaril.Wasm.Interp.Diverge.Thms
import Silmaril.Proofs.Wasm.Abstract.StoreCall.Expose
import Silmaril.Proofs.Wasm.Abstract.StoreCall.Answer
import Silmaril.Proofs.Wasm.Abstract.StoreCall.Descent
import Silmaril.Proofs.Wasm.Abstract.StoreCall.LocalDiv

/-!
# Store bodies with internal calls as events: theorems (F4, exposure)

For the exposed abstract body `denListE = denListC callEv`
(`Silmaril.Wasm.Abstract.StoreCall.Defs`), whose internal calls are visible
events of `CallSig H`:

* **Exposure is sound for `EvalO`.** `evalO_path`: every derivation of the
  oracle semantics `Recursion.EvalO C` is a path of the exposed abstract body
  whose call events are all answered as `C` allows (`Answered C`), ending as
  the derivation does (`endR`; a trap is the trap effect).
* **Recursion closed.** `eval_path`: every derivation of the native
  interpreter's recursive big-step relation `Binaryen.Eval` (calls run their
  callees) is such a path with the answers of the closure `closedCall`
  (`Recursion.evalO_closed_iff`).
* **Core 3.0.** `core_call_path`: on typed, native, arity-checked stores at
  every profile, every Core 3.0 run of an invocation to a result with final
  store `s'`, internal calls and recursion included, is an answered path of
  the exposed abstract body of the callee's code, with the answers of
  `closedCall`, which is Core 3.0's call semantics (`Oracle.closedCall_core_iff`).

* **Exposure is exact.** `path_evalO`: conversely, every finished path of the
  exposed body whose call events are answered by `C` is an `EvalO C`
  derivation. So `evalO_iff` (value outcomes, final store and frame included)
  and `evalO_trap_iff` (traps); with `closedCall`, `eval_iff`/`eval_trap_iff`
  for the recursive semantics.

* **Divergence through calls, on the existing divergence.** The native descent
  relation `Decomp.Reach`/`BodyReach` (a problem reaches an internal call after
  a terminating prefix: the descents of `Interp.EvalDiv` and of
  `Shape.closeDL`) is exactly a *pending call event* of the exposed body after
  `closedCall`-answered events: `reach_iff_pend`, `bodyReach_iff_exposed`,
  `bodyPath_iff_exposed`. So divergence of a call (`Interp.FunDiv`, the
  coinductive `EvalDiv` of #319/#322) is exactly a finite chain of exposed
  descents to a locally diverging call, or an infinite chain of exposed
  descents (`funDiv_iff_exposed`, with `funDiv_of_chain`), and on typed,
  native, arity-checked stores at every profile so is Core 3.0 divergence
  (`core_diverges_iff_exposed`).

* **Local divergence, exposed.** `Interp.LocalDiv` (the function diverges while
  every call it makes returns, including infinitely many returning calls) is
  read on the exposed body: `localDiv_reach_call` (every call reached under
  local divergence returns in `closedCall`), `exposed_of_localDiv` (local
  divergence is silent divergence after `closedCall`-answered events, or an
  infinite `closedCall`-answered run) and, conversely, `localDiv_of_exposedInf`
  (an infinite answered run is local divergence). At the level of calls:
  `exposed_of_wasmLocalDiv`, `wasmLocalDiv_of_exposedInf`, and for Core 3.0
  `core_diverges_exposed` (divergence ⇒ finite exposed descents to a call whose
  exposed body diverges silently or runs forever answered, or an infinite chain)
  and `core_diverges_of_exposed` (the productive and chain cases ⇒ divergence).

* **Silent divergence, on typed stores.** On typed (`InvokeOk`), native,
  arity-checked stores, *silent* exposed divergence is not a stuck
  configuration: `core_diverges_iff_exposed_local` is the exact statement,
  Core 3.0 divergence ⇔ finitely many exposed descents to a call whose exposed
  body diverges silently (after answered events) **or** runs forever answered
  (infinitely many returning calls), or an infinite exposed chain. The silent
  case is proved against typed progress of the native interpreter
  (`Interp.funDiv_iff_invokeRun_none`): a terminating invocation evaluates every
  descendant call's body (`reach_eval_call`), and an evaluating body has no
  silent exposed divergence (answers are functional, so its finished answered
  paths are unique).

**Not yet.** At the level of arbitrary (untyped) problems, silent exposed
divergence also covers stuck configurations, so it is not `LocalDiv` there.
Also not covered: `try_table` (F5), imports (host events), indirect calls and
tail calls (only direct `call` is exposed).
-/

public section

namespace Silmaril.Wasm.Abstract.StoreCall

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody

variable {H : Type}

/-- **Exposure.** Every `EvalO C` derivation is a path of the exposed abstract
body with every call event answered by `C`. -/
theorem evalO_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalO C s f stk es r) :
    ∃ cs, Answered C cs ∧
      Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (endR r) :=
  Silmaril.Proofs.Wasm.Abstract.StoreCall.evalO_path h

/-- **Recursion.** Every derivation of the recursive native semantics is a path
of the exposed abstract body with every call answered by the closure. -/
theorem eval_path {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) :
    ∃ cs, Answered closedCall cs ∧
      Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (endR r) :=
  evalO_path (evalO_closed_iff.2 h)

/-- **Core 3.0, with calls and recursion.** Every Core run of an invocation to a
result is an answered path of the exposed abstract body of the callee, with the
answers of `closedCall` (Core's call semantics). -/
theorem core_call_path {s : Store H} {a : Nat} {us : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a us) (P : Numerics.Profile) (r : Result) (s' : Store H)
    (h : ∃ c : Config H, Steps P closedHost (invoke s a us) c ∧ c.code = r.toAdmin ∧
      c.store = s') :
    ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame)
      (bfl fl : Flow) (cs : List (Call (CallSig H))),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      Answered closedCall cs ∧
      Path (((denListE (liftInstrs fn.body) (Frame.forCall fi.module us fn.locals) [] :
        M (CallSig H) H Res).run ⟨s⟩).run) cs (endR (s', f₂, bfl)) ∧
      exitFlow rs.length bfl = some fl ∧ flowBeh fl = some r.toBehaviour := by
  obtain ⟨fi, ps, rs, bfl, fl, hfi, hty, hc, hex, hb⟩ :=
    (closedCall_core_iff hs hF hS hok P r s').2 h
  rw [closedCall_fixpoint] at hc
  obtain ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hev⟩ := hc
  rw [hfi] at hfi'
  obtain rfl := Option.some.inj hfi'
  rw [hty] at hty'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty')
  obtain ⟨cs, hA, hp⟩ := evalO_path hev
  exact ⟨fi, fn, ps, rs, f₂, bfl, fl, cs, hfi, hcode, hty, hA, hp, hex, hb⟩

/-- **Conversely**, every finished path of the exposed body whose call events
are answered by `C` is an `EvalO C` derivation. -/
theorem path_evalO {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {cs : List (Call (CallSig H))}
    {e : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs e) (he : e ≠ .div) :
    ∃ r, EvalO C s f stk es r ∧ endR r = e :=
  Silmaril.Proofs.Wasm.Abstract.StoreCall.list_ans es s f stk cs e hA h he

/-- **Exposure is exact (values).** An `EvalO C` outcome that is not a trap is
exactly a finished answered path of the exposed body with that store, frame
and flow. -/
theorem evalO_iff {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    EvalO C s f stk es (s', f', fl) ↔
      ∃ cs, Answered C cs ∧ Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs
        (.val (.ok (⟨(f', fl)⟩, ⟨s'⟩))) := by
  have hend : endR (s', f', fl) = .val (.ok (⟨(f', fl)⟩, ⟨s'⟩)) := by
    cases fl <;> first | exact absurd rfl hfl | rfl
  constructor
  · intro h
    obtain ⟨cs, hA, hp⟩ := evalO_path h
    exact ⟨cs, hA, hend ▸ hp⟩
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, f₁, fl₁⟩, hev, he⟩ := path_evalO hA hp (by simp)
    obtain ⟨-, h1, h2⟩ := Silmaril.Proofs.Wasm.Abstract.StoreCall.endR_ok_inv he
    simp only [ULift.up.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    subst h2
    exact hev

/-- **Exposure is exact (traps).** `EvalO C` traps exactly when the exposed body
has a finished answered path to the trap. -/
theorem evalO_trap_iff {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} :
    (∃ s' f', EvalO C s f stk es (s', f', .trap)) ↔
      ∃ cs, Answered C cs ∧ Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs
        (.val (.error ⟨⟩)) := by
  constructor
  · rintro ⟨s', f', h⟩
    exact evalO_path h
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, f₁, fl₁⟩, hev, he⟩ := path_evalO hA hp (by simp)
    obtain rfl := Silmaril.Proofs.Wasm.Abstract.StoreCall.endR_err_inv he
    exact ⟨s₁, f₁, hev⟩

/-- **Recursion, exactly.** Value outcomes of the recursive native semantics are
exactly the finished paths of the exposed body answered by `closedCall`. -/
theorem eval_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    Eval s f stk es (s', f', fl) ↔
      ∃ cs, Answered closedCall cs ∧
        Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs
          (.val (.ok (⟨(f', fl)⟩, ⟨s'⟩))) :=
  evalO_closed_iff.symm.trans (evalO_iff hfl)

/-- Traps of the recursive native semantics, exactly. -/
theorem eval_trap_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    (∃ s' f', Eval s f stk es (s', f', .trap)) ↔
      ∃ cs, Answered closedCall cs ∧
        Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (.val (.error ⟨⟩)) := by
  rw [← evalO_trap_iff]
  simp only [evalO_closed_iff]

/-! ## Divergence through calls -/

/-- **Descents are pending calls.** A problem reaches an internal call after a
terminating prefix exactly when the exposed body makes that call event after
call events answered by `closedCall`. -/
theorem reach_iff_pend {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} :
    Reach s f stk es y ↔ ∃ cs, Answered closedCall cs ∧
      Pend (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (callOp y) :=
  ⟨Silmaril.Proofs.Wasm.Abstract.StoreCall.reach_pend,
    fun ⟨cs, hA, hp⟩ => Silmaril.Proofs.Wasm.Abstract.StoreCall.list_pend es s f stk cs _ hA hp⟩

/-- Native descents of calls are exposed descents. -/
theorem bodyReach_iff_exposed {x y : (wasmOShape H).self.Op} : BodyReach x y ↔ ExposedReach x y := by
  constructor
  · rintro ⟨fi, fn, hfi, hcode, hr⟩
    exact ⟨fi, fn, hfi, hcode, reach_iff_pend.1 hr⟩
  · rintro ⟨fi, fn, hfi, hcode, hp⟩
    exact ⟨fi, fn, hfi, hcode, reach_iff_pend.2 hp⟩

theorem bodyPath_iff_exposed {x z : (wasmOShape H).self.Op} : BodyPath x z ↔ ExposedPath x z := by
  constructor
  · intro h
    induction h with
    | refl x => exact .refl x
    | step h _ ih => exact .step (bodyReach_iff_exposed.1 h) ih
  · intro h
    induction h with
    | refl x => exact .refl x
    | step h _ ih => exact .step (bodyReach_iff_exposed.2 h) ih

/-- **Divergence of a call, through call events.** A call diverges (the
coinductive `Interp.EvalDiv` of its body) exactly when a finite chain of
exposed descents reaches a locally diverging call, or an infinite chain of
exposed descents starts at it. Any store. -/
theorem funDiv_iff_exposed (x : (wasmOShape H).self.Op) :
    Interp.FunDiv x.2.2 x.1 x.2.1 ↔
      (∃ z, ExposedPath x z ∧ wasmLocalDiv z) ∨
        ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, ExposedReach (g n) (g (n + 1)) := by
  constructor
  · intro h
    rcases funDiv_path_or_chain h with ⟨z, hp, hz⟩ | ⟨g, hg0, hg⟩
    · exact .inl ⟨z, bodyPath_iff_exposed.1 hp, hz⟩
    · exact .inr ⟨g, hg0, fun n => bodyReach_iff_exposed.1 (hg n)⟩
  · rintro (⟨z, hp, hz⟩ | ⟨g, rfl, hg⟩)
    · exact funDiv_of_path (bodyPath_iff_exposed.2 hp) hz
    · exact Silmaril.Proofs.Wasm.Abstract.StoreCall.funDiv_of_chain
        fun n => bodyReach_iff_exposed.2 (hg n)

/-- **Core 3.0 divergence, through call events.** On a typed invocation of a
native, arity-checked store, at every profile: the invocation diverges exactly
when a finite chain of exposed descents reaches a locally diverging call, or an
infinite chain of exposed descents starts at it. -/
theorem core_diverges_iff_exposed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Diverges P closedHost (invoke s a vs) ↔
      (∃ z, ExposedPath ⟨a, (vs, s)⟩ z ∧ wasmLocalDiv z) ∨
        ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
          ∀ n, ExposedReach (g n) (g (n + 1)) :=
  (Silmaril.Wasm.Interp.core_diverges_iff_funDiv hs hF hS hok P).trans
    (funDiv_iff_exposed ⟨a, (vs, s)⟩)

/-! ## Local divergence -/

/-- Under local divergence, every reached internal call returns (or traps or
throws) in `closedCall`. -/
theorem localDiv_reach_call {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (hR : Reach s f stk es y) (hL : Interp.LocalDiv s f stk es) :
    ∃ out, closedCall y.2.2 y.1 y.2.1 out :=
  Silmaril.Proofs.Wasm.Abstract.StoreCall.localDiv_reach_call hR hL

/-- **Local divergence on the exposed body.** -/
theorem exposed_of_localDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (hL : Interp.LocalDiv s f stk es) :
    (∃ cs, Answered closedCall cs ∧
        Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs .div) ∨
      ∃ ω, AnsweredS closedCall ω ∧
        InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω :=
  Silmaril.Proofs.Wasm.Abstract.StoreCall.exposed_of_localDiv hL

/-- **Productive local divergence.** An infinite run of the exposed body with
every call event answered by `closedCall` is local divergence. -/
theorem localDiv_of_exposedInf {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {ω : Nat → Call (CallSig H)} (hA : AnsweredS closedCall ω)
    (h : InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω) :
    Interp.LocalDiv s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.StoreCall.localDiv_of_prod ⟨ω, hA, h⟩

theorem exposed_of_wasmLocalDiv {z : (wasmOShape H).self.Op} (h : wasmLocalDiv z) :
    ExposedSilent z ∨ ExposedInf z := by
  obtain ⟨fi, fn, hfi, hcode, hL⟩ := h
  rcases exposed_of_localDiv hL with ⟨cs, hA, hp⟩ | ⟨ω, hA, hp⟩
  · exact .inl ⟨fi, fn, hfi, hcode, cs, hA, hp⟩
  · exact .inr ⟨fi, fn, hfi, hcode, ω, hA, hp⟩

theorem wasmLocalDiv_of_exposedInf {z : (wasmOShape H).self.Op} (h : ExposedInf z) :
    wasmLocalDiv z := by
  obtain ⟨fi, fn, hfi, hcode, ω, hA, hp⟩ := h
  exact ⟨fi, fn, hfi, hcode, localDiv_of_exposedInf hA hp⟩

/-- **Core 3.0 divergence, on exposed bodies.** A diverging typed invocation of a
native, arity-checked store reaches, by finitely many exposed descents, a call
whose exposed body diverges silently or runs forever answered, or starts an
infinite chain of exposed descents. Every profile. -/
theorem core_diverges_exposed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile)
    (h : Diverges P closedHost (invoke s a vs)) :
    (∃ z, ExposedPath ⟨a, (vs, s)⟩ z ∧ (ExposedSilent z ∨ ExposedInf z)) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
        ∀ n, ExposedReach (g n) (g (n + 1)) := by
  rcases (core_diverges_iff_exposed hs hF hS hok P).1 h with ⟨z, hp, hz⟩ | hc
  · exact .inl ⟨z, hp, exposed_of_wasmLocalDiv hz⟩
  · exact .inr hc

/-- **Conversely**, finitely many exposed descents to a call whose exposed body
runs forever answered, or an infinite chain of exposed descents, is Core 3.0
divergence. -/
theorem core_diverges_of_exposed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile)
    (h : (∃ z, ExposedPath ⟨a, (vs, s)⟩ z ∧ ExposedInf z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
        ∀ n, ExposedReach (g n) (g (n + 1))) :
    Diverges P closedHost (invoke s a vs) := by
  refine (core_diverges_iff_exposed hs hF hS hok P).2 ?_
  rcases h with ⟨z, hp, hz⟩ | hc
  · exact .inl ⟨z, hp, wasmLocalDiv_of_exposedInf hz⟩
  · exact .inr hc

/-- **Core 3.0 divergence, exactly, on exposed bodies.** On a typed invocation of
a native, arity-checked store, at every profile: the invocation diverges exactly
when finitely many exposed descents reach a call whose exposed body diverges
silently (no unanswered call) or has an infinite run answered by `closedCall`
(infinitely many returning calls), or an infinite chain of exposed descents
starts at it. -/
theorem core_diverges_iff_exposed_local {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Diverges P closedHost (invoke s a vs) ↔
      (∃ z, ExposedPath ⟨a, (vs, s)⟩ z ∧ (ExposedSilent z ∨ ExposedInf z)) ∨
        ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
          ∀ n, ExposedReach (g n) (g (n + 1)) := by
  refine ⟨core_diverges_exposed hs hF hS hok P, fun h => ?_⟩
  rcases h with ⟨z, hp, hsil | hinf⟩ | hc
  · by_contra hnd
    have hnf : ¬ Silmaril.Wasm.Interp.FunDiv s a vs :=
      fun hd => hnd ((Silmaril.Wasm.Interp.core_diverges_iff_funDiv hs hF hS hok P).2 hd)
    rw [Silmaril.Wasm.Interp.funDiv_iff_invokeRun_none hs hF hS hok] at hnf
    push Not at hnf
    obtain ⟨fuel, hfuel⟩ := hnf
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hfuel
    obtain ⟨fi, fn, r', hfi, hcode, hev⟩ :=
      Silmaril.Proofs.Wasm.Abstract.StoreCall.eval_of_invokeRun hF hr
    obtain ⟨fi₂, fn₂, r₂, hfi₂, hcode₂, hev₂⟩ :=
      Silmaril.Proofs.Wasm.Abstract.StoreCall.eval_of_bodyPath (bodyPath_iff_exposed.2 hp)
        ⟨fi, fn, r', hfi, hcode, hev⟩
    obtain ⟨fi₃, fn₃, hfi₃, hcode₃, cs, hA, hpath⟩ := hsil
    rw [hfi₂] at hfi₃; cases hfi₃
    rw [hcode₂] at hcode₃; cases hcode₃
    exact Silmaril.Proofs.Wasm.Abstract.StoreCall.not_silent_of_eval hev₂ hA hpath
  · exact core_diverges_of_exposed hs hF hS hok P (.inl ⟨z, hp, hinf⟩)
  · exact core_diverges_of_exposed hs hF hS hok P (.inr hc)

end Silmaril.Wasm.Abstract.StoreCall
