module

public import Silmaril.Proofs.Wasm.Interp.OracleSim
public import Silmaril.Proofs.Wasm.Interp.CallFrame
public import Silmaril.Wasm.Abstract.HostEval.Defs

/-!
# The host-call oracle is sound, for the native host slice (proofs)

`Abstract.hostCall host` answers Wasm callees by running their bodies and host
callees by the host. It is an `OracleSound` oracle (`hostCall_sound`), so
`evalO_good` makes every `EvalH host` run a Core 3.0 run, **for hosts in the
native host slice** `NativeHostSlice`:

* a host answer **extends** the store's functions as Core's `Extend` does
  (existing addresses keep their functions; new ones may be appended), and the
  appended functions keep the store native-profile and arity-checked
  (`FuncsGood`). So hosts that allocate functions are covered, as long as what
  they allocate is native code passing the check;
* returned values have the callee's declared result arity (as `HostOk`'s
  `ResultTyped` gives on typed stores);
* a host answer is not an exception (the native profile has no exceptions).

No determinism or totality of the host is assumed.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core Silmaril.Wasm.Abstract

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **The native host slice**: hosts whose answers extend the store's functions
(`FuncsGood`: Core extension, keeping the native profile and the arity check),
answer values at the declared result arity, and do not throw. -/
structure NativeHostSlice (host : HostSemantics H) : Prop where
  funcs : ∀ h s vs s' r, host h s vs (.returned s' r) → FuncsGood s.funcs s'.funcs
  arity : ∀ (s : Store H) (a : Nat) (fi : FuncInst H) (h : H) (ps rs : List Validation.CValType)
    (vs ws : List Val) (s' : Store H), s.funcs[a]? = some fi → fi.code = .host h →
    Validation.DefType.funcType? fi.type = some (ps, rs) →
    host h s vs (.returned s' (.values ws)) → ws.length = rs.length
  noThrow : ∀ h s vs s' t, ¬ host h s vs (.returned s' (.throw t))

/-- The oracle facts, as a call relation to close under. -/
def SoundAt (P : Numerics.Profile) (host : HostSemantics H) : CallRel H := fun s a us out =>
  ∀ (f : Frame) (fi : FuncInst H) (ps rs : List Validation.CValType),
    StoreChk s.funcs → s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob out.2 ∧
        FuncsGood s.funcs out.1.funcs) ∧
      (∀ vs, out.2.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨out.1, f, vals (vs.take rs.length).reverse⟩) ∧
      (out.2 = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨out.1, f, [.trap]⟩)

theorem soundAt_sound : OracleSound P host (SoundAt (H := H) P host) :=
  fun _ _ f _ fi ps rs _ _ hS hfi hty hn h => h f fi ps rs hS hfi hty hn

theorem hostCallOp_le_soundAt (hH : NativeHostSlice host) :
    hostCallOp host (SoundAt P host) ≤ SoundAt P host := by
  rintro s a us ⟨s₂, fl⟩ (hb | hh) f fi ps rs hS hfi hty hn
  · obtain ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hbody⟩ := hb
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    obtain ⟨aga, cga⟩ := evalO_good (P := P) (host := host) soundAt_sound hbody
    have hlocals : (Frame.forCall fi.module us fn.locals).locals.length =
        ps.length + fn.locals.length := forCall_length _ _ hn
    obtain ⟨ob, hb, hob⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
    have hbc : chk s.funcs (Frame.forCall fi.module us fn.locals).module
        (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [hlocals]
      exact hb
    obtain ⟨hok, inv⟩ := aga hS hbc
    obtain ⟨h₁, h₂, -⟩ := steps_callRef_of_good (P := P) (host := host) hS hn hfi hcode hty aga cga f
    exact ⟨⟨ob, hob, hok, inv.1⟩, h₁, h₂⟩
  · obtain ⟨fi', h, r, hfi', hcode, hhost, hfl⟩ := hh
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    dsimp only at hhost hfl
    subst hfl
    obtain ⟨ps', rs', he, hpl, hrl⟩ := expand_of_funcType hty
    have hstep : Step P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₂, f, r.toAdmin⟩ := Step.callRefHost trivial hfi he (hn.trans hpl.symm) hcode hhost
    have hF := hH.funcs _ _ _ _ _ hhost
    rcases r with ws | t | _
    · have hw := hH.arity s a fi h ps rs us ws s₂ hfi hcode hty hhost
      refine ⟨⟨some rs.length, .inr rfl, by simp [FlowOk, FlowOkE, resFlow, hw], hF⟩, fun vs hvs => ?_, ?_⟩
      · simp only [resFlow, Binaryen.Flow.retVals, Option.some.injEq] at hvs
        subst hvs
        have : (ws.reverse.take rs.length).reverse = ws := by
          rw [List.take_of_length_le (by simp [hw])]
          simp
        rw [this]
        exact .single hstep
      · intro h'
        simp [resFlow] at h'
    · exact (hH.noThrow _ _ _ _ _ hhost).elim
    · exact ⟨⟨none, .inl rfl, trivial, hF⟩, fun vs hvs => by simp [resFlow, Binaryen.Flow.retVals] at hvs,
        fun _ => .single hstep⟩

/-- **The host-call oracle is sound** for the native host slice. -/
theorem hostCall_sound (hH : NativeHostSlice host) : OracleSound P host (hostCall host) := by
  have hle : hostCall host ≤ SoundAt P host := OrderHom.lfp_le _ (hostCallOp_le_soundAt hH)
  intro s s₂ f a fi ps rs us fl hS hfi hty hn h
  exact hle s a us (s₂, fl) h f fi ps rs hS hfi hty hn

/-- **Forward simulation of the native semantics with host calls**, native host
slice, every profile: every `EvalH host` run of arity-checked code is a Core
3.0 run with the same host. -/
theorem evalH_good (hH : NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalH host s f stk es r) : ArityGood s f stk es r ∧ CoreGood P host s f stk es r :=
  evalO_good (hostCall_sound hH) h

end Silmaril.Wasm.Interp
