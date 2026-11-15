module

public import Silmaril.Wasm.Abstract.StoreBody.Defs
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Abstract.StoreBody.Basic
import Silmaril.Proofs.Wasm.Abstract.StoreBody.Complete
import Silmaril.Proofs.Wasm.Abstract.StoreBody.Invoke

/-!
# Folded Wasm bodies over the actual store: theorems

For the denotation `den`/`denList` of folded trees into `BodyM` over the actual
store (`Silmaril.Wasm.Abstract.StoreBody.Defs`):

* **Primitives are the interpreter's.** `run_flatK`: a lifted flat instruction
  runs to exactly the tree of `Binaryen.evalFlat`'s outcome on the current
  store: the new store and frame with its flow, the trap, or (no outcome)
  silent divergence. In particular the store effects of `global.set` and of
  integer `store` are `evalFlat`'s (`run_globalSet` as an example).
* **Loops are Elgot iteration.** `den_loop_unfold`: the fixpoint law unfolds a
  loop once.
* **Sound for the native interpreter.** `run_sound`: on call-free,
  `try_table`-free trees, every outcome of `Binaryen.run` (any fuel) is the
  abstract body's outcome, with the same final store, frame and flow (a trap
  as the trap effect).

* **Exact for the native interpreter.** `eval_den`: every derivation of the
  interpreter's fuel-free big-step relation `Binaryen.Eval` is computed by the
  abstract body; `den_cases`: the abstract body either diverges or computes an
  `Eval` outcome; `den_diverge_iff`: it diverges exactly when `Binaryen.run`
  has no result at any fuel.

* **Invocations and Core 3.0.** `denInvoke a vs` is the abstract invocation of
  the function at `a` of the current store (callee frame, body, call outcome).
  For a call-free function (`CallFreeAt`): `invoke_sound` (every `invokeRun`
  result is computed), `invoke_diverge_iff` (divergence is fuel exhaustion),
  and, on typed, native, arity-checked stores at every profile,
  `invoke_core_result` (**the Core 3.0 runs of the invocation to a value or
  exception result are exactly the abstract invocation's outcomes, final store
  included**) and `invoke_core_trap` (Core traps exactly when the abstract
  invocation traps), `invoke_core_diverges` (Core may diverge exactly when the
  abstract invocation diverges).

**Not yet.** Calls inside bodies (F4) and `try_table` (F5).
-/

public section

namespace Silmaril.Wasm.Abstract.StoreBody

open Silmaril.Wasm Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core

variable {E : Sig.{0}} {H : Type}

/-- **The lifted primitive.** A flat instruction's body runs to the tree of the
native interpreter step on the current store. -/
theorem run_flatK (i : Instr) (f : Frame) (stk : List Val) (s : Store H) :
    ((flatK i f stk : M E H Res).run ⟨s⟩).run = evalTree (evalFlat s f stk i) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.run_flatK i f stk s

/-- Example of a store effect: `global.set` writes the global through
`Store.setGlobal`, as `evalFlat` does. -/
theorem run_globalSet (g : GlobalIdx) (f : Frame) (v : Val) (r : List Val) (s : Store H)
    {p : Nat × GlobalInst} (hg : s.global? f g = some p) :
    ((flatK (.globalSet g) f (v :: r) : M E H Res).run ⟨s⟩).run =
      Silmaril.Elgot.ITree.ret (.ok (⟨(f, .normal r)⟩, ⟨s.setGlobal p.1 v⟩)) := by
  rw [run_flatK]; simp [evalFlat, hg, evalTree]

/-- A loop unfolds once (the Elgot fixpoint law). -/
theorem den_loop_unfold (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (den (.loop bt body) f stk : M E H Res) =
      (loopBody bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => den (.loop bt body) c.down.1 c.down.2) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.den_loop_unfold bt body f stk

/-- **Sound for the native interpreter.** On call-free trees, every outcome of
`Binaryen.run`, at any fuel, is the abstract body's outcome. -/
theorem run_sound {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (hc : callFreeL es = true) (h : run n s f stk es = some r) :
    ((denList es f stk : M E H Res).run ⟨s⟩).run = evalTree (some r) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.run_sound n hc h

/-- Every big-step derivation of the interpreter is computed by the abstract body. -/
theorem eval_den {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (hc : callFreeL es = true) (h : Eval s f stk es r) :
    ((denList es f stk : M E H Res).run ⟨s⟩).run = evalTree (some r) := by
  obtain ⟨n, hn⟩ := run_of_eval h
  exact run_sound hc hn

/-- **Complete.** The abstract body of a call-free list diverges, or computes the
outcome of a big-step derivation of the interpreter. -/
theorem den_cases {es : List BExpr} (hc : callFreeL es = true) (s : Store H) (f : Frame)
    (stk : List Val) :
    ((denList es f stk : M E H Res).run ⟨s⟩).run = Silmaril.Elgot.ITree.diverge ∨
      ∃ r, Eval s f stk es r ∧ ((denList es f stk : M E H Res).run ⟨s⟩).run = evalTree (some r) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.list_good es hc s f stk

theorem evalTree_ne_diverge (r : Store H × Frame × Flow) :
    (evalTree (E := E) (some r)) ≠ Silmaril.Elgot.ITree.diverge := by
  obtain ⟨s', f', fl⟩ := r
  cases fl <;> exact Silmaril.Elgot.ITree.ret_ne_diverge _

/-- **Divergence is fuel exhaustion.** The abstract body of a call-free list
diverges exactly when the native interpreter has no result at any fuel. -/
theorem den_diverge_iff {es : List BExpr} (hc : callFreeL es = true) (s : Store H) (f : Frame)
    (stk : List Val) :
    ((denList es f stk : M E H Res).run ⟨s⟩).run = Silmaril.Elgot.ITree.diverge ↔
      ∀ n, run n s f stk es = none := by
  constructor
  · intro hd n
    cases hn : run n s f stk es with
    | none => rfl
    | some r => exact absurd ((run_sound hc hn).symm.trans hd) (evalTree_ne_diverge r)
  · intro hn
    rcases den_cases (E := E) hc s f stk with hd | ⟨r, hr, -⟩
    · exact hd
    · obtain ⟨m, hm⟩ := run_of_eval hr
      rw [hn m] at hm; cases hm

/-! ## Invocations -/

/-- Every `invokeRun` result of a call-free function is the abstract invocation's. -/
theorem invoke_sound {s : Store H} {a : Nat} {vs : List Val} (hc : CallFreeAt s a)
    {fuel : Nat} {r : Store H × Flow} (h : invokeRun fuel s a vs = some r) :
    ((denInvoke a vs : M E H _).run ⟨s⟩).run = invTree (some r) :=
  (Silmaril.Proofs.Wasm.Abstract.StoreBody.invoke_exact hc).1 fuel r h

/-- The abstract invocation of a call-free function diverges exactly when
`invokeRun` has no result at any fuel. -/
theorem invoke_diverge_iff {s : Store H} {a : Nat} {vs : List Val} (hc : CallFreeAt s a) :
    ((denInvoke a vs : M E H _).run ⟨s⟩).run = Silmaril.Elgot.ITree.diverge ↔
      ∀ fuel, invokeRun fuel s a vs = none := by
  constructor
  · intro hd fuel
    cases h : invokeRun fuel s a vs with
    | none => rfl
    | some r =>
      have := (invoke_sound (E := E) hc h).symm.trans hd
      obtain ⟨s', fl⟩ := r
      cases fl <;> exact absurd this (Silmaril.Elgot.ITree.ret_ne_diverge _)
  · intro hn
    rcases (Silmaril.Proofs.Wasm.Abstract.StoreBody.invoke_exact (E := E) (vs := vs) hc).2 with
      hd | ⟨fuel, r, h, -⟩
    · exact hd
    · rw [hn fuel] at h; cases h

theorem flowBeh_trap {fl : Flow} {r : Result} (hr : r ≠ .trap)
    (h : flowBeh fl = some r.toBehaviour) : fl ≠ .trap := by
  rintro rfl
  cases r <;> simp_all [flowBeh, Result.toBehaviour]

/-- **Core 3.0, value and exception results.** On a typed invocation of a
native, arity-checked store, at every profile, for a call-free function: the
Core runs of the invocation to a non-trap result `r` with final store `s'` are
exactly the abstract invocation's outcomes with that store and behaviour. -/
theorem invoke_core_result {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hc : CallFreeAt s a) (P : Numerics.Profile) (r : Result)
    (hr : r ≠ .trap) (s' : Store H) :
    (∃ c : Config H, Steps P closedHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧
        c.store = s') ↔
      ∃ fl, ((denInvoke a vs : M E H _).run ⟨s⟩).run =
          Silmaril.Elgot.ITree.ret (.ok (⟨fl⟩, ⟨s'⟩)) ∧ flowBeh fl = some r.toBehaviour := by
  rw [Silmaril.Wasm.Interp.native_store_adequacy hs hF hS hok P r s']
  constructor
  · rintro ⟨fuel, fl, h, hb⟩
    refine ⟨fl, ?_, hb⟩
    rw [invoke_sound hc h]
    have := flowBeh_trap hr hb
    cases fl <;> first | exact absurd rfl this | rfl
  · rintro ⟨fl, h, hb⟩
    rcases (Silmaril.Proofs.Wasm.Abstract.StoreBody.invoke_exact (E := E) (vs := vs) hc).2 with
      hd | ⟨fuel, ⟨s'', fl''⟩, h', he⟩
    · change ((denInvoke a vs : M E H _).run ⟨s⟩).run = _ at hd
      rw [h] at hd; exact absurd hd (Silmaril.Elgot.ITree.ret_ne_diverge _)
    · change ((denInvoke a vs : M E H _).run ⟨s⟩).run = _ at he
      rw [h] at he
      refine ⟨fuel, fl, ?_, hb⟩
      rw [h']
      cases fl'' <;> simp [invTree] at he <;> obtain ⟨rfl, rfl⟩ := he <;> rfl

/-- **Core 3.0, traps.** On a typed invocation of a native, arity-checked store,
at every profile, for a call-free function: Core traps exactly when the abstract
invocation traps. -/
theorem invoke_core_trap {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hc : CallFreeAt s a) (P : Numerics.Profile) :
    (∃ c : Config H, Steps P closedHost (invoke s a vs) c ∧ c.code = [.trap]) ↔
      ((denInvoke a vs : M E H _).run ⟨s⟩).run = Silmaril.Elgot.ITree.ret (.error ⟨⟩) := by
  constructor
  · rintro ⟨c, hst, hcode⟩
    obtain ⟨fuel, fl, h, hb⟩ :=
      (Silmaril.Wasm.Interp.native_store_adequacy hs hF hS hok P .trap c.store).1
        ⟨c, hst, hcode, rfl⟩
    rw [invoke_sound hc h]
    cases fl <;> simp_all [flowBeh, Result.toBehaviour, invTree]
  · intro h
    rcases (Silmaril.Proofs.Wasm.Abstract.StoreBody.invoke_exact (E := E) (vs := vs) hc).2 with
      hd | ⟨fuel, ⟨s'', fl⟩, h', he⟩
    · change ((denInvoke a vs : M E H _).run ⟨s⟩).run = _ at hd
      rw [h] at hd; exact absurd hd (Silmaril.Elgot.ITree.ret_ne_diverge _)
    · change ((denInvoke a vs : M E H _).run ⟨s⟩).run = _ at he
      rw [h] at he
      have hfl : fl = .trap := by
        cases fl <;> first | rfl | (have := Silmaril.Elgot.ITree.ret_inj.1 he; cases this)
      subst hfl
      obtain ⟨c, hst, hc', -⟩ :=
        (Silmaril.Wasm.Interp.native_store_adequacy hs hF hS hok P .trap s'').2
          ⟨fuel, .trap, h', rfl⟩
      exact ⟨c, hst, hc'⟩

/-- **Core 3.0, divergence.** On a typed invocation of a native, arity-checked
store, at every profile, for a call-free function: the invocation may diverge
in Core exactly when the abstract invocation diverges. -/
theorem invoke_core_diverges {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hc : CallFreeAt s a) (P : Numerics.Profile) :
    Behaviour.diverges ∈ behaviours P closedHost s a vs ↔
      ((denInvoke a vs : M E H _).run ⟨s⟩).run = Silmaril.Elgot.ITree.diverge := by
  rw [Silmaril.Wasm.Interp.native_adequacy hs hF hS hok, invoke_diverge_iff hc]
  constructor
  · rintro (⟨fuel, s', fl, -, hb⟩ | ⟨-, hn⟩)
    · cases fl <;> simp [flowBeh] at hb
    · exact hn
  · exact fun hn => .inr ⟨rfl, hn⟩

end Silmaril.Wasm.Abstract.StoreBody
