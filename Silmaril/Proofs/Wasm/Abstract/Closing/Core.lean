module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
import Silmaril.Proofs.Wasm.Abstract.Closing.Basic

/-!
# The closed open module against Core 3.0: proofs

With the closed host, on typed, native, arity-checked stores, a function's
Core 3.0 abstract function `wasmFun` is `Shape.close wasmOpen`, plus
divergence exactly when the closure has no behaviour.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Closing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem endOfFlow_of_flowBeh {fl : Flow} {r : Result} (s : Store H)
    (h : flowBeh fl = some r.toBehaviour) : endOfFlow fl s = endOfResult r s := by
  rcases fl with ws | ⟨_, ws⟩ | ws | _ | t <;> rcases r with vs | a | _ <;>
    simp_all [flowBeh, Result.toBehaviour, endOfFlow, endOfResult]

theorem result_of_closedOutcome {s : Store H} {a : Nat} {vs : List Val} {s' : Store H} {fl : Flow}
    (h : ClosedOutcome s a vs s' fl) : ∃ r : Result, flowBeh fl = some r.toBehaviour := by
  obtain ⟨-, -, -, rs, -, bfl, -, -, -, -, hx⟩ := h
  rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> simp only [exitFlow, Option.some.injEq,
    reduceCtorEq] at hx <;> subst hx
  · exact ⟨.values _, rfl⟩
  · exact ⟨.values _, rfl⟩
  · exact ⟨.values _, rfl⟩
  · exact ⟨.trap, rfl⟩
  · exact ⟨.throw t, rfl⟩

theorem flowBeh_ne_diverges (fl : Flow) : flowBeh fl ≠ some .diverges := by
  rcases fl <;> simp [flowBeh]

theorem toBehaviour_ne_diverges (r : Result) : r.toBehaviour ≠ .diverges := by
  cases r <;> simp [Result.toBehaviour]

/-- Core 3.0 divergence of a native invocation is the absence of closed
outcomes. -/
theorem diverges_iff {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Diverges P closedHost (invoke s a vs) ↔ ∀ s' fl, ¬ ClosedOutcome s a vs s' fl := by
  have he := behaviours_eq_closed hs hF hS hok P
  constructor
  · intro hd
    have hb : Behaviour.diverges ∈ behaviours P closedHost s a vs := .inr ⟨rfl, hd⟩
    rw [he] at hb
    rcases hb with ⟨_, fl, -, hfl⟩ | ⟨-, h⟩
    · exact absurd hfl (flowBeh_ne_diverges fl)
    · exact h
  · intro h
    have hb : Behaviour.diverges ∈ behaviours P closedHost s a vs := by
      rw [he]
      exact .inr ⟨rfl, h⟩
    rcases hb with ⟨_, r, -, -, hr⟩ | ⟨-, hd⟩
    · exact absurd hr.symm (toBehaviour_ne_diverges r)
    · exact hd

/-- **Core 3.0 functions are the closure of the open module**, plus divergence
exactly when the closure is empty. -/
theorem wasmFun_eq_close {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    wasmFun P closedHost a s vs =
      Shape.close wasmOpen a s vs ∪ {x | x = ([], .div) ∧ Shape.close wasmOpen a s vs = ∅} := by
  have hcl : Shape.close wasmOpen a s vs = ∅ ↔ ∀ s' fl, ¬ ClosedOutcome s a vs s' fl := by
    rw [close_wasmOpen, Set.eq_empty_iff_forall_notMem]
    exact ⟨fun h s' fl hc => h _ ⟨s', fl, hc, rfl⟩, fun h _ ⟨s', fl, hc, _⟩ => h s' fl hc⟩
  ext x
  rw [Set.mem_union, Set.mem_ofPred_eq, hcl, ← diverges_iff hs hF hS hok P, close_wasmOpen]
  constructor
  · rintro (⟨c', r, hst, hc, rfl⟩ | ⟨rfl, hd⟩)
    · obtain ⟨fl, hco, hb⟩ :=
        (core_result_iff_closed hs hF hS hok P r c'.store).mp ⟨c', hst, hc, rfl⟩
      exact .inl ⟨_, fl, hco, by rw [endOfFlow_of_flowBeh _ hb]⟩
    · exact .inr ⟨rfl, hd⟩
  · rintro (⟨s', fl, hco, rfl⟩ | ⟨rfl, hd⟩)
    · obtain ⟨r, hb⟩ := result_of_closedOutcome hco
      obtain ⟨c', hst, hc, rfl⟩ := (core_result_iff_closed hs hF hS hok P r s').mpr ⟨fl, hco, hb⟩
      exact .inl ⟨c', r, hst, hc, by rw [endOfFlow_of_flowBeh _ hb]⟩
    · exact .inr ⟨rfl, hd⟩

end Silmaril.Proofs.Wasm.Abstract.Closing
