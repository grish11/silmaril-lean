module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Core

/-!
# Divergence of the fragment denotation is Core 3.0 divergence

For a validated fragment call site (`IsFragmentSite`: a typed store holding the
Core code of the function), the abstract body diverges exactly when the Core
3.0 invocation has an infinite run of steps (`Diverges`). So on validated code,
the denotation's divergence is never a stuck configuration: Core type safety
(`invoke_safe`, behind `behaviours_eq_run`) rules stuck runs out, and every
run without a fragment outcome is genuinely infinite.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
  Silmaril.Wasm.Abstract.FragBody Silmaril.Wasm.SSA Silmaril.Elgot.ITree
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {E : Sig.{0}} {S : Type 1}

theorem outBeh_some_ne_diverges (o : FOut) : outBeh (some o) ≠ .diverges := by
  rcases o with (_ | _) | _ <;> simp [outBeh]

theorem den_diverges_iff_core {H : Type} {x : Silmaril.Wasm.Abstract.CallSite H} {ft : FuncType}
    {bf : Binaryen.BFunc} {f : FragFunc} (hx : Silmaril.Wasm.Abstract.IsFragmentSite x ft bf f)
    {vs : List Val} (hok : InvokeOk x.store x.addr vs) (P : Numerics.Profile) {args : List WVal}
    (hv : vs = args.map WVal.toVal) (s : S) :
    run' (denFunc f ⟨args⟩ : M E S _) s = diverge ↔ Diverges P closedHost (invoke x.store x.addr vs) := by
  obtain ⟨args', hv', -, h⟩ := hx.callSem hok P
  obtain rfl := WVal.map_toVal_inj (hv'.symm.trans hv)
  rw [denFunc_diverge_iff' (E := E)]
  constructor
  · intro hno
    have hm : (Behaviour.diverges : Behaviour Val) ∈ Silmaril.Wasm.Abstract.callSem P x vs := by
      rw [h]; exact .inr ⟨rfl, hno⟩
    rcases hm with ⟨c', r, -, -, hb⟩ | ⟨-, hd⟩
    · cases r <;> simp [Result.toBehaviour] at hb
    · exact hd
  · intro hd o ho
    have hm : (Behaviour.diverges : Behaviour Val) ∈ Silmaril.Wasm.Abstract.callSem P x vs :=
      .inr ⟨rfl, hd⟩
    rw [h] at hm
    rcases hm with ⟨o', -, he⟩ | ⟨-, hno⟩
    · exact outBeh_some_ne_diverges o' he.symm
    · exact hno o ho

end Silmaril.Proofs.Wasm.Abstract.FragBody
