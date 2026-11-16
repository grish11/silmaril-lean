module

public import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Proofs.Wasm.Execution.Core.InversionHost

/-!
# Inversion of `call_ref` on a host function

The host counterpart of `Step.callRef_wasm_inv`
(`Silmaril.Wasm.Execution.Core.Inversion.Thms`). Proofs:
`Silmaril.Proofs.Wasm.Execution.Core.InversionHost`.

* `Step.callRef_host_inv`: a step of `vals vs ++ [ref.func a, call_ref]` with a
  host function at `a` either takes a host answer or stutters on host
  divergence, on the top `ps.length` values.
* `Step.callRef_host_stuck`: with exactly the arguments, a call the host has no
  outcome for has no step.
-/

public section

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {c : Config H}

/-- A `call_ref` of a host function takes a host answer or stutters on host divergence. -/
theorem Step.callRef_host_inv {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {hh : H}
    (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
      ((∃ s' res, host hh s vs₂ (.returned s' res) ∧ c = ⟨s', f, vals vs₁ ++ res.toAdmin⟩) ∨
        (host hh s vs₂ .diverged ∧ c = ⟨s, f, vals vs₁ ++ vals vs₂ ++ [.ref (.func a), r]⟩)) :=
  Proofs.Inversion.callRef_host_inv h hr hf hcode rfl

/-- **A host call with no host outcome is stuck.** -/
theorem Step.callRef_host_stuck {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (hno : ∀ o, ¬ host hh s vs o) : ¬ Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c :=
  Proofs.Inversion.callRef_host_stuck hr hf hcode he hn hno

/-- **A host `call_ref` in a sequence context**: a host answer or a stutter on
the top arguments, the values below and the continuation untouched. -/
theorem Step.callRef_host_inv_seq {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {hh : H}
    {rest : List Admin} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (h : Step P host ⟨s, f, vals vs ++ .ref (.func a) :: r :: rest⟩ c) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
      ((∃ s' res, host hh s vs₂ (.returned s' res) ∧
          c = ⟨s', f, vals vs₁ ++ res.toAdmin ++ rest⟩) ∨
        (host hh s vs₂ .diverged ∧
          c = ⟨s, f, vals vs₁ ++ vals vs₂ ++ .ref (.func a) :: r :: rest⟩)) :=
  Proofs.Inversion.callRef_host_inv_seq hr hf hcode h

end Silmaril.Wasm.Execution.Core
