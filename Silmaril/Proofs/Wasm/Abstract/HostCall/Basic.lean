module

public import Silmaril.Wasm.Abstract.HostCall.Defs

/-!
# Core 3.0 host calls as a relational host (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Validation

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- An allowed answer is one Core step of the host call, in any frame. -/
theorem answer_step {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val} {r : Result}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hans : coreHostRel host ⟨h, s, us⟩ (.answer (s', r))) :
    Step P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ⟨s', f, r.toAdmin⟩ :=
  Step.callRefHost trivial hf he hn hcode hans

/-- Allowed divergence makes the call diverge in Core, in any frame. -/
theorem diverge_diverges {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hdiv : coreHostRel host ⟨h, s, us⟩ .diverge) :
    Diverges P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ :=
  ⟨fun _ => _, rfl, fun _ => Step.callRefHostDiv trivial hf he hn hcode hdiv⟩

/-- The relational host is functional exactly when the host semantics is
deterministic. -/
theorem functional_iff :
    (coreHostRel host).Functional ↔
      ∀ h s vs (o o' : HostOutcome H), host h s vs o → host h s vs o' → o = o' := by
  constructor
  · intro hR h s vs o o' ho ho'
    rcases o with ⟨s₁, r₁⟩ | _ <;> rcases o' with ⟨s₂, r₂⟩ | _
    · have := hR ⟨h, s, vs⟩ (.answer (s₁, r₁)) (.answer (s₂, r₂)) ho ho'
      cases this
      rfl
    · cases hR ⟨h, s, vs⟩ (.answer (s₁, r₁)) .diverge ho ho'
    · cases hR ⟨h, s, vs⟩ .diverge (.answer (s₂, r₂)) ho ho'
    · rfl
  · intro hD m o o' ho ho'
    rcases o with ⟨s₁, r₁⟩ | _ <;> rcases o' with ⟨s₂, r₂⟩ | _
    · cases hD _ _ _ _ _ ho ho'
      rfl
    · cases hD _ _ _ _ _ ho ho'
    · cases hD _ _ _ _ _ ho ho'
    · rfl

end Silmaril.Proofs.Wasm.Abstract.HostCall
