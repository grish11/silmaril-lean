module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Logic.Core.Thms

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

/-- A direct `call` of a host function answered by the host, under values `ws`
and before `rest`: two Core steps (`call`, then `call_ref-hostfunc`). -/
theorem steps_call_answer {s s' : Store H} {f : Frame} {x : Silmaril.Wasm.FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us ws : List Val} {r : Result} {rest : List Admin}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length) (hcode : fi.code = .host h)
    (hans : coreHostRel host ⟨h, s, us⟩ (.answer (s', r))) :
    Steps P host ⟨s, f, vals ws ++ vals us ++ .plain (.call x) :: rest⟩
      ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ := by
  have h₁ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) (ws ++ us) rest
    (Step.call (s := s) (f := f) hx hf)
  have h₂ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
    (answer_step (f := f) hf he hn hcode hans)
  simp only [vals_append, List.append_assoc, List.singleton_append] at h₁ h₂ ⊢
  exact Relation.ReflTransGen.head h₁ (Relation.ReflTransGen.single (by simpa using h₂))

/-- A direct `call` of a host function on which the host may diverge diverges in
Core, under values `ws` and before `rest`. -/
theorem diverges_call {s : Store H} {f : Frame} {x : Silmaril.Wasm.FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us ws : List Val} {rest : List Admin}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length) (hcode : fi.code = .host h)
    (hdiv : coreHostRel host ⟨h, s, us⟩ .diverge) :
    Diverges P host ⟨s, f, vals ws ++ vals us ++ .plain (.call x) :: rest⟩ := by
  have h₁ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) (ws ++ us) rest
    (Step.call (s := s) (f := f) hx hf)
  have h₂ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
    (Step.callRefHostDiv (f := f) (c := .callRefType fi.type) trivial hf he hn hcode hdiv)
  simp only [vals_append, List.append_assoc, List.singleton_append] at h₁ h₂ ⊢
  let L : Config H := ⟨s, f, vals ws ++ (vals us ++ .ref (.func a) :: .callRefType fi.type :: rest)⟩
  refine ⟨fun n => if n = 0 then ⟨s, f, vals ws ++ (vals us ++ .plain (.call x) :: rest)⟩ else L,
    rfl, fun n => ?_⟩
  rcases n with _ | n
  · simpa [L] using h₁
  · simpa [L] using h₂

end Silmaril.Proofs.Wasm.Abstract.HostCall
