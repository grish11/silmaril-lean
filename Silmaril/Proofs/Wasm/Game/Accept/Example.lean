module

public import Silmaril.Wasm.Game.Accept.Thms
public import Silmaril.Wasm.Game.Examples.Defs
import Silmaril.Proofs.Wasm.Game.Examples.StartImport
import Silmaril.Proofs.Wasm.Game.Linking.Callout

/-!
# Accepted inputs of a concrete module: proofs

Non-vacuity of `Silmaril.Wasm.Game.Accept.Callouts` on `exStart`
(`Silmaril.Wasm.Game.Examples`), whose start function calls its import `"env" "f"` with no
arguments: the run of `Silmaril.Proofs.Wasm.Game.Examples.run_to_callout` reaches the
host-call redex during instantiation, which `decompose?` finds (`decompose?_fill`), against an
environment that never answers (it satisfies the host contract vacuously).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Accept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.Examples Silmaril.Proofs.Wasm.Game.Examples

/-- The environment that never answers. -/
def mute : SEnv UImp := ⟨Unit, fun _ _ _ _ => False, fun _ _ => False⟩

theorem mute_ok (s : Store Nat) : UEnvOk s mute := fun _ _ _ _ _ _ _ _ h => h.elim

/-- `exStart`'s instance has no memory. -/
theorem t_mems : exPrep.1.frame.module.mems = [] := by decide +kernel

/-- **`exStart` calls `"env" "f"` with no arguments**, for every profile. -/
theorem exStart_callout (P : Profile) :
    (⟨("env", "f"), [], none⟩ : Callout) ∈ Callouts P UEnvOk 0 exStart := by
  obtain ⟨fi₀, fi₁, code, x, hl, h0, h1, hloc, hbody, hx, ht₀, ht₁, hm₁⟩ := exShape
  have hrun := run_to_callout (P := P) (host := fun _ _ _ _ => False) hl t_funcs h1 hloc
    hbody hx ht₁ hm₁
  refine ⟨exMT, exI, exC₀, ex_isSpecInstance, mute, (), mute_ok _, false,
    ⟨exPrep.1.store, exPrep.1.frame, [.frame 0 (Frame.forCall fi₁.module [] [])
      [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]]]⟩, (), ?_, ?_⟩
  · rw [exC₀_eq]
    exact Session.of_core_steps .start hrun
  · have hd := Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill (s := exPrep.1.store)
      (.frame [] 0 (Frame.forCall fi₁.module [] []) (.label [] 0 [] (.top [] []) []) [])
      (args := []) (a := 0) (c := .callRefType fi₀.type) trivial (by rw [hl]; rfl) (ty_nil ht₀)
      (by simp [Ty.length]) h0
    refine ⟨.frame [] 0 (Frame.forCall fi₁.module [] []) (.label [] 0 [] (.top [] []) []) [], 0, 0,
      ?_, rfl, ?_⟩
    · simpa [Ctx.fill, vals] using hd
    · simp [exC₀_eq, t_mems]

end Silmaril.Proofs.Wasm.Game.Accept
