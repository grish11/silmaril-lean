module

public import Silmaril.Games.Abstract.Exception.Defs
public import Silmaril.Wasm.Abstract.SSAFragment.Thms
public import Silmaril.Wasm.Execution.Core.Properties

/-!
# Exception properties of concrete Core 3.0 code

Both directions, through the actual Core 3.0 rules.

* **No escape** (`IsFragmentSite.noThrow`, `IsFragmentSite.not_mayEscape`): a
  structured native λSSA fragment function never lets an exception escape on
  any typed invocation, under any profile with a closed host. Its behaviours
  are its fragment run outcomes (`behaviours_eq_run`), which are returns, traps
  and divergence only. This is a semantic no-escape certificate: no
  *executable* run escapes. It says nothing about syntactic graph paths.
* **Escape** (`throw_in_frame_escapes`): a `throw` of a tag without
  parameters, as the body of an activation frame, escapes. The configuration
  reaches `throwing` by the Core 3.0 rules `throw`, `throw_ref-label` and
  `throw_ref-frame`, so its behaviours contain `throws`.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games.Abstract Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SSA Silmaril.Wasm.Validation

variable {H : Type}

/-- Fragment functions never throw out of a typed invocation. -/
theorem IsFragmentSite.noThrow {x : CallSite H} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hx : IsFragmentSite x ft bf f) {vs : List Val} (hok : InvokeOk x.store x.addr vs)
    (P : Numerics.Profile) (a : Nat) : Behaviour.throws a ∉ Silmaril.Wasm.Abstract.callSem P x vs := by
  obtain ⟨args, -, -, h⟩ := hx.callSem hok P
  rw [h]
  rintro (⟨o, -, ho⟩ | ⟨ho, -⟩)
  · rcases o with (_ | _) | _ <;> simp [outBeh] at ho
  · cases ho

/-- Fragment functions have no escaping run, as abstract functions. -/
theorem IsFragmentSite.not_mayEscape {x : CallSite H} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hx : IsFragmentSite x ft bf f) {vs : List Val} (hok : InvokeOk x.store x.addr vs)
    (P : Numerics.Profile) : ¬ AFun.MayEscape (wasmFun P closedHost x.addr) x.store vs := by
  rintro ⟨c, a, s', hm⟩
  apply hx.noThrow hok P a
  rw [callSem_eq_image]
  exact ⟨_, hm, rfl⟩

/-- A `throw` of a parameterless tag as a frame's body escapes. -/
theorem throw_in_frame_escapes {P : Numerics.Profile} {host : HostSemantics H} {s : Store H}
    {f fi : Frame} {n m : Nat} {cont : List Instr} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (ht : s.tag? fi x = some (ta, ti)) (he : Expand ti.type (.func .nil .nil)) :
    Behaviour.throws s.exns.length ∈
      behavioursOf P host ⟨s, f, [.frame n fi [.label m cont [.plain (.throw x)]]]⟩ := by
  have h₀ : Step P host ⟨s, fi, [.plain (.throw x)]⟩
      ⟨s.addExn ⟨ta, []⟩, fi, throwing s.exns.length⟩ :=
    Step.throw (vs := []) ht he rfl
  have h₁ := Step.ctxtFrame (f := f) (n := n) (Step.ctxtLabel (n := m) (cont := cont) h₀)
  have h₂ : Step P host ⟨s.addExn ⟨ta, []⟩, f, [.frame n fi [.label m cont (throwing s.exns.length)]]⟩
      ⟨s.addExn ⟨ta, []⟩, f, [.frame n fi (throwing s.exns.length)]⟩ :=
    Step.ctxtFrame Step.throwRefLabel
  have h₃ : Step P host ⟨s.addExn ⟨ta, []⟩, f, [.frame n fi (throwing s.exns.length)]⟩
      ⟨s.addExn ⟨ta, []⟩, f, throwing s.exns.length⟩ := Step.throwRefFrame
  exact mem_behavioursOf (r := .throw s.exns.length)
    (h₁.steps.trans (h₂.steps.trans h₃.steps)) rfl

end Silmaril.Wasm.Abstract
