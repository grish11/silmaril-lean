module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Root
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.First
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Compose

/-!
# The fragment passes the root checks

* `rootChecked_of_multiImpFrag`: a component of `MultiImpFrag` passes the reference machine's
  root checks (`RootChecked`): its only import is `f: func(x: u32)` (`rootShape`, parameter name
  included), which the host supplies at that type;
* `startAdequacyFrag_of_checked`: so the start goal on the fragment is an instance of the
  corrected start goal `Task.startAdequacyChecked`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.SingleThreaded (neverFail)

/-- **The fragment passes the root checks.** -/
theorem rootChecked_of_multiImpFrag {r : RefComponent} (h : MultiImpFrag r) : RootChecked r := by
  obtain ⟨-, -, -, pre, mi, cargs, post, hs, hshape, hpost⟩ := multiImpFrag_inv h
  obtain ⟨pre', rfl, hni⟩ := rootShape_inv hshape
  have hrest : NoImport (pre' ++ Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) :=
    (noImport_prop hni).append (noImport_cons_inst (noImport_of_postOk hpost))
  have hr : r = .type (.func fFuncType) :: .import_ { name := "f" } (.func 0) ::
      (pre' ++ Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) := by
    rw [firstCore?_eq r hs]
    rfl
  subst hr
  unfold RootChecked rootChecked
  rw [Bool.and_eq_true]
  refine ⟨argsComplete_root hrest, ?_⟩
  show (precheckImports preStore (importArgs hostI) Frame.empty _).toBool = true
  erw [precheck_root hrest]
  rfl

/-- **The start goal on the fragment from the corrected start goal.** -/
theorem startAdequacyFrag_of_checked (h : Task.startAdequacyChecked) : Task.startAdequacyFrag :=
  fun b c r t n ws hc hr hv hf himp hex hu hp =>
    h b c r t n ws hc hr hv (inFrag_of_hostWired (multiImpFrag_inv hf).2.1)
      (rootChecked_of_multiImpFrag hf) himp hex hu hp

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
