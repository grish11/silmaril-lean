module

import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Observation.Thms
import Silmaril.Wasm.Component.Reference.Litmus.Thms
import Silmaril.Wasm.Validation.Intrinsic.ReifyThms

open Silmaril Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.IntrinsicWiring Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus

private def rawAdder : Core3Component := adderS.toRef

private def typedAdder :=
  (Closed.lift? .p2 core3Profile core3ModuleType? rawAdder).get (by decide +kernel)

private def addType : Types.FuncType Nat :=
  { params := labels "a" [.prim .u32, .prim .u32], result := some (.prim .u32) }

private def exposeAdd : Exposure typedAdder.1 "add" (.func addType) :=
  ⟨⟨0, by decide +kernel⟩, by with_unfolding_all rfl⟩

example : ValidComponentCore3 .p2 typedAdder.2.val.erase typedAdder.1 :=
  checkCore3?_sound typedAdder.2.val.checked

private abbrev TypedPayload := Σ raw : Wasm.Module, Wasm.Validation.Intrinsic.Reify.Reified raw

private def reifiedBody : TypedPayload :=
  ⟨_, (Wasm.Validation.Intrinsic.Reify.reify? (binCore3 .add)).get (by decide +kernel)⟩

private def bodyErase (payload : TypedPayload) := payload.2.typed.erase

private def typedBodySource : Syntax.Component TypedPayload := Syntax.Component.map (fun _ => reifiedBody) rawAdder

private def typedBodyComponent :=
  (Closed.lift? .p2 core3Profile (core3ModuleType? ∘ bodyErase) typedBodySource).get
    (by decide +kernel)

private def fromIntrinsic := typedBodyComponent.2.val.map bodyErase (fun checked => checked)

example : fromIntrinsic.erase = rawAdder := by
  rw [fromIntrinsic, Closed.erase_map, typedBodyComponent.2.property]
  rfl

private def limeAdder : Lime1.Module :=
  (Lime1.Module.ofCore? (binCore3 .add)).get (by decide +kernel)

private def nativeSyntax : Syntax.Component Lime1.Module := Syntax.Component.map (fun _ => limeAdder) rawAdder

private def nativeAdder :=
  (Closed.lift? .p2 lime1Profile lime1ModuleType nativeSyntax).get (by decide +kernel)

example : checkLime1? .p2 nativeAdder.2.val.erase = .ok nativeAdder.1 := nativeAdder.2.val.checked

private def badBodySyntax : Syntax.Component Lime1.Module :=
  Syntax.Component.map (fun _ => {limeAdder with funcs := limeAdder.funcs.map fun func => {func with body := []}})
    rawAdder

example : (checkLime1? .p2 badBodySyntax).isOk = true := by decide +kernel

example : (Closed.lift? .p2 core3Profile (core3ModuleType? ∘ Lime1.Module.toCore) badBodySyntax).isSome = false :=
  by decide +kernel

private def projectedAdder :=
  (Closed.lift? .p2 core3Profile (core3ModuleType? ∘ Lime1.Module.toCore) nativeSyntax).get (by decide +kernel)

private def fromLime := projectedAdder.2.val.map Lime1.Module.toCore (fun checked => checked)

private theorem fromLime_exact : fromLime.erase = rawAdder := by
  rw [fromLime, Closed.erase_map, projectedAdder.2.property]
  rfl

private def exposeLime : Exposure projectedAdder.1 "add" (.func addType) :=
  ⟨⟨0, by decide +kernel⟩, by with_unfolding_all rfl⟩

private theorem adderAdequate : adderS.Adequate := by
  refine ⟨adderS_good, ?_, adderS_inst, adderS_arity⟩
  intro expo listed
  simp only [adderS, List.mem_singleton] at listed
  subst expo
  exact ⟨rfl, rfl⟩

private theorem projectedReturns (P : Numerics.Profile) (prof : ProfileKind) (left right : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 (left + right))]) ∈
      exportBehaviours prof (refHost P) () fromLime.erase [] "add"
        [toRefVal (.u32 left), toRefVal (.u32 right)] := by
  have transfer := fromLime.terminal_iff fromLime_exact adderAdequate P prof ⟨0, by decide⟩ exposeLime
    [.u32 left, .u32 right] rfl (.returns (some [toRefVal (.u32 (left + right))])) trivial
  have observed := transfer.mpr ⟨[.u32 (left + right)], rfl, adder_ir P left right⟩
  rwa [exposeLime.entry] at observed

example : (Closed.lift? .p2 core3Profile core3ModuleType?
    [.coreInstance (.instantiate 0 [])]).isSome = false := by decide +kernel

example : (Closed.lift? .p2 core3Profile core3ModuleType?
    [.component rawAdder]).isSome = false := by decide +kernel

#print axioms Program.lift_erase
#print axioms Closed.lift_erase
#print axioms Closed.lift_isSome_iff
#print axioms Closed.sound
#print axioms Closed.erase_map
#print axioms Closed.terminal_iff
#print axioms fromLime_exact
#print axioms projectedReturns
