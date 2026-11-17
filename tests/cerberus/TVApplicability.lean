import Silmaril.Project.Shapes.CTV.Thms
import Silmaril.Project.CTV.Examples.Defs

/-! Regression tests for the per-type profile check (`Silmaril.Cerberus.TV.Applicability`), from the
review of #911: the scan covers the runtime functions the program reaches, so a runtime function
with a floating result blocks the x86-64 profile (it did not when only the program part was
scanned). Kernel-checked with `cbv`. -/

open Silmaril.Cerberus Silmaril.Cerberus.TV Silmaril.Project.CTV.Examples Silmaril.Project.Shapes.CTV

set_option maxRecDepth 100000

/-- The `return 1 + 2;` file reaches its 3 runtime functions, which name `_Bool`. -/
example : (reachableStdlib foldSourceBindings).length = 3 := by cbv
example : mentions foldSourceBindings = [.scalar .bool, .scalar .int] := by cbv

/-- A synthetic runtime function with a floating result, under `main`'s symbol (so reached). -/
def floatRuntime : Codec.FileBindings :=
  match foldSourceBindings.funInfo with
  | (s, l, _) :: _ => { foldSourceBindings with
      stdlib := foldSourceBindings.stdlib ++ [(s, .builtinDecl l (.object .floating) [])] }
  | [] => foldSourceBindings

set_option maxHeartbeats 4000000 in
example : (mentions floatRuntime).contains (.scalar .float) = true := by cbv

set_option maxHeartbeats 4000000 in
example : ¬ linuxX86_64.AppliesTo floatRuntime := by
  unfold Profile.AppliesTo; rw [show ((mentions floatRuntime).all linuxX86_64.coherentAt) = false by cbv]
  decide

/-- An unreachable runtime function is not scanned: it cannot run. -/
def unreachableFloatRuntime : Codec.FileBindings :=
  { foldSourceBindings with
      stdlib := foldSourceBindings.stdlib ++ [(⟨⟨[]⟩, 999999, .none⟩, .builtinDecl .unknown (.object .floating) [])] }

example : mentions unreachableFloatRuntime = [.scalar .bool, .scalar .int] := by cbv
