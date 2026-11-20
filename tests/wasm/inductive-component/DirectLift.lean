module

import Silmaril.Wasm.Component.Reference.DirectLift.Thms

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

private def charExport : SimpleExport := ⟨"codepoint", ⟨[], [.char]⟩, 0⟩

example : DirectLift.Reports charExport .trap (.values [.i32 0xD800]) :=
  ⟨[Flat.i32 0xD800], rfl, by decide +kernel⟩

example : DirectLift.Reports charExport .trap (.throw 0) := trivial

example : ¬ DirectLift.Reports charExport (.resolved none) (.values []) := id

#print axioms DirectLift.terminalReadback
