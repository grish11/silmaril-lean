module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.CaptureExamples
open Silmaril.Logic.Kore.GeneralFixedPoint
open Predicates
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000

/-- Two genuinely different declared sorts. L occurs only in the guard; X
occurs in both endpoints. The complete parsed claim retains both captures. -/
def text : String :=
  "[] module Captures sort Cfg{} [] sort Label{} [] claim{} " ++
  "\\rewrites{Cfg{}}(\\and{Cfg{}}(X:Cfg{}," ++
  "\\equals{Label{},Cfg{}}(L:Label{},L:Label{})),X:Cfg{}) [] endmodule []"

theorem accepted : (checkText "Cfg" 16 text).isSome = true := by decide +kernel

def package : Package "Cfg" 16 text := (checkText "Cfg" 16 text).get accepted

def selection : ClaimSelection package :=
  let owner := package.definition.modules[0]
  ⟨owner, by exact List.mem_cons_self, owner.claims[0], by exact List.mem_cons_self⟩

theorem actual_captures : selection.declaration.payload.checked.objects =
    [("X", "Cfg"), ("L", "Label")] := by decide +kernel

/-- The actual checked guard, not a caller-selected predicate, is true in
any admitted model at every sorted capture assignment. -/
theorem actual_guard
    (M : Matching.GeneralFixedPoint.Model package.definition.ambient.signature)
    (a : Env M selection.declaration.payload.checked.objects) :
    rawPredicateTruth M selection.declaration.payload.checked.fuel
      selection.declaration.payload.checked.objects
      selection.declaration.payload.checked.raw.guard a := by
  change rawValue M 16 [("X", "Cfg"), ("L", "Label")] a "Label" (.evar "L" "Label") =
    rawValue M 16 [("X", "Cfg"), ("L", "Label")] a "Label" (.evar "L" "Label")
  rfl

/-- Reusing one capture name with a second sort is rejected. -/
def incoherentText : String :=
  "[] module Captures sort Cfg{} [] sort Label{} [] claim{} " ++
  "\\rewrites{Cfg{}}(\\and{Cfg{}}(X:Cfg{}," ++
  "\\equals{Label{},Cfg{}}(X:Label{},X:Label{})),X:Cfg{}) [] endmodule []"

theorem incoherent_rejected : (checkText "Cfg" 16 incoherentText).isSome = false := by
  decide +kernel

/-- A claim endpoint at the wrong declared sort is also rejected. -/
def wrongEndpointText : String :=
  "[] module Captures sort Cfg{} [] sort Label{} [] claim{} " ++
  "\\rewrites{Cfg{}}(X:Cfg{},L:Label{}) [] endmodule []"

theorem wrong_endpoint_rejected : (checkText "Cfg" 16 wrongEndpointText).isSome = false := by
  decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.CaptureExamples
