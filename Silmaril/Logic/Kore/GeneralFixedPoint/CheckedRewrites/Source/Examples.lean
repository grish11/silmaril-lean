module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Examples

/-- A tree-sorted identity rewrite with a shared named capture. -/
def treeText : String :=
  "[] module Trees sort Tree{} [] axiom{} " ++
  "\\rewrites{Tree{}}(X:Tree{},X:Tree{}) [] endmodule []"

/-- A different configuration signature, with a cross-sort existential guard. -/
def packetText : String :=
  "[] module Packets sort Packet{} [] sort Label{} [] axiom{} " ++
  "\\rewrites{Packet{}}(\\and{Packet{}}(P:Packet{}," ++
  "\\exists{Packet{}}(L:Label{},\\equals{Label{},Packet{}}(L:Label{},L:Label{})))," ++
  "P:Packet{}) [] endmodule []"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
theorem tree_checked : (checkText "Tree" 16 treeText).isSome = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
theorem packet_checked : (checkText "Packet" 24 packetText).isSome = true := by
  decide +kernel

/-- An empty helper module need not itself declare the configuration sort. -/
def helperText : String :=
  "[] module Helper endmodule [] module Configs sort Config{} [] endmodule []"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
theorem helper_accepted : (checkText "Config" 8 helperText).isSome = true := by
  decide +kernel

/-- Definition-level configuration declaration is required even without rules. -/
theorem empty_missing_configuration_rejects :
    (checkText "Missing" 4 "[] module Empty endmodule []").isSome = false := by
  decide +kernel

/-- A concrete cfg sort must retain its `{}` braces in predicate result position. -/
def malformedResult : String :=
  "[] module Bad sort Cfg{} [] axiom{} " ++
  "\\rewrites{Cfg{}}(\\and{Cfg{}}(X:Cfg{},\\equals{Cfg{},Cfg}(X:Cfg{},X:Cfg{}))," ++
  "X:Cfg{}) [] endmodule []"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
theorem malformed_result_rejects : (checkText "Cfg" 16 malformedResult).isSome = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
theorem trailing_input_rejects :
    (checkText "Tree" 16 (treeText ++ " garbage")).isSome = false := by
  decide +kernel

/-- Inspect the actual installed axioms of the last accepted source module. -/
def installedOrigins (cfg : String) (fuel : Nat) (text : String) :
    Option (List (Kore.Modules.Origin × Bool)) := do
  let p ← checkText cfg fuel text
  let m ← p.definition.modules.getLast?
  return m.axioms.map (fun r => (r.origin, r.isClaim))

def diamondText : String :=
  "[] module Root sort Cfg{} [] axiom{} " ++
  "\\rewrites{Cfg{}}(X:Cfg{},X:Cfg{}) [] endmodule [] " ++
  "module Left import Root [] endmodule [] " ++
  "module Right import Root [] endmodule [] " ++
  "module Join import Left [] import Right [] endmodule []"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
/-- Import-path occurrences are repeated, with the SAME original declaration
index and axiom kind on both paths through the diamond. -/
theorem diamond_original_occurrences : installedOrigins "Cfg" 16 diamondText =
    some [(⟨"Root", 1⟩, false), (⟨"Root", 1⟩, false)] := by
  decide +kernel

def claimOnlyText : String :=
  "[] module Claims sort Cfg{} [] claim{} " ++
  "\\rewrites{Cfg{}}(X:Cfg{},X:Cfg{}) [] endmodule [] " ++
  "module Client import Claims [] endmodule []"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
/-- Successful parsed claims never become imported transitions. -/
theorem imported_claims_not_installed : installedOrigins "Cfg" 16 claimOnlyText = some [] := by
  decide +kernel

def hiddenSymbolText : String :=
  "[] module Sorts sort Cfg{} [] endmodule [] " ++
  "module Symbols import Sorts [] symbol c{}():Cfg{} [] endmodule [] " ++
  "module Client import Sorts [] axiom{} " ++
  "\\rewrites{Cfg{}}(c{}(),c{}()) [] endmodule []"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
/-- An ambient symbol does not become visible merely because its sort is imported. -/
theorem hidden_symbol_rejects : (checkText "Cfg" 16 hiddenSymbolText).isSome = false := by
  decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Examples
