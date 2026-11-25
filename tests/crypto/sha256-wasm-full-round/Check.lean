module

import Silmaril.Wasm.Examples.Sha256FullRound.Thms
meta import Silmaril.Wasm.Examples.Sha256FullRound.Defs
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Silmaril.Wasm.Examples.Sha256FullRound
open Lean Elab Command

private def abcRound0 : Input :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19, 0x428a2f98, 0x61626380⟩

example : outputWords abcRound0 0xa54ff53a =
    #v[0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0x3c6ef372,
       0xfa2a4622, 0x510e527f, 0x9b05688c, 0x1f83d9ab] := by decide +kernel

run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for decl in [``decode_fixture, ``run_e, ``round_output, ``call_round] do
    let axioms ← collectAxioms decl
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{decl} transitively uses {axiomName}"
    logInfo m!"{decl} transitive axioms {axioms.toList}"

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the rebuilt Wasm path")
  let rebuilt ← IO.FS.readBinFile path
  if rebuilt.data != fixture.data then
    throw (IO.userError "rebuilt Wasm differs from the Lean fixture")
  IO.println s!"Rebuilt Wasm matches all {rebuilt.size} pinned octets"
