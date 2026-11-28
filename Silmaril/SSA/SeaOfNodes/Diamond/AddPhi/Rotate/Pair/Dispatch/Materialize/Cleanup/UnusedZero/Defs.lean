module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Defs

/-! Delete the now-unused leading zero in the emitted post-join suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero

open Pure.SubZero (word wordPort)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- Nominate the leading producer only if it is an actual zero literal.
The deletion checker separately checks all its possible users. -/
def leadingZero? : (p : Suffix) → Option (GVN.Producer p.dataflow word)
  | ⟨.cons (.literal value) .nil _, _⟩ => if value = 0 then some .here else none
  | _ => none

/-- Pass the original result wire as the complete outgoing packet. -/
def suffixEdit? (p : Suffix) :
    Option (Pure.Deletion.Result Pure.SubZero.Opcode (dataPorts [word, word]) [wordPort] [] p.sigs) := do
  let candidate ← leadingZero? p
  Pure.Deletion.delete? candidate (.cons p.result .nil)

/-- Rebuild only the post-join suffix from the checked deletion. -/
def rewrite? (p : Program inputs sigs [word]) : Option (Program inputs sigs [word]) :=
  (suffixEdit? p.suffix).map fun edit =>
    { p with suffix := { sigs := edit.erasure.sigs', dataflow := edit.erasure.flow, result := edit.outputs.get .head } }

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero
