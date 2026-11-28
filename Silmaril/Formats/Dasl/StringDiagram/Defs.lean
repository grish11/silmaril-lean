module

@[expose] public section

namespace Silmaril.Formats.Dasl.StringDiagram

structure Box (Label : Type) where
  inputs : Int64
  outputs : Int64
  label : Label

/-- The raw positional object. Box sources are indexed by destination input slot,
in box-major order. Both source tables use the same producer ordinals. -/
structure Diagram (Label : Type) where
  inputs : Int64
  exports : Int64
  boxes : List (Box Label)
  boxSources : List Int64
  exportSources : List Int64

variable {Label : Type}

def Diagram.inputWidths (d : Diagram Label) : List Nat :=
  d.boxes.map fun box => box.inputs.toInt.toNat

def Diagram.sourceCount (d : Diagram Label) : Nat :=
  d.inputs.toInt.toNat + (d.boxes.map fun box => box.outputs.toInt.toNat).sum

/-- Arithmetic is done in Nat before applying the structural signed-I64 bounds. -/
def maxCount : Nat := 2 ^ 63 - 1

/-- Structural validity only. A source can have any number of uses, and forward and
cyclic references are allowed. A label is opaque to these checks. -/
def Diagram.wellFormed (d : Diagram Label) : Bool :=
  let slots := d.inputWidths.sum
  let sources := d.sourceCount
  let sourceOK (s : Int64) := decide (0 ≤ s.toInt ∧ s.toInt < (sources : Int))
  decide (0 ≤ d.inputs.toInt ∧ 0 ≤ d.exports.toInt ∧
    d.boxes.length ≤ maxCount ∧ slots ≤ maxCount ∧ sources ≤ maxCount ∧
    d.boxSources.length = slots ∧ d.exportSources.length = d.exports.toInt.toNat) &&
    d.boxes.all (fun box => decide (0 ≤ box.inputs.toInt ∧ 0 ≤ box.outputs.toInt)) &&
    d.boxSources.all sourceOK && d.exportSources.all sourceOK

abbrev Checked (Label : Type) := { d : Diagram Label // d.wellFormed = true }

def check? (d : Diagram Label) : Option (Checked Label) :=
  if valid : d.wellFormed = true then some ⟨d, valid⟩ else none

/-- Split the flat destination table using the widths, including empty groups.
The final check rules out a surplus suffix. -/
def splitInputs? {α : Type} : List Nat → List α → Option (List (List α))
  | [], entries => if entries.isEmpty then some [] else none
  | width :: widths, entries => do
    let (group, rest) := entries.splitAt width
    if group.length = width then
      return group :: (← splitInputs? widths rest)
    else
      none

end Silmaril.Formats.Dasl.StringDiagram
