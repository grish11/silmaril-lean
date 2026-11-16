module

public import Silmaril.Project.Registry.Consequence.Defs
public import Silmaril.Wasi.Component.Consequence.Signed.Matrix.Defs

/-!
# The protocol track's evidence matrix, as registry rows

`signedMatrixRows` reads `Silmaril.Wasi.Consequence.SignedMatrix.cells` (the protocol track's
coverage of its signed and two-sided protocols) as `MatrixRows`, field by field and verbatim:
the variant (its `repr`), the reading, the listed declarations, the evidence (`definitions`,
`specStrategy`, `execution`), the strength (`exact`, `sound`, `boundedComplete`, `laws`) and the
note. The classifications are the protocol owner's; the registry only checks that the listed
declarations exist.
-/

@[expose] public section

namespace Silmaril.Project.ConsequenceSystems.Matrix

open Silmaril.Wasi.Consequence.SignedMatrix

/-- The evidence of a cell, by its constructor name. -/
def evidenceName : Evidence → String
  | .definitions => "definitions"
  | .specStrategy => "specStrategy"
  | .execution => "execution"

/-- The strength of a cell, by its constructor name. -/
def strengthName : Strength → String
  | .exact => "exact"
  | .sound => "sound"
  | .boundedComplete => "boundedComplete"
  | .laws => "laws"

/-- The cells as registry rows. -/
def signedMatrixRows : Silmaril.Project.MatrixRows :=
  cells.map fun c => (reprStr c.variant, c.reading, c.theorems, evidenceName c.evidence,
    strengthName c.strength, c.note)

end Silmaril.Project.ConsequenceSystems.Matrix
