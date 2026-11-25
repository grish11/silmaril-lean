module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Defs
public import Silmaril.Wasm.Institution.Operational.Division.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (AdminInstr Value)

variable {I : Type}

def liftValue (v : Value) : Core.Val := .num ⟨v.type, v.bits⟩

/-- The flat projection retains source instructions and traps. A code can be
read back using the version's public partial inverse on source instructions. -/
def emitAdmin (emit : I → Instr) : AdminInstr I → Option Core.Admin
  | .source i => some (.plain (emit i))
  | .trap => some .trap
  | _ => none

def readAdmin (read : Instr → Option I) : Core.Admin → Option (AdminInstr I)
  | .plain i => (read i).map .source
  | .trap => some .trap
  | _ => none

def emitCode (emit : I → Instr) (code : List (AdminInstr I)) : List Core.Admin :=
  code.filterMap (emitAdmin emit)

def readCode (read : Instr → Option I) (code : List Core.Admin) : Option (List (AdminInstr I)) :=
  code.mapM (readAdmin read)

structure CoreEncoding (S : Syntax I) where
  emit : I → Instr
  read : Instr → Option I
  read_emit : ∀ i, read (emit i) = some i
  value : ∀ v, emitAdmin emit (S.value v) = some (liftValue v).toAdmin
  divide : ∀ t sign, emitAdmin emit (S.divide t sign) = some (Division.divOp t sign)
  nop : emitAdmin emit S.nop = some (.plain .nop)

end Silmaril.Wasm.Institution.Operational.LegacyDivision
