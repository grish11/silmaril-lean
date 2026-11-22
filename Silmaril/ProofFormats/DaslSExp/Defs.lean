module

public import Silmaril.Formats.Dasl.SExp.Defs
public import Silmaril.Logic.Concrete.Codec.Defs

/-! Adapter for the `SE` carrier of existing HOL/MLTT (and other) concrete codecs.
It preserves syntax, not the bytes of a different DASL profile. -/

@[expose] public section

namespace Silmaril.ProofFormats.DaslSExp

open Silmaril.Formats (SExp)
open Silmaril.Logic.Smt (SE)

mutual
def ofLogic : SE → SExp String
  | .atom text => .atom text
  | .list items => SExp.ofList (ofLogicItems items)

def ofLogicItems : List SE → List (SExp String)
  | [] => []
  | head :: rest => ofLogic head :: ofLogicItems rest
end

def toLogic : SExp String → SE
  | .atom text => .atom text
  | .list _ items => .list (List.ofFn fun index => toLogic (items index))

end Silmaril.ProofFormats.DaslSExp
