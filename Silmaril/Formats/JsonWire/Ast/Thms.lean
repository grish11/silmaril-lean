module

public import Silmaril.Formats.JsonWire.Ast.Defs
import Silmaril.Proofs.Formats.JsonWire.Ast

@[expose] public section

namespace Silmaril.Formats.JsonWire

theorem unitsString_stringUnits (text : String) : unitsString? (stringUnits text) = some text :=
  Silmaril.Proofs.Formats.JsonWire.Ast.unitsString_stringUnits text

end Silmaril.Formats.JsonWire
