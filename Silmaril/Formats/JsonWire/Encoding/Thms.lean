module

public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Formats.JsonWire.Grammar.Defs
import Silmaril.Proofs.Formats.JsonWire.Encoding

@[expose] public section

namespace Silmaril.Formats.JsonWire

/-- The RFC token reader recovers the ordered AST and leaves the suffix untouched. -/
theorem value?_printedTokens (tree : Ast Decimal) (fuel : Nat)
    (enough : (Internal.printedTokens tree).length < fuel) (rest : List Internal.Token) :
    Internal.value? .rfc8259 fuel (Internal.printedTokens tree ++ rest) =
      some (tree.mapScalar Internal.addFinite, rest) :=
  Silmaril.Proofs.Formats.JsonWire.Encoding.value?_printedTokens tree fuel enough rest

/-- Reading the printer's actual bytes recovers every ordered RFC JSON tree,
including exact decimal fields, all UTF-16 units, and duplicate names. -/
theorem parse_encode (tree : Ast Decimal) : parse? (encode tree) = some tree :=
  Silmaril.Proofs.Formats.JsonWire.Encoding.parse_encode tree

end Silmaril.Formats.JsonWire
