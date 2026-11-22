module

public import Silmaril.Formats.Dasl.Prolly.Set.Defs
public import Silmaril.Logic.HOLLight.SExp.Thms

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.HOL

open Silmaril.Formats.Dasl
open Silmaril.Logic.HOLLight

/-- Use canonical HOL term bytes as unsigned bytewise lexicographic Prolly keys.
These are labels for assumption terms, not object addresses. -/
def hypothesisKey : Encode.TotalCodec Tm Prolly.ByteKey where
  encode term := (SExp.printTm term).map UInt8.toFin
  decode? key := SExp.parseTm (key.map UInt8.ofFin)
  recovers term := by simpa [List.map_map, Function.comp_def] using SExp.parseTm_printTm term

end Silmaril.ProofFormats.DaslSyntax.HOL
