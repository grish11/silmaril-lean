module

import Silmaril.Formats.Json.Fast.Parser.Thms

open Silmaril.Formats
open Silmaril.Formats.Json.Fast.Parser

example :
    let pos : Pos := ⟨0, (r#""\ud83d\ude00\u0000\n""# ++ ",null").toList⟩
    let stop : Pos := ⟨22, ",null".toList⟩
    JsonWire.Internal.tokensOf pos.rest = (JsonWire.Internal.tokensOf stop.rest).map
      (.string (JsonWire.stringUnits (String.ofList ['😀', Char.ofNat 0, '\n'])) :: ·) :=
  quoted_tokens (size := 27) rfl

#print axioms quoted_tokens
#print axioms numberLoop_sound
#print axioms more_sound
#print axioms series_sound
#print axioms Json.Fast.Value.toWire?_ofObject
