module

public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Formats.JsonWire.Concrete.Thms
public import Silmaril.Formats.JsonBytes.Defs
import Silmaril.Proofs.Formats.JsonWire.Parse
import Silmaril.Proofs.Formats.JsonWire.Rfc8259

/-! # JSON on the wire: lemmas

* `parse?_isSome_iff`, `parse?_isSome_iff_isJson`: **the RFC 8259 reader accepts exactly the JSON
  texts** of `Silmaril.Formats.JsonBytes.language .rfc8259`, the RFC's ABNF transcribed over
  UTF-8 bytes. The proof goes through the declarative grammar of the reader's stages
  (`Silmaril.Formats.JsonWire.Grammar.Thms`): UTF-8 decoding, the lexer, the parser;
* `parseCst?_sound`: a lossless CST the reader returns has the input as its source and is the
  reader's parse of it (`IsCst`);
* the concrete-syntax lemmas of `Silmaril.Formats.JsonWire.Concrete.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonWire

theorem parseCst?_sound {dialect : Dialect} {bytes : Bytes} {cst : Cst}
    (h : parseCst? dialect bytes = some cst) : cst.source = bytes ∧ IsCst dialect cst :=
  Silmaril.Proofs.Formats.JsonWire.Parse.parseCst?_sound h

/-- **The RFC 8259 reader accepts exactly the JSON texts**: `parse?` succeeds on the bytes `w`
iff `w` is a JSON text (`Silmaril.Formats.JsonBytes.language .rfc8259`: RFC 8259's grammar over
UTF-8 bytes, any `\uXXXX` escape). -/
theorem parse?_isSome_iff (w : List UInt8) :
    (parse? (Bytes.ofList w)).isSome ↔ w ∈ JsonBytes.language .rfc8259 :=
  Silmaril.Proofs.Formats.JsonWire.Rfc8259.parse?_isSome_iff w

/-- The same, for `Bytes`. -/
theorem parse?_isSome_iff_isJson (b : Bytes) : (parse? b).isSome ↔ b.IsJson .rfc8259 := by
  have := parse?_isSome_iff b.toList
  rw [Bytes.ofList_toList] at this
  exact this

end Silmaril.Formats.JsonWire

end
