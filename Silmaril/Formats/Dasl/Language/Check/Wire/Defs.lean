module

public import Silmaril.Formats.Dasl.Language.Check.Defs
public import Silmaril.Formats.Dasl.Wire.Defs

public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Semantics.Naming

def readBlob (read : Cid → Option ByteArray) (name : Cid) : ReadResult ByteArray :=
  if name.val[1]? == some 0x55 then
    match read name with
    | some bytes => .found bytes
    | none => .missing
  else .invalidWire

/-- Only successful decodes are bindings. The query API retains the failure
status separately, so a malformed fixed wire binding cannot appear as missing. -/
@[expose] def queryStore (read : Cid → Option ByteArray) : Store Cid :=
  ⟨fun name value => readObject read name = .found value,
    fun name value => readBlob read name = .found value⟩

private def certifyRead {Payload : Type} {rel : Payload → Prop} (answer : ReadResult Payload)
    (sound : ∀ payload, answer = .found payload → rel payload) : Except ReadFailure {payload // rel payload} :=
  match answer with
  | .found payload => .ok ⟨payload, sound payload rfl⟩
  | .missing => .error .missing
  | .invalidWire => .error .invalid

/-- Reuse the canonical reader. `sound` connects successful reads to a reference
relation; neither this adapter nor the checker authenticates payloads by hashing. -/
def queries (read : Cid → Option ByteArray) {reference : Store Cid}
    (sound : (queryStore read).Subset reference) : Queries reference where
  readObject name := certifyRead (readObject read name) (fun _ found => sound.1 found)
  readBlob name := certifyRead (readBlob read name) (fun _ found => sound.2 found)

end Silmaril.Formats.Dasl.Wire
