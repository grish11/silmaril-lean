module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs

/-! Opt-in native schema-only IPC to a mixed Parquet file with zero row groups. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly

open Silmaril.Formats.Relational.NamedTable

inductive Error where
  | source (cause : MixedIpc.Error)
  | batchCount (actual : Nat)
  | sink (cause : Multi.Error)
  deriving DecidableEq, Repr

def plan (descriptor : MixedIpc.Descriptor) : Multi.Input :=
  ⟨field descriptor.integer, field descriptor.binary, []⟩

/-- The canonical footer has the two ordered unannotated leaves, zero total
rows and no row groups. The file has no data pages. -/
def metadata (descriptor : MixedIpc.Descriptor) : Footer.Metadata :=
  Multi.metadataOrdered (physicalOrder descriptor) (plan descriptor) []

/-- Reuse bounded mixed assembly with an empty plan. Certify the parsed
footer, file extent and checked projection before returning the native file. -/
def emit (limits : Multi.Limits) (descriptor : MixedIpc.Descriptor) :
    Except Multi.Error Multi.Encoded := do
  let input := plan descriptor
  let order := physicalOrder descriptor
  let output ← Multi.assembleOrdered order limits input
  if output.CheckedOrdered order limits input then
    (Multi.certify limits input output).map fun _ => output
  else throw .extent

/-- Require exact IPC exhaustion with zero record batches. An explicit
zero-row batch belongs to the regular ordered converter. -/
def convert (source : MixedIpc.Limits) (sink : Multi.Limits) (input : KBytes) :
    Except Error Multi.Encoded := do
  let observed ← (MixedIpc.read source input).mapError .source
  let [] := observed.batches | .error (.batchCount observed.batches.length)
  (emit sink observed.descriptor).mapError .sink

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly
