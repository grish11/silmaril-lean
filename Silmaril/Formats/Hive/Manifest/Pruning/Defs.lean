module

public import Silmaril.Formats.Hive.Manifest.Defs

/-!
# Skip-open pruning of declared Hive manifests

The reference scan is `Manifest.scan`: it observes every reached file's
outcome. This opt-in scan skips files whose partition predicate is false
or unknown. Its observation can differ if a rejected file fails or closes
before EOF.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind Group Error : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

def scanFileSkippingRejected (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (file : File schema Value) :
    Events.Trace projection.schema Value (FileError Error) :=
  if (predicate file.cells).getD false then
    scanFile opener projection (fun _ => some true) file
  else
    ⟨[], .eos⟩

/-- Evaluate the predicate once per reached declaration. Skip opening rejected
files, and keep the original order and multiplicity of retained declarations. -/
def scanSkippingRejected (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (files : List (File schema Value)) :
    Events.Trace projection.schema Value (FileError Error) :=
  ParquetScan.assemble (scanFileSkippingRejected opener projection predicate) files

/-- Every rejected occurrence would open and reach EOF under the reference
scan with the opener's actual pull budget. Retained files may fail. -/
def RejectedFilesReachEOF (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (files : List (File schema Value)) : Prop :=
  ∀ file ∈ files, (predicate file.cells).getD false = false →
    (scanFile opener projection predicate file).termination = .eos

/-- A declaration is reached when the strict scan of its preceding
occurrences reaches EOF. Require rejected files to reach EOF only at these
positions, using the reference opener's actual pull budget. -/
def ReachedRejectedFilesReachEOF (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (files : List (File schema Value)) : Prop :=
  ∀ before file after, files = before ++ file :: after →
    (scan opener projection predicate before).termination = .eos →
    (predicate file.cells).getD false = false →
    (scanFile opener projection predicate file).termination = .eos

end Silmaril.Formats.Hive.Manifest
