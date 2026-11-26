module

public import Silmaril.Formats.Hive.ParquetScan.Defs

/-!
# Declared Hive file manifests

Prepare an ordered list of relative file declarations at one physical schema.
Path normalization describes the logical partition directory. The opener
receives the original declaration, including the filename's literal spelling.
Scan calls the pure opener only as it reaches each file. Rejection by a
partition predicate suppresses rows and retains the file's terminal outcome.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

inductive PathError where
  | missingFilename
  | invalidSegment
  | invalidCharacter
  deriving BEq, Repr

/-- The leaf is opaque text. The parent is a slash-separated directory,
with no empty, dot or dot-dot components. This is a lexical convention. -/
def splitFile (path : String) : Except PathError (String × String) :=
  if path.contains '\\' || path.contains (Char.ofNat 0) then .error .invalidCharacter
  else
    match (path.splitOn "/").reverse with
    | [] => .error .missingFilename
    | name :: parents =>
      if name.isEmpty then .error .missingFilename
      else if name.contains ':' then .error .invalidCharacter
      else if (name :: parents).any (fun segment => segment.isEmpty || segment == "." || segment == "..")
        then .error .invalidSegment
      else .ok ("/".intercalate parents.reverse, name)

structure FilePath where
  declared : String
  canonicalDirectory : String
  filename : String
  deriving BEq, Repr

structure File (schema : PartitionSchema Kind) (Value : Kind → Type*) where
  path : FilePath
  cells : Scan.Row schema.toScan Value

inductive PrepareError (Failure : Type*) where
  | schema (reason : TypedPartitions.Error Failure)
  | relativePath (path : String) (reason : PathError)
  | partitionPath (path : String) (reason : PartitionPath.Error)
  | binding (path : String) (reason : TypedPartitions.Error Failure)
  deriving BEq, Repr

abbrev DirectoryParser :=
  PartitionPath.Options → String → Except PartitionPath.Error PartitionPath.Partition

abbrev FileParser :=
  PartitionPath.Options → String → String → Except PartitionPath.Error PartitionPath.Partition

/-- Directory profiles ignore the leaf after the shared lexical split. -/
def DirectoryParser.asFileParser (parse : DirectoryParser) : FileParser :=
  fun options directory _ => parse options directory

/-- Split the literal path and bind the selected directory profile with the
shared typed schema. The canonical directory always uses URI rendering. -/
def prepareFileWithFileParser {Failure : Type*} (schema : PartitionSchema Kind)
    (parse : FileParser) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (declared : String) : Except (PrepareError Failure) (File schema Value) :=
  ((splitFile declared).mapError (PrepareError.relativePath declared)).bind fun (directory, filename) =>
    ((parse options directory filename).mapError (PrepareError.partitionPath declared)).bind fun entries =>
      ((PartitionPath.render options entries).mapError (PrepareError.partitionPath declared)).bind
        fun canonicalDirectory =>
          ((TypedPartitions.decode schema convert entries).mapError (PrepareError.binding declared)).map
            fun cells => ⟨⟨declared, canonicalDirectory, filename⟩, cells⟩

def prepareFileWith {Failure : Type*} (schema : PartitionSchema Kind)
    (parse : DirectoryParser) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (declared : String) : Except (PrepareError Failure) (File schema Value) :=
  prepareFileWithFileParser schema parse.asFileParser options convert declared

/-- Prepare one file using the default checked URI directory profile. -/
def prepareFile {Failure : Type*} (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (convert : Convert Value Failure) (declared : String) :
    Except (PrepareError Failure) (File schema Value) :=
  prepareFileWith schema PartitionPath.parse options convert declared

/-- Check the schema even for an empty list, then validate declarations from
left to right. Repeated declarations remain separate occurrences. -/
def prepare {Failure : Type*} (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (convert : Convert Value Failure) (paths : List String) :
    Except (PrepareError Failure) (List (File schema Value)) :=
  match TypedPartitions.checkSchema physical schema with
  | .error reason => .error (.schema reason)
  | .ok () => paths.mapM (prepareFile schema options convert)

/-- Opening supplies a typed source and a pull budget at the declared schema. -/
structure Opened (Group : Type*) (physical : Scan.Schema String Kind)
    (Value : Kind → Type*) (Error : Type*) where
  source : Parquet.Reader.Source Group physical Value Error
  fuel : Nat

abbrev Opener (Group : Type*) (physical : Scan.Schema String Kind)
    (Value : Kind → Type*) (Error : Type*) :=
  String → Except Error (Opened Group physical Value Error)

inductive FileError (Error : Type*) where
  | open (path : String) (reason : Error)
  | source (path : String) (reason : Error)
  deriving DecidableEq, Repr

/-- The dataset has its own declared schema, so a file open failure becomes a
read error of the dataset with a distinct open cause. -/
def scanFile {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) : Events.Trace projection.schema Value (FileError Error) :=
  match opener file.path.declared with
  | .error reason => ⟨[], .readError (.open file.path.declared reason)⟩
  | .ok opened =>
    let trace := ParquetScan.readFile opened.source opened.fuel
    let result := ParquetScan.scanPartition projection predicate ⟨file.cells, [trace]⟩
    let termination := match result.termination with
      | .eos => .eos
      | .closed => .closed
      | .readError reason => .readError (.source file.path.declared reason)
      | .closeError reason => .closeError (.source file.path.declared reason)
    ⟨result.batches, termination⟩

/-- Call the opener on the current file and advance only after its EOF.
This traverses the manifest lazily in file order and returns an observed trace. -/
def scan {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) : Events.Trace projection.schema Value (FileError Error) :=
  ParquetScan.assemble (scanFile opener projection predicate) files

end Silmaril.Formats.Hive.Manifest
