module

public import Silmaril.Formats.Hive.Manifest.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem prepareFileWith_declared {Failure : Type*} (parse : DirectoryParser) (options : Silmaril.Formats.Hive.PartitionPath.Options)
    (convert : Convert Value Failure) {declared : String} {file : File schema Value}
    (prepared : prepareFileWith schema parse options convert declared = .ok file) :
    file.path.declared = declared := by
  simp only [prepareFileWith, Except.bind, Except.map] at prepared
  split at prepared
  · cases prepared
  · split at prepared
    · cases prepared
    · split at prepared
      · cases prepared
      · split at prepared
        · cases prepared
        · cases prepared
          rfl

theorem prepare_preserves_paths {Failure : Type*} (options : Silmaril.Formats.Hive.PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (prepared : prepare physical schema options convert paths = .ok files) :
    files.map (fun file => file.path.declared) = paths := by
  unfold prepare at prepared
  split at prepared
  · cases prepared
  · induction paths generalizing files with
    | nil =>
      change Except.ok [] = Except.ok files at prepared
      cases prepared
      rfl
    | cons path rest ih =>
      rw [List.mapM_cons] at prepared
      simp only [bind, Except.bind, pure, Except.pure] at prepared
      split at prepared
      · cases prepared
      · rename_i file parsed
        split at prepared
        · cases prepared
        · rename_i tail more
          cases prepared
          simp [prepareFileWith_declared _ options convert parsed, ih more]

theorem scan_first_terminal {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (before : List (File schema Value)) (current : File schema Value) (after : List (File schema Value))
    (exhausted : ∀ file ∈ before, (scanFile opener projection predicate file).termination = .eos)
    (stop : (scanFile opener projection predicate current).termination ≠ .eos) :
    let run := scan opener projection predicate (before ++ current :: after)
    let last := scanFile opener projection predicate current
    run.rows = before.flatMap (fun file => (scanFile opener projection predicate file).rows) ++ last.rows ∧
      run.termination = last.termination := by
  induction before with
  | nil =>
    simp only [List.nil_append, List.flatMap_nil]
    have stopped := Silmaril.Formats.Hive.ParquetScan.assemble_stops
      (scanFile opener projection predicate) current after stop
    rw [scan, stopped]
    exact ⟨rfl, rfl⟩
  | cons file rest ih =>
    have headEof := Silmaril.Formats.Hive.ParquetScan.assemble_eof
      (scanFile opener projection predicate) file (rest ++ current :: after)
      (exhausted file (List.mem_cons_self ..))
    have tail := ih (fun entry member => exhausted entry (List.mem_cons_of_mem _ member))
    simp only [List.cons_append, List.flatMap_cons, scan] at tail ⊢
    exact ⟨by rw [headEof.1, tail.1, List.append_assoc], headEof.2.trans tail.2⟩

end Silmaril.Proofs.Formats.Hive.Manifest
