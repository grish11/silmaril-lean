module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
public import Silmaril.Formats.Hive.Manifest.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress (CastError parseDecimal convert layout firstRequiredNull
  preparePath preparePaths)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

variable {schema : PartitionSchema Kind} {options : PartitionPath.Options}

theorem convert_int32_ok_iff (name : String) (nullability : FlatColumn.Layout)
    (missing : TypedPartitions.Missing) (text : String) (value : Int32) :
    convert ⟨name, .int32 nullability, missing⟩ text = .ok value ↔ parseDecimal text = some value.toInt := by
  cases parsed : parseDecimal text with
  | none => simp [convert, parsed]
  | some number =>
    by_cases bounds : Int32.minValue.toInt ≤ number ∧ number ≤ Int32.maxValue.toInt
    · simp only [convert, parsed, dite_eq_left bounds, Except.ok.injEq, Option.some.injEq]
      constructor
      · rintro rfl
        exact Int32.toInt_ofIntLE.symm
      · intro equal
        exact Int32.toInt.inj (Int32.toInt_ofIntLE.trans equal)
    · simp only [convert, parsed, dite_eq_right bounds, reduceCtorEq, Option.some.injEq, false_iff]
      rintro rfl
      exact bounds ⟨value.minValue_le_toInt, value.toInt_le⟩

theorem preparePath_ok_iff {path : String} {file : File schema Value} :
    preparePath schema options path = .ok file ↔
      Manifest.prepareFile schema options convert path = .ok file ∧
        ∀ i, layout (schema.toScan.kind i).2 = .required → (file.cells i).isSome = true := by
  have admits (result : File schema Value) :
      firstRequiredNull result = none ↔
        ∀ i, layout (schema.toScan.kind i).2 = .required → (result.cells i).isSome = true := by
    simp [firstRequiredNull, List.find?_eq_none, Bool.and_eq_true, not_and, Option.isSome_iff_ne_none]
  cases checked : Manifest.prepareFile schema options convert path with
  | error reason => simp [preparePath, checked]
  | ok result =>
    simp only [preparePath, checked, Except.ok.injEq]
    cases failed : firstRequiredNull result with
    | none =>
      have admitted := (admits result).mp failed
      simp only [Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, admitted⟩
      · exact And.left
    | some index =>
      constructor
      · intro impossible
        contradiction
      · rintro ⟨rfl, admitted⟩
        rw [← admits, failed] at admitted
        contradiction

private theorem mapM_cons_ok_iff {α β ε : Type} (f : α → Except ε β)
    (head : α) (tail : List α) (items : List β) :
    (head :: tail).mapM f = .ok items ↔
      ∃ first rest, items = first :: rest ∧ f head = .ok first ∧ tail.mapM f = .ok rest := by
  cases first : f head <;> cases rest : tail.mapM f <;>
    simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, eq_comm]

private theorem mapM_ok_iff {paths : List String} {files : List (File schema Value)} :
    paths.mapM (preparePath schema options) = .ok files ↔
      paths.mapM (Manifest.prepareFile schema options convert) = .ok files ∧
        ∀ file ∈ files, ∀ i, layout (schema.toScan.kind i).2 = .required →
          (file.cells i).isSome = true := by
  induction paths generalizing files with
  | nil =>
    constructor
    · intro equal
      cases equal
      exact ⟨rfl, by simp⟩
    · intro h
      cases h.1
      rfl
  | cons path rest ih =>
    rw [mapM_cons_ok_iff, mapM_cons_ok_iff]
    constructor
    · rintro ⟨first, remaining, rfl, hFirst, hTail⟩
      obtain ⟨sharedFirst, admittedFirst⟩ := preparePath_ok_iff.mp hFirst
      obtain ⟨sharedTail, admittedTail⟩ := ih.mp hTail
      refine ⟨⟨first, remaining, rfl, sharedFirst, sharedTail⟩, ?_⟩
      intro file mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact admittedFirst
      · exact admittedTail file mem
    · rintro ⟨⟨first, remaining, rfl, hFirst, hTail⟩, admitted⟩
      exact ⟨first, remaining, rfl, preparePath_ok_iff.mpr ⟨hFirst, admitted first (by simp)⟩,
        ih.mpr ⟨hTail, fun file mem => admitted file (List.mem_cons_of_mem _ mem)⟩⟩

theorem preparePaths_ok_iff (int32 byteArray : Field)
    {paths : List String} {files : List (File schema Value)} :
    preparePaths int32 byteArray schema options paths = .ok files ↔
      Manifest.prepare (Int32ByteArrayGroup.File.schema int32 byteArray) schema options convert paths =
        .ok files ∧
      ∀ file ∈ files, ∀ i, layout (schema.toScan.kind i).2 = .required → (file.cells i).isSome = true := by
  cases admission : TypedPartitions.checkSchema (Failure := CastError)
      (Int32ByteArrayGroup.File.schema int32 byteArray) schema with
  | error reason => simp [preparePaths, Manifest.prepare, admission]
  | ok accepted =>
    simp only [preparePaths, Manifest.prepare, admission]
    exact mapM_ok_iff

end Silmaril.Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress
