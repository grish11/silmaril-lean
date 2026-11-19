module

public import Silmaril.Elf.Corpus.CjsonTypePredicates.Defs

@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonTypePredicates
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1
theorem null_at : Silmaril.Elf.CodeAt F nullAddress nullCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem null_symbol : s3_61.name = ("cJSON_IsNull".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_61.raw.value = nullAddress ∧ s3_61.raw.size = 19 ∧ s3_61.kind = 2 := by decide +kernel
theorem bool_at : Silmaril.Elf.CodeAt F boolAddress boolCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem bool_symbol : s3_94.name = ("cJSON_IsBool".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_94.raw.value = boolAddress ∧ s3_94.raw.size = 19 ∧ s3_94.kind = 2 := by decide +kernel
theorem number_at : Silmaril.Elf.CodeAt F numberAddress numberCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem number_symbol : s3_30.name = ("cJSON_IsNumber".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_30.raw.value = numberAddress ∧ s3_30.raw.size = 19 ∧ s3_30.kind = 2 := by decide +kernel
theorem string_at : Silmaril.Elf.CodeAt F stringAddress stringCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem string_symbol : s3_55.name = ("cJSON_IsString".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_55.raw.value = stringAddress ∧ s3_55.raw.size = 19 ∧ s3_55.kind = 2 := by decide +kernel
theorem array_at : Silmaril.Elf.CodeAt F arrayAddress arrayCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem array_symbol : s3_64.name = ("cJSON_IsArray".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_64.raw.value = arrayAddress ∧ s3_64.raw.size = 19 ∧ s3_64.kind = 2 := by decide +kernel
theorem object_at : Silmaril.Elf.CodeAt F objectAddress objectCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem object_symbol : s3_36.name = ("cJSON_IsObject".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_36.raw.value = objectAddress ∧ s3_36.raw.size = 19 ∧ s3_36.kind = 2 := by decide +kernel
theorem invalid_at : Silmaril.Elf.CodeAt F invalidAddress invalidCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem invalid_symbol : s3_37.name = ("cJSON_IsInvalid".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_37.raw.value = invalidAddress ∧ s3_37.raw.size = 19 ∧ s3_37.kind = 2 := by decide +kernel
theorem false_at : Silmaril.Elf.CodeAt F falseAddress falseCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem false_symbol : s3_81.name = ("cJSON_IsFalse".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_81.raw.value = falseAddress ∧ s3_81.raw.size = 19 ∧ s3_81.kind = 2 := by decide +kernel
theorem true_at : Silmaril.Elf.CodeAt F trueAddress trueCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem true_symbol : s3_48.name = ("cJSON_IsTrue".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_48.raw.value = trueAddress ∧ s3_48.raw.size = 19 ∧ s3_48.kind = 2 := by decide +kernel
theorem raw_at : Silmaril.Elf.CodeAt F rawAddress rawCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem raw_symbol : s3_88.name = ("cJSON_IsRaw".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_88.raw.value = rawAddress ∧ s3_88.raw.size = 19 ∧ s3_88.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.CjsonTypePredicates
