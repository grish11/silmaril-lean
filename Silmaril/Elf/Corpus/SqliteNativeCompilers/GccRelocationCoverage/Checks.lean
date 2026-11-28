module

import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.Thms

open Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage (pinned_absolute_slot)
open Silmaril.Elf.Link.Dyn (Resolver Val finfo frun relocVal resolve)
open Silmaril.Elf.Link.DynElf.Elf (Def DynInfo Rela relas)
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.X86 (Byte Word)
open Silmaril.X86.Link (Blob)

private def referenceFile (binding : Byte) : Blob :=
  -- Null symbol, symbol 1 with name offset 1, then the string table "\0x\0".
  let bytes := List.replicate 24 0 ++ [1, 0, 0, 0, binding, 0, 0, 0] ++
    List.replicate 16 0 ++ [0, 0x78, 0]
  ⟨Blob.valueLE bytes, bytes.length⟩

private def info : DynInfo := ⟨[⟨1, 4, 0, 0, 51, 51⟩], [(6, 0), (5, 48)]⟩

private def lookup (defn : Def) : Resolver := fun ref plt =>
  if ref.name = [0x78] ∧ plt = false then some (some (1, defn)) else none

private def slotWord (resolver : Resolver) (binding : Byte) (addend : Int)
    (ifunc : Word → Option Word := fun _ => none) : Option (Option Word) :=
  (relocVal resolver (referenceFile binding) info ⟨0, 1, 1, addend⟩).bind
    (Val.word [0x1000, 0x2000] ifunc 0)

-- Signed addend with a definition in the second object, and wraparound for SHN_ABS.
example : slotWord (lookup ⟨0x20, false, false⟩) 0x12 (-4) = some (some 0x201c) := by decide +kernel
example : slotWord (lookup ⟨0xffffffffffffffff, false, true⟩) 0x12 1 = some (some 0) := by decide +kernel

-- Search miss for a weak reference, a strong reference, and a reader failure.
example : slotWord (fun _ _ => some none) 0x22 (-1) = some (some 0xffffffffffffffff) := by decide +kernel
example : slotWord (fun _ _ => some none) 0x12 (-1) = none := by decide +kernel
example : slotWord (fun _ _ => none) 0x22 (-1) = none := by decide +kernel

-- Apply the addend to the result of the IFUNC, after calling its unadjusted address.
example : slotWord (lookup ⟨0x20, true, false⟩) 0x12 4
    (fun address => if address = 0x2020 then some 0x3000 else none) = some (some 0x3004) := by
  decide +kernel
example : slotWord (lookup ⟨0x20, true, false⟩) 0x12 4 = none := by decide +kernel

example :
    let row : Rela := ⟨0x10e520, 1, 195, 0⟩
    ∃ dynamic main plt, finfo F = some dynamic ∧ frun F (relas dynamic) = some (main, plt) ∧
      row ∈ main ∧ (relocVal (resolve [F]) F dynamic row).bind
        (Val.word [0x00007f2300000000] (fun _ => none) 0) = some (some 0x00007f23000374e0) := by
  obtain ⟨dynamic, main, plt, hi, ht, hr, hw⟩ := pinned_absolute_slot
  exact ⟨dynamic, main, plt, hi, ht, hr, by rw [hw]; decide +kernel⟩
