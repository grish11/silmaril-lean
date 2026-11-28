module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Defs
import Silmaril.Elf.Staged.Reader.Thms
import Silmaril.Elf.Link.Dyn.Elf.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding

open Silmaril.Elf
open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Corpus.SqliteMutex.Unlock
open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word)
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F
local notation "Glibc" => Silmaril.Elf.Staged.Pinned.GlibcLibc.F

private def readDefinition : Rd (Option DynElf.Elf.Def) := do
  let info ← Elf.dynInfo
  Elf.lookupDef info unlockRef true

private theorem sqlite_no_definition : readDefinition.run (blobRead Sqlite) = some none := by
  open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So in
  exact (partIs_of_kbytes K.wf_true K.toByteArray_eq
    (ws := [⟨0, 568⟩, ⟨1109464, 464⟩, ⟨608, 2440⟩, ⟨3048, 8304⟩,
      ⟨11352, 6523⟩, ⟨17876, 692⟩])
    (p := readDefinition) (v := none) (by decide +kernel)).run

private theorem glibc_definition :
    readDefinition.run (blobRead Glibc) = some (some glibcDefinition) := by
  open Silmaril.Elf.Staged.Pinned.GlibcLibc in
  exact (partIs_of_kbytes K.wf_true K.toByteArray_eq
    (ws := [⟨0, 848⟩, ⟨0x202940, 0x240⟩, ⟨0x4508, 0x50d4⟩, ⟨0x95e0, 0x127e0⟩,
      ⟨0x1bdc0, 0x8870⟩, ⟨0x24630, 0x18a8⟩, ⟨0x25ed8, 0x5ac⟩])
    (p := readDefinition) (v := some glibcDefinition) (by decide +kernel)).run

private theorem read_to_resolver {file : Silmaril.X86.Link.Blob} {found : Option DynElf.Elf.Def}
    (h : readDefinition.run (blobRead file) = some found) :
    ∃ d, Dyn.finfo file = some d ∧ Dyn.frun file (Elf.lookupDef d unlockRef true) = some found := by
  change (Rd.bind Elf.dynInfo (fun info => Elf.lookupDef info unlockRef true)).run
    (blobRead file) = some found at h
  rw [Rd.run_bind] at h
  exact Option.bind_eq_some_iff.mp h

theorem resolve_unlock (tail : List Silmaril.X86.Link.Blob) :
    Dyn.resolve (scope tail) unlockRef true =
      some (some (1, glibcDefinition)) := by
  obtain ⟨sqliteInfo, sqliteHeader, sqliteNoDef⟩ := read_to_resolver sqlite_no_definition
  obtain ⟨glibcInfo, glibcHeader, glibcDef⟩ := read_to_resolver glibc_definition
  simp [scope, Dyn.resolve, Dyn.resolveFrom, sqliteHeader, sqliteNoDef, glibcHeader, glibcDef]

private def readReference : Rd DynElf.Elf.Ref := do
  let info ← Elf.dynInfo
  Elf.refOf info jumpSlot.sym

private theorem sqlite_reference :
    readReference.run (blobRead Sqlite) = some unlockRef := by
  open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So in
  exact (partIs_of_kbytes K.wf_true K.toByteArray_eq
    (ws := [⟨0, 568⟩, ⟨1109464, 464⟩, ⟨4032, 24⟩,
      ⟨11352, 6523⟩, ⟨17876, 692⟩, ⟨18568, 96⟩])
    (p := readReference) (v := unlockRef) (by decide +kernel)).run

private theorem relocates
    (file : Silmaril.X86.Link.Blob) (info : Elf.DynInfo) (resolver : Dyn.Resolver)
    (name : Dyn.frun file (Elf.refOf info jumpSlot.sym) = some unlockRef)
    (chosen : resolver unlockRef true = some (some (1, glibcDefinition))) :
    Dyn.relocVal resolver file info jumpSlot = some (.addr 1 0xa1b50) := by
  change (Dyn.frun file (Elf.refOf info jumpSlot.sym)).bind
    (fun ref => Dyn.bindVal resolver ref true) = _
  rw [name]
  change Dyn.bindVal resolver unlockRef true = _
  change (resolver unlockRef true).bind
    (fun found => match found with
      | some definition => some (Dyn.defVal definition)
      | none => if unlockRef.weak then some (.abs 0) else none) = _
  rw [chosen]
  rfl

theorem eager_slot_value (tail : List Silmaril.X86.Link.Blob) :
    ∃ d, Dyn.finfo Sqlite = some d ∧
      Dyn.relocVal (Dyn.resolve (scope tail)) Sqlite d jumpSlot =
        some (.addr 1 0xa1b50) := by
  have reference := sqlite_reference
  change (Rd.bind Elf.dynInfo (fun info => Elf.refOf info jumpSlot.sym)).run
    (blobRead Sqlite) = some unlockRef at reference
  rw [Rd.run_bind] at reference
  have sourced : (Dyn.finfo Sqlite).bind (fun info => Dyn.frun Sqlite (Elf.refOf info jumpSlot.sym)) =
      some unlockRef := reference
  obtain ⟨d, info, name⟩ := Option.bind_eq_some_iff.mp sourced
  exact ⟨d, info, relocates Sqlite d _ name (resolve_unlock tail)⟩

theorem absolute_relocation :
    readAbsoluteReloc.run
      (blobRead Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F) = some absoluteReloc := by
  open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So in
  exact (partIs_of_kbytes K.wf_true K.toByteArray_eq
    (ws := [⟨0, 568⟩, ⟨1109464, 464⟩, ⟨46744, 24⟩])
    (p := readAbsoluteReloc) (v := absoluteReloc) (by decide +kernel)).run

theorem unlock_word (tail : List Blob) (sqliteBase glibcBase : Word) (otherBases : List Word)
    (ifunc : Word → Option Word) (resolver : Word) :
    ∃ d, Dyn.finfo Sqlite = some d ∧
      (Dyn.relocVal (Dyn.resolve (scope tail)) Sqlite d jumpSlot).bind
        (Dyn.Val.word (sqliteBase :: glibcBase :: otherBases) ifunc resolver) =
          some (some (glibcBase + 0xa1b50#64)) := by
  obtain ⟨d, info, value⟩ := eager_slot_value tail
  refine ⟨d, info, ?_⟩
  rw [value]
  rfl

end Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding
