module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Error hashKey)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Guards

theorem rejects (heap : Heap) (table : Table) (key value : Lists.Value) (reason : Rejection)
    (blocked : table.rejection = some reason) :
    Lists.GoDictionary.Guards.set heap table key value = .error (.guard reason) table ∧
    delete heap table key = .error (.guard reason) table := by
  simp [Lists.GoDictionary.Guards.set, delete, blocked]

theorem set_ready (heap : Heap) (table : Table) (key value : Lists.Value) (next : Lists.GoDictionary.Deletion.Table)
    (allowed : table.rejection = none)
    (ran : Lists.GoDictionary.Deletion.set heap table.rows key value = .ok next) :
    Lists.GoDictionary.Guards.set heap table key value = .ok () { table with contents := some next } := by
  have rows : table.initialize.rows = table.rows := rfl
  simp only [Lists.GoDictionary.Guards.set, allowed]
  rw [rows, ran]
  rfl

theorem initialize_allocated (table : Table) (rows : Lists.GoDictionary.Deletion.Table)
    (allocated : table.contents = some rows) : table.initialize = table := by
  cases table
  simp [Table.initialize, Table.rows] at allocated ⊢
  simp [allocated]

theorem set_hash_error (heap : Heap) (table : Table) (key value : Lists.Value) (error : Error)
    (allowed : table.rejection = none) (hashed : hashKey heap key = .error error) :
    Lists.GoDictionary.Guards.set heap table key value = .error (.table error) table.initialize := by
  simp [Lists.GoDictionary.Guards.set, allowed, Lists.GoDictionary.Deletion.set,
    Lists.GoDictionary.Deletion.lookupWithHash, hashed, bind, Except.bind]

theorem delete_unallocated (heap : Heap) (table : Table) (key : Lists.Value)
    (allowed : table.rejection = none) (empty : table.contents = none) :
    delete heap table key = .ok none table := by
  simp [delete, allowed, empty]

theorem delete_hash_error (heap : Heap) (table : Table) (key : Lists.Value)
    (rows : Lists.GoDictionary.Deletion.Table) (error : Error) (allowed : table.rejection = none)
    (allocated : table.contents = some rows) (hashed : hashKey heap key = .error error) :
    delete heap table key = .error (.table error) table := by
  simp [delete, allowed, allocated, Lists.GoDictionary.Deletion.delete,
    Lists.GoDictionary.Deletion.lookupWithHash, hashed, bind, Except.bind]

theorem delete_ready (heap : Heap) (table : Table) (key : Lists.Value)
    (rows next : Lists.GoDictionary.Deletion.Table) (removed : Option Lists.Value)
    (allowed : table.rejection = none) (allocated : table.contents = some rows)
    (ran : Lists.GoDictionary.Deletion.delete heap rows key = .ok (removed, next)) :
    delete heap table key = .ok removed { table with contents := some next } := by
  simp [delete, allowed, allocated, ran]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards
