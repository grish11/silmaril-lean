module

public import Silmaril.Semantics.Naming.Table.Defs

public section

namespace Silmaril.Proofs.Semantics.Naming.Table

open Silmaril.Semantics.Naming
open Silmaril.Semantics.Naming.Table

variable {Name Payload : Type}

theorem lookup_iff {table : Table Payload} {route : List Bool} {payload : Payload} :
    table.lookup route = some payload ↔ Entry table route payload := by
  constructor
  · induction route generalizing table with
    | nil =>
      cases table with
      | empty => simp [lookup]
      | node slot zero one =>
        intro found
        change slot = some payload at found
        subst slot
        exact .here
    | cons bit rest ih =>
      cases table with
      | empty => simp [lookup]
      | node slot zero one =>
        cases bit
        · exact fun found => .zero (ih found)
        · exact fun found => .one (ih found)
  · intro entry
    induction entry with
    | here => rfl
    | zero _ ih => exact ih
    | one _ ih => exact ih

theorem lookup_set (table : Table Payload) (write read : List Bool) (payload : Payload) :
    (table.set write payload).lookup read =
      if read = write then some payload else table.lookup read := by
  induction write generalizing table read with
  | nil =>
    cases table <;> cases read with
    | nil => simp [Table.set, lookup]
    | cons head tail => cases head <;> simp [Table.set, lookup]
  | cons bit rest ih =>
    cases table <;> cases bit <;> cases read with
    | nil => simp [Table.set, lookup]
    | cons head tail => cases head <;> simp [Table.set, lookup, ih]

theorem overlay_iff {left right : Name → Option Payload} (compatible : Compatible left right)
    {name : Name} {payload : Payload} :
    graph (overlay left right) name payload ↔ union (graph left) (graph right) name payload := by
  cases found : left name with
  | none => simp [graph, overlay, union, found]
  | some first =>
    simp only [graph, overlay, union, found]
    change some first = some payload ↔ some first = some payload ∨ right name = some payload
    simp only [Option.some.injEq]
    exact ⟨Or.inl, fun member => member.elim id (compatible found)⟩

end Silmaril.Proofs.Semantics.Naming.Table
