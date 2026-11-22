module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Localize

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block)
open Silmaril.Formats.Dasl.Prolly (scan)

variable {Name Key Payload : Type}

def childNames : Block Name Key Payload → List Name
  | .leaf _ => []
  | .branch _ children => children.map Prod.snd

structure Table (Name Key Payload : Type) where
  arena : Indexed Name Key Payload
  locate : Name → Option Nat
  origin : Nat → Option Name

inductive Fault (Name : Type) where
  | read (fault : Silmaril.Formats.Dasl.Prolly.Fault Name)
  | unplanned (name : Name)
  | forward (name : Name)
  deriving DecidableEq, Repr

def mapReadFault {Ref Target : Type} (map : Ref → Target) :
    Silmaril.Formats.Dasl.Prolly.Fault Ref → Silmaril.Formats.Dasl.Prolly.Fault Target
  | .fuel ref => .fuel (map ref)
  | .missing ref => .missing (map ref)
  | .invalidWire ref => .invalidWire (map ref)
  | .invalidNode ref => .invalidNode (map ref)

namespace Table

def empty : Table Name Key Payload := ⟨.empty, fun _ => none, fun _ => none⟩

def handle (table : Table Name Key Payload) (name : Name) : Handle Name :=
  (table.locate name).elim (.external name) .local

/-- The default only supplies a total proof projection. A readable local
index in a valid table always has an origin. -/
def project (table : Table Name Key Payload) (fallback : Name) : Handle Name → Name
  | .local index => (table.origin index).getD fallback
  | .external name => name

def Covered (locate : Name → Option Nat) (block : Block Name Key Payload) : Prop :=
  ∀ child ∈ childNames block, ∃ index, locate child = some index

/-- Installed edges are all local. An unrelated object/blob link embedded in a
leaf payload or key is not a structural Prolly child. -/
structure Valid (table : Table Name Key Payload) (source : Reader Name Key Payload) : Prop where
  inverse : ∀ name index, table.locate name = some index ↔ table.origin index = some name
  domain : ∀ index, index < table.arena.blocks.size → ∃ name, table.origin index = some name
  installed : ∀ name index, table.locate name = some index →
    ∃ block, source name = .ok block ∧ table.arena.blocks[index]? = some (Indexed.localize table.locate block) ∧
      Covered table.locate block
  backward : ∀ (index : Nat) block, table.arena.blocks[index]? = some block → Indexed.admissible index block = true

/-- One append lineage: observed handles and bytes already present cannot be
rebound. This is not a comparison of bare indices from different tables. -/
structure Extends (before after : Table Name Key Payload) : Prop where
  hits : ∀ ⦃name index⦄, before.locate name = some index → after.locate name = some index
  origins : ∀ ⦃index name⦄, before.origin index = some name → after.origin index = some name
  blocks : ∀ ⦃index : Nat⦄ ⦃block⦄, before.arena.blocks[index]? = some block → after.arena.blocks[index]? = some block

abbrev Ticket (table : Table Name Key Payload) (name : Name) := {index : Nat // table.locate name = some index}

def Ticket.lift {before after : Table Name Key Payload} {name : Name} (extension : before.Extends after)
    (ticket : before.Ticket name) : after.Ticket name := ⟨ticket.val, extension.hits ticket.property⟩

/-- A proof view whose domain contains only installed names. External fallback
is deliberately outside the forward refinement contract. -/
def installedReader (table : Table Name Key Payload) (source : Reader Name Key Payload) : Reader Name Key Payload :=
  fun name => if (table.locate name).isSome then source name else .error (.missing name)

def write [DecidableEq Name] (table : Table Name Key Payload) (name : Name)
    (arena : Indexed Name Key Payload) (index : Nat) : Table Name Key Payload where
  arena := arena
  locate query := if query = name then some index else table.locate query
  origin query := if query = index then some name else table.origin query

/-- One step of a checked schedule. A hit reuses the already verified block
from the same source view. A miss requires every structural child first. -/
def add [DecidableEq Name] (table : Table Name Key Payload) (source : Reader Name Key Payload) (name : Name) :
    Except (Fault Name) (Table Name Key Payload) := do
  if (table.locate name).isSome then .ok table
  else
    let block ← (source name).mapError Fault.read
    if (childNames block).all (fun child => (table.locate child).isSome) then
      match table.arena.append? (Indexed.localize table.locate block) with
      | none => .error (.forward name)
      | some (arena, index) => .ok (table.write name arena index)
    else .error (.unplanned name)

def install [DecidableEq Name] (source : Reader Name Key Payload) :
    List Name → Table Name Key Payload → Except (Fault Name) (Table Name Key Payload)
  | [], table => .ok table
  | name :: rest, table => (table.add source name).bind (install source rest)

/-- First check the selected rooted graph using the existing closed-view scan
and global entry ordering check. Then install the children-before-parent
schedule. An omitted root/child is not key absence. No tentative table is
returned on a fault. -/
def checkedRoot [DecidableEq Name] [LinearOrder Key] (table : Table Name Key Payload) (source : Reader Name Key Payload)
    (width fuel : Nat) (root : Name) (schedule : List Name) : Except (Fault Name) (Table Name Key Payload × Nat) := do
  let entries ← (scan source width fuel none root).mapError Fault.read
  let some _ := OrderedMap.ofEntries? entries | .error (.read (.invalidNode root))
  let installed ← install source schedule table
  match installed.locate root with
  | none => .error (.unplanned root)
  | some index => .ok (installed, index)

end Table
end Silmaril.Formats.Dasl.Arena.Prolly.Localize
