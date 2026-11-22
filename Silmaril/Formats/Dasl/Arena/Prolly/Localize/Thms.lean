module

public import Silmaril.Formats.Dasl.Arena.Prolly.Localize.Defs
import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Localize

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Localize.Table

open Silmaril.Formats.Dasl.Prolly (Read Stored route scan)
open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type}
variable {source : Reader Name Key Payload} {before after : Table Name Key Payload}

theorem empty_valid : (empty (Name := Name) (Key := Key) (Payload := Payload)).Valid source :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.empty_valid

theorem Extends.refl (table : Table Name Key Payload) : table.Extends table :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.extends_refl table

theorem Extends.trans {later : Table Name Key Payload} (first : before.Extends after) (second : after.Extends later) :
    before.Extends later := Proofs.Formats.Dasl.Arena.Prolly.Localize.extends_trans first second

/-- A previously installed name reuses exactly the old index and table. Pass
the same source snapshot to retain the validity guarantee. -/
theorem add_hit [DecidableEq Name] {name : Name} {index : Nat} (hit : before.locate name = some index) :
    before.add source name = .ok before := by simp [add, hit]

theorem add_spec [DecidableEq Name] {name : Name} (valid : before.Valid source)
    (added : before.add source name = .ok after) :
    after.Valid source ∧ before.Extends after ∧ ∃ index, after.locate name = some index :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.add_spec valid added

theorem install_spec [DecidableEq Name] {schedule : List Name} (valid : before.Valid source)
    (done : install source schedule before = .ok after) :
    after.Valid source ∧ before.Extends after ∧ ∀ name ∈ schedule, ∃ index, after.locate name = some index :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.install_spec valid done

theorem checkedRoot_spec [DecidableEq Name] [LinearOrder Key] {width fuel index : Nat} {root : Name}
    {schedule : List Name} (valid : before.Valid source)
    (done : before.checkedRoot source width fuel root schedule = .ok (after, index)) :
    after.Valid source ∧ before.Extends after ∧ after.locate root = some index ∧
      ∃ entries map, scan source width fuel none root = .ok entries ∧ OrderedMap.ofEntries? entries = some map :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.checkedRoot_spec valid done

/-- An adequate finite schedule and a valid scan suffice. This does not assert
that a schedule can be discovered from an arbitrary reader. -/
theorem checkedRoot_of_install [DecidableEq Name] [LinearOrder Key] {width fuel index : Nat} {root : Name}
    {schedule : List Name} {entries : List (Key × Payload)} {map : OrderedMap Key Payload}
    (scanned : scan source width fuel none root = .ok entries) (ordered : OrderedMap.ofEntries? entries = some map)
    (installed : install source schedule before = .ok after) (hit : after.locate root = some index) :
    before.checkedRoot source width fuel root schedule = .ok (after, index) := by
  simp [checkedRoot, scanned, ordered, installed, hit, Except.mapError, Bind.bind, Except.bind]

theorem forward (valid : after.Valid source) :
    (after.installedReader source).Refines after.handle (after.arena.read source) :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.forward valid

theorem reverse (valid : after.Valid source) (fallback : Name) :
    (after.arena.read source).Refines (after.project fallback) source :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.reverse valid fallback

/-- Exact agreement for a localized root, including fuel and node faults.
Only structural child references are relabelled; keys and payloads are unchanged. -/
theorem route_agrees [LinearOrder Key] (valid : after.Valid source) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {name : Name} {index : Nat} (hit : after.locate name = some index) :
    route (after.arena.read source) width key fuel expected (.local index) =
      (route source width key fuel expected name).mapError (mapReadFault after.handle) :=
  Proofs.Formats.Dasl.Arena.Prolly.Localize.route_agrees valid width fuel key hit

/-- Applies to each binding reference that validates the captured successful
reads and the reference tree. Neither missing nor faulty reads give an answer. -/
theorem lookup_sound [LinearOrder Key] [DecidableEq Name]
    {codec : BlockCodec Name Key Payload} {input : Read Name} {names : List Name}
    (valid : after.Valid (Resident.capture codec input names).read)
    {tree : Semantics.Prolly.Tree Key Payload} (routable : tree.Routable)
    {address : Block Name Key Payload → Name} {store : Store Name}
    (stored : Stored codec address tree store) (bound : store.Binding) (sound : Read.Sound input store)
    {width fuel root : Nat} {key : Key} {result : Option Payload}
    (localized : after.locate (tree.rootName address) = some root)
    (hit : after.arena.lookup (Resident.capture codec input names).read width fuel root key = .ok result) :
    tree.entries.lookup key = result := by
  apply after.arena.lookup_sound (reverse valid (tree.rootName address)) routable stored bound sound ?_ hit
  simp [project, (valid.inverse _ _).mp localized]

end Silmaril.Formats.Dasl.Arena.Prolly.Localize.Table
