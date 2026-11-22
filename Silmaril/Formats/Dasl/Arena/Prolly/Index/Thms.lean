module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Index

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly

open Silmaril.Semantics.Prolly (Block)
open Silmaril.Formats.Dasl.Prolly (Read Stored route)

variable {Name Key Payload Ref Target : Type}

/-- Successful routed reads commute with reference projection. This does not turn source
faults into target faults or equate the two views' available blocks. -/
theorem route_refines [LinearOrder Key] {source : Reader Ref Key Payload} {map : Ref → Target}
    {target : Reader Target Key Payload} (agrees : source.Refines map target) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {ref : Ref} {result : Option Payload}
    (hit : route source width key fuel expected ref = .ok result) :
    route target width key fuel expected (map ref) = .ok result :=
  Proofs.Formats.Dasl.Arena.Prolly.Index.route_refines agrees width fuel key hit

namespace Indexed

/-- The fresh index is exactly the old length; every other lookup is unchanged.
Iterating successful appends never rebinds an existing local index. -/
theorem append_spec {arena next : Indexed Name Key Payload} {block : Block (Handle Name) Key Payload} {index : Nat}
    (appended : arena.append? block = some (next, index)) :
    index = arena.blocks.size ∧ next.blocks[index]? = some block ∧
      (∀ other, other ≠ index → next.blocks[other]? = arena.blocks[other]?) :=
  Proofs.Formats.Dasl.Arena.Prolly.Index.append_spec appended

theorem acquire_spec {arena next : Indexed Name Key Payload} {source : Reader Name Key Payload}
    {locate : Name → Option Nat} {name : Name} {index : Nat}
    (acquired : arena.acquire source locate name = .ok (some (next, index))) :
    ∃ block, source name = .ok block ∧ next.blocks[index]? = some (localize locate block) :=
  Proofs.Formats.Dasl.Arena.Prolly.Index.acquire_spec acquired

theorem admissible_iff {bound level : Nat} {children : List (Key × Handle Name)} :
    admissible bound (.branch (Payload := Payload) level children) = true ↔
      ∀ child ∈ children, KnownBefore bound child.2 :=
  Proofs.Formats.Dasl.Arena.Prolly.Index.admissible_iff

theorem append_local_live {arena next : Indexed Name Key Payload} {index level child : Nat} {key : Key}
    {children : List (Key × Handle Name)} (appended : arena.append? (.branch level children) = some (next, index))
    (member : (key, .local child) ∈ children) :
    ∃ block, arena.blocks[child]? = some block ∧ next.blocks[child]? = some block :=
  Proofs.Formats.Dasl.Arena.Prolly.Index.append_local_live appended member

theorem localize_relabel (locate : Name → Option Nat) (project : Handle Name → Name)
    (external : ∀ name, project (.external name) = name)
    (localName : ∀ name index, locate name = some index → project (.local index) = name)
    (block : Block Name Key Payload) : relabel project (localize locate block) = block :=
  Proofs.Formats.Dasl.Arena.Prolly.Index.localize_relabel locate project external localName block

theorem eagerNames_at (arena : Indexed Name Key Payload) (choose : Block Name Key Payload → Option Name)
    (fuel : Nat) (index : Fin arena.blocks.size) :
    (arena.eagerNames choose fuel)[index.val]? = some (arena.name? choose fuel (.local index)) := by
  simp [eagerNames]

/-- Conditional refinement to the named snapshot, then to any valid binding reference.
The explicit projection premise is a requirement on a localization, not a hash uniqueness axiom. -/
theorem lookup_sound [LinearOrder Key] [DecidableEq Name] (arena : Indexed Name Key Payload)
    {codec : BlockCodec Name Key Payload} {input : Read Name} {names : List Name} {project : Handle Name → Name}
    (agrees : (arena.read (Resident.capture codec input names).read).Refines project (Resident.capture codec input names).read)
    {tree : Semantics.Prolly.Tree Key Payload} (routable : tree.Routable) {address : Block Name Key Payload → Name}
    {store : Store Name} (stored : Stored codec address tree store) (bound : store.Binding) (sound : Read.Sound input store)
    {width fuel root : Nat} {key : Key} {result : Option Payload} (rootName : project (.local root) = tree.rootName address)
    (hit : arena.lookup (Resident.capture codec input names).read width fuel root key = .ok result) :
    tree.entries.lookup key = result := by
  apply Resident.lookup_sound routable stored bound sound (width := width) (fuel := fuel) (key := key) (names := names)
  exact rootName ▸ route_refines agrees width fuel key hit

end Indexed
end Silmaril.Formats.Dasl.Arena.Prolly
