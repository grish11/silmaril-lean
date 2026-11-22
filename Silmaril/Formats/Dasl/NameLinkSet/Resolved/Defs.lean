module

public import Silmaril.Formats.Dasl.NameLinkSet.Defs
public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.NameLinkSet

open Silmaril.Semantics

variable {Key Name : Type} [LinearOrder Key]

/-- Object targets are already fully named trees; raw link targets are bytes. -/
abbrev Target : Link Name → Type
  | .obj _ => Named Name
  | .blob _ => ByteArray

def Target.named : (link : Link Name) → Target link → Named Name
  | .obj name, child => .obj name child
  | .blob name, bytes => .blob name bytes

/-- Every member has a target of its link's kind. Neither construction nor
inspection requires that those targets agree with a store. -/
abbrev ResolvedView (key : Encode.TotalCodec Key (Link Name)) (layout : Layout Key) :=
  (member : ↥(names layout)) → Target (key.encode member.val)

namespace ResolvedView

variable {key : Encode.TotalCodec Key (Link Name)} {layout : Layout Key}

def entry (view : ResolvedView key layout) (member : ↥(names layout)) : Named Name :=
  Target.named (key.encode member.val) (view member)

def memberAt (layout : Layout Key) (position : Fin layout.keys.length) : ↥(names layout) :=
  ⟨layout.keys.get position, List.mem_toFinset.mpr (List.get_mem _ _)⟩

/-- Materialize an ordinary DASL named list in the reference set's order. -/
def toNamed (view : ResolvedView key layout) : Named Name :=
  .list layout.keys.length fun position => view.entry (memberAt layout position)

/-- Forget names extensionally, without changing the reference set. -/
def contents (view : ResolvedView key layout) : Set Value :=
  Set.range fun member => (view.entry member).erase

/-- Agreement with an independently chosen naming relation, including link kind. -/
def Valid (view : ResolvedView key layout) (rel : Naming.Relation (Link Name) (Named Name)) : Prop :=
  ∀ member, rel (key.encode member.val) (view.entry member)

/-- The existing DASL expansion semantics check every nested binding as well. -/
abbrev ValidIn (view : ResolvedView key layout) (store : Store Name) : Prop :=
  view.Valid fun link => Expands store (.ref link)

end ResolvedView

/-- An ordinary named tree whose shallow projection is exactly a sorted array
of the chosen links. The witness is erased; no second key array is stored. -/
def IsSortedNamed (key : Encode.TotalCodec Key (Link Name)) (tree : Named Name) : Prop :=
  ∃ layout : Layout Key, tree.embed.shallow = linkArray.encode (links key layout)

abbrev SortedNamed (key : Encode.TotalCodec Key (Link Name)) := {tree : Named Name // IsSortedNamed key tree}

namespace SortedNamed

variable {key : Encode.TotalCodec Key (Link Name)}

def forget [DecidableEq Name] (tree : SortedNamed key) : Layout Key :=
  ((codec key).decode? tree.val.embed.shallow).get (by
    obtain ⟨layout, shape⟩ := tree.property
    change tree.val.embed.shallow = (codec key).encode layout at shape
    rw [shape, (codec key).recovers layout]
    rfl)

def entries (tree : Named Name) : List (Named Name) :=
  match tree with
  | .list _ children => List.ofFn children
  | _ => []

def entryLink? : Named Name → Option (Link Name)
  | .obj name _ => some (.obj name)
  | .blob name _ => some (.blob name)
  | _ => none

/-- A direct scan of resident AST children, without consulting the store. -/
def lookup? [DecidableEq Name] (tree : SortedNamed key) (query : Key) : Option (Named Name) :=
  (entries tree.val).find? fun node => decide (entryLink? node = some (key.encode query))

/-- Store coherence is independent of the tree's structural subtype. -/
def ValidIn (tree : SortedNamed key) (store : Store Name) : Prop :=
  Expands store tree.val.embed.shallow tree.val

end SortedNamed
end Silmaril.Formats.Dasl.NameLinkSet
