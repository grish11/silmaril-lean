module

public import Silmaril.Semantics.BTree.Defs
public import Silmaril.Semantics.Page.Defs

/-! A page representation of finite leaf-oriented B-trees. -/

@[expose] public section
namespace Silmaril.Semantics.BTreePages

open BTree

universe u
variable {Key Value Id : Type} {Memory : Type u}

/-- A path of zero-based child slots from the root. -/
abbrev Position := List Nat

/-- Assigns page IDs to positions. Only the positions present in a tree matter. -/
abbrev Layout (Id : Type) := Position → Id

inductive PageData (Key Value Id : Type) where
  | leaf (entries : List (Key × Value))
  | branch (children : Branch Key Id)

/-- Follow a structural path, independently of memory and page IDs. -/
def atPath (tree : Tree Key Value) : Position → Option (Tree Key Value)
  | [] => some tree
  | slot :: rest =>
    match tree with
    | ⟨0, _⟩ => none
    | ⟨height + 1, node⟩ =>
      node.children[slot]?.bind (fun child => atPath ⟨height, child⟩ rest)

/-- Encode a single node with pointers to its immediate children. -/
def encode (layout : Layout Id) (position : Position) :
    (height : Nat) → Node Key Value height → PageData Key Value Id
  | 0, entries => .leaf entries
  | _ + 1, node => .branch
      ⟨node.fenced.zipIdx.map (fun (entry, slot) => (entry.1, layout (position ++ [slot]))),
        layout (position ++ [node.fenced.length])⟩

def pageAt (layout : Layout Id) (tree : Tree Key Value) (position : Position) :
    Option (PageData Key Value Id) :=
  (atPath tree position).map (fun subtree => encode layout position subtree.height subtree.root)

/-- Exactly the page IDs assigned to reachable positions, including the root. -/
def Footprint (layout : Layout Id) (tree : Tree Key Value) (page : Id) : Prop :=
  ∃ position, atPath tree position ≠ none ∧ layout position = page

/-- Logical validity and absence of aliases between positions of this tree. -/
def WellFormed [LinearOrder Key] (layout : Layout Id) (tree : Tree Key Value) : Prop :=
  tree.Valid ∧ ∀ left right, atPath tree left ≠ none → atPath tree right ≠ none →
    layout left = layout right → left = right

/-- The set of memories representing this tree. Every footprint slot is defined
with the expected payload. Other slots are unrestricted. -/
def Represents [LinearOrder Key] (store : Page.Store Id (PageData Key Value Id) Memory)
    (layout : Layout Id) (tree : Tree Key Value) (memory : Memory) : Prop :=
  WellFormed layout tree ∧ ∀ position data, pageAt layout tree position = some data →
    store.lookup memory (layout position) = .defined data

/-- Relations on ordinary slots, including absent and UNDEF slots. -/
def AgreesOn (store : Page.Store Id (PageData Key Value Id) Memory) (pages : Id → Prop)
    (left right : Memory) : Prop :=
  ∀ page, pages page → store.lookup left page = store.lookup right page

/-- Two roots can share a page precisely when their demands at that ID agree. -/
def Compatible (leftLayout rightLayout : Layout Id) (left right : Tree Key Value) : Prop :=
  ∀ leftPos rightPos leftData rightData,
    pageAt leftLayout left leftPos = some leftData →
    pageAt rightLayout right rightPos = some rightData →
    leftLayout leftPos = rightLayout rightPos → leftData = rightData

/-- One lookup decision. The left case finishes at a leaf (possibly with a miss).
The right case gives the ID of the next page. -/
def inspect [LinearOrder Key] (key : Key) : PageData Key Value Id → Option Value ⊕ Id
  | .leaf entries => .inl (entries.lookup key)
  | .branch children => .inr (children.route key).2

/-- Read a page and make the same decision used by the full lookup. -/
def lookupStep [LinearOrder Key] (key : Key) (page : Id) :
    Page.Program Id (PageData Key Value Id) (Option Value ⊕ Id) :=
  (Page.Program.read page).bind (fun data => .pure (inspect key data))

/-- Read one page per level. The height is trusted root metadata; inconsistent
page kinds take the explicit divergence branch. -/
def lookup [LinearOrder Key] (key : Key) : Nat → Id → Page.Program Id (PageData Key Value Id) (Option Value)
  | 0, page => (lookupStep key page).bind fun
    | .inl result => .pure result
    | .inr _ => .diverge
  | height + 1, page => (lookupStep key page).bind fun
    | .inl _ => .diverge
    | .inr child => lookup key height child

end Silmaril.Semantics.BTreePages
