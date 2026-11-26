module

public import Silmaril.Semantics.BTreePages.Defs
public import Silmaril.Semantics.Page.Array.Defs

/-! Routed B-tree observations and representation at both endpoints of a page trace. -/

@[expose] public section
namespace Silmaril.Semantics.BTreePages

open BTree

universe u
variable {Key Value Id : Type} {Memory : Type u} [LinearOrder Key]

/-- The reads demanded by the logical route, in order from the root to a leaf. -/
def lookupTraceFrom (key : Key) (layout : Layout Id) (position : Position) :
    (height : Nat) → Node Key Value height → ReadWrite.ReadTrace Id (PageData Key Value Id)
  | 0, node => [(layout position, encode layout position 0 node)]
  | height + 1, node =>
    let child := node.route key
    (layout position, encode layout position (height + 1) node) ::
      lookupTraceFrom key layout (position ++ [child.1]) height child.2

def lookupTrace (key : Key) (layout : Layout Id) (tree : Tree Key Value) :
    ReadWrite.ReadTrace Id (PageData Key Value Id) :=
  lookupTraceFrom key layout [] tree.height tree.root

/-- The endpoints may have different trees and placements. -/
def Validates (trace : ReadWrite.Trace Id (PageData Key Value Id))
    (store : Page.Store Id (PageData Key Value Id) Memory)
    (beforeLayout : Layout Id) (before : Tree Key Value)
    (afterLayout : Layout Id) (after : Tree Key Value) : Prop :=
  trace.Validates store.access (Represents store beforeLayout before) (Represents store afterLayout after)

def RepresentsUndefArray {n : Nat} (layout : Layout Nat) (tree : Tree Key Value)
    (pages : Page.UndefArray n (PageData Key Value Nat)) : Prop :=
  Represents (Page.mapStore Nat _) layout tree pages.toMemory

def RepresentsArray {n : Nat} (layout : Layout Nat) (tree : Tree Key Value)
    (pages : Page.Array n (PageData Key Value Nat)) : Prop :=
  RepresentsUndefArray layout tree pages.embed

end Silmaril.Semantics.BTreePages
