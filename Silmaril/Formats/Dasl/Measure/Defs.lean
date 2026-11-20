module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

variable {Name Ref : Type}

structure Metrics where
  nodes : Nat := 0
  depth : Nat := 0
  links : Nat := 0
  linkDepth : Nat := 0
  deriving DecidableEq, Repr

inductive Scope where
  | inline
  | unfolded
  deriving DecidableEq

namespace Metrics

def siblings (left right : Metrics) : Metrics :=
  ⟨left.nodes + right.nodes, max left.depth right.depth, left.links + right.links,
    max left.linkDepth right.linkDepth⟩

def parent (link : Nat) (children : Metrics) : Metrics :=
  ⟨children.nodes + 1, children.depth + 1, children.links + link, children.linkDepth + link⟩

def sum (children : List Metrics) : Metrics := children.foldr siblings {}

/-- Budgets are inclusive and independent; no byte-size estimate is implicit. -/
def Within (result budget : Metrics) : Prop :=
  result.nodes ≤ budget.nodes ∧ result.depth ≤ budget.depth ∧
  result.links ≤ budget.links ∧ result.linkDepth ≤ budget.linkDepth

structure Valid (result : Metrics) : Prop where
  depth_le_nodes : result.depth ≤ result.nodes
  links_le_nodes : result.links ≤ result.nodes
  linkDepth_le_links : result.linkDepth ≤ result.links
  linkDepth_le_depth : result.linkDepth ≤ result.depth

end Metrics

/-- Count AST constructors, including one constructor for a link, and maximum numbers
of constructors and links on a path. Inline measurements stop at links. Blob payloads
are bytes, not extra AST constructors. An empty container has depth one. -/
def Tree.measure (scope : Scope) : Tree Ref Name → Metrics
  | .ref _ | .blob _ _ => Metrics.parent 1 {}
  | .obj _ child => Metrics.parent 1 (match scope with | .inline => {} | .unfolded => child.measure scope)
  | .dict keys values => Metrics.parent 0 (Metrics.sum (keys.sort.attach.map fun key =>
      (values ⟨key.val, (Finset.mem_sort _).mp key.property⟩).measure scope))
  | .list _ values => Metrics.parent 0 (Metrics.sum (List.ofFn fun index => (values index).measure scope))
  | _ => Metrics.parent 0 {}

inductive Block (Name : Type) where
  | object (name : Name) (value : Shallow Name)
  | blob (name : Name) (bytes : ByteArray)

def Block.link : Block Name → Link Name
  | .object name _ => .obj name
  | .blob name _ => .blob name

def Block.BoundIn (store : Store Name) : Block Name → Prop
  | .object name value => store.objects name value
  | .blob name bytes => store.blobs name bytes

def Block.byteSize? (serialize : Shallow Name → Option ByteArray) : Block Name → Option Nat
  | .object _ value => (serialize value).map ByteArray.size
  | .blob _ bytes => some bytes.size

/-- One entry per expanded target occurrence; unresolved references add no block. -/
def Partial.blockOccurrences : Partial Name → List (Block Name)
  | .obj name child => .object name (Partial.shallow child) :: blockOccurrences child
  | .blob name bytes => [.blob name bytes]
  | .dict keys values => keys.sort.attach.flatMap fun key =>
      blockOccurrences (values ⟨key.val, (Finset.mem_sort _).mp key.property⟩)
  | .list _ values => (List.ofFn fun index => blockOccurrences (values index)).flatten
  | _ => []

/-- The named root block is counted once, in addition to expanded targets. -/
def Partial.blocks (root : Name) (tree : Partial Name) : List (Block Name) :=
  .object root tree.shallow :: tree.blockOccurrences

def Named.blocks (root : Name) (tree : Named Name) : List (Block Name) := tree.embed.blocks root

/-- A budget for each individual CAS block. Bytes and inline shape have separate APIs. -/
def Block.inlineMetrics (block : Block Name) : Metrics :=
  match block with
  | .object _ value => value.measure .inline
  | .blob _ _ => {}

def maxInlineMetrics (blocks : List (Block Name)) : Metrics :=
  blocks.foldr (fun block rest =>
    let metric := block.inlineMetrics
    ⟨max metric.nodes rest.nodes, max metric.depth rest.depth, max metric.links rest.links,
      max metric.linkDepth rest.linkDepth⟩) {}

/-- Distinct block identities count typed names, not untyped digests or equal payloads. -/
def distinctLinks [DecidableEq Name] (blocks : List (Block Name)) : Finset (Link Name) :=
  (blocks.map Block.link).toFinset

/-- Sum serialized object bytes and raw bytes over occurrences, without defaulting errors. -/
def occurrenceBytes? (serialize : Shallow Name → Option ByteArray) (blocks : List (Block Name)) : Option Nat :=
  (blocks.mapM (Block.byteSize? serialize)).map List.sum

def maxBlockBytes? (serialize : Shallow Name → Option ByteArray) (blocks : List (Block Name)) : Option Nat :=
  (blocks.mapM (Block.byteSize? serialize)).map (·.foldr max 0)

/-- Sum one size per distinct typed name. The size reader must be tied to the intended
reference (for example by `byteSizeAgrees`); the function never picks between conflicting
payloads having the same name. -/
def distinctBytes? [DecidableEq Name] (size? : Link Name → Option Nat) (blocks : List (Block Name)) : Option Nat :=
  ((blocks.map Block.link).eraseDups.mapM size?).map List.sum

def byteSizeAgrees (store : Store Name) (serialize : Shallow Name → Option ByteArray)
    (size? : Link Name → Option Nat) : Prop :=
  ∀ block : Block Name, block.BoundIn store → size? block.link = block.byteSize? serialize

open Silmaril.Semantics.Naming in
/-- Specification lookup; executable readers can instead prove `byteSizeAgrees`. -/
noncomputable def storeByteSize? {store : Store Name} (bound : store.Binding)
    (serialize : Shallow Name → Option ByteArray) : Link Name → Option Nat
  | .obj name => (bound.1.lookup name).bind fun value => (serialize value).map ByteArray.size
  | .blob name => (bound.2.lookup name).map ByteArray.size

end Silmaril.Formats.Dasl
