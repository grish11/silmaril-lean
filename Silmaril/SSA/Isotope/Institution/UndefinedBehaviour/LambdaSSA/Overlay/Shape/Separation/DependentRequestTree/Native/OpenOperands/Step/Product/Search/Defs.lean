module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Defs

/-! # Reachable product search for guarded native tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}

/-- An exhaustive finite inventory of configurations of a typed table.
The inventory may contain duplicates. -/
structure ConfigurationEnumeration (R : List Syntax.Ty) where
  configs : List (Packet R)
  complete : ∀ config, config ∈ configs

abbrev ProductConfig (R T : List Syntax.Ty) := Packet R × Packet T

/-- The selected reply and its resulting pair of exact configurations. -/
abbrev ProductEdge (S : RequestSignature Φ) (R T : List Syntax.Ty) :=
  (Σ f : Φ, Packet (S.replies f)) × ProductConfig R T

/-- Equal requests expose all of their shared typed reply edges. Terminal
pairs and local mismatches have no outgoing comparison edges. -/
def Head.productEdges [DecidableEq Φ] (replies : ReplyEnumeration S) :
    Head S R → Head S T → List (ProductEdge S R T)
  | .request f arg next, .request g arg' next' =>
    if eq : (f, arg.val) = (g, arg'.val) then
      let keys : f = g := congrArg Prod.fst eq
      (replies.packets f).map fun reply =>
        let target : Packet (S.replies g) := keys ▸ reply
        (⟨f, reply⟩, next reply.1 reply.2, next' target.1 target.2)
    else []
  | _, _ => []

def Table.productEdges [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pair : ProductConfig R T) : List (ProductEdge S R T) :=
  (g.head caller pair.1).productEdges replies (h.head caller' pair.2)

def Table.productLocal [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pair : ProductConfig R T) : Bool :=
  (g.head caller pair.1).checkPair replies (fun _ _ => true) (h.head caller' pair.2)

inductive ProductPath (edges : ProductConfig R T → List (ProductEdge S R T)) (start : ProductConfig R T) :
    List (ProductEdge S R T) → ProductConfig R T → Prop where
  | start : ProductPath edges start [] start
  | step {past p edge} : ProductPath edges start past p → edge ∈ edges p →
      ProductPath edges start (past ++ [edge]) edge.2

/-- Every pair visited along a path, including its initial pair. -/
def ProductPath.vertices (start : ProductConfig R T) (path : List (ProductEdge S R T)) :
    List (ProductConfig R T) :=
  start :: path.map (fun edge => edge.2)

namespace ProductSearch

abbrev Visit (S : RequestSignature Φ) (R T : List Syntax.Ty) :=
  ProductConfig R T × List (ProductEdge S R T)

def discover (edges : ProductConfig R T → List (ProductEdge S R T))
    (remaining : List (ProductConfig R T)) (seen : List (Visit S R T)) : Option (Visit S R T) :=
  seen.findSome? fun (p, path) =>
    (edges p).findSome? fun edge =>
      if productContains remaining edge.2.1 edge.2.2 then some (edge.2, path ++ [edge]) else none

/-- Each discovery removes its configuration from the remaining inventory. -/
def scan (edges : ProductConfig R T → List (ProductEdge S R T)) :
    Nat → List (ProductConfig R T) → List (Visit S R T) → List (Visit S R T)
  | 0, _, seen => seen
  | fuel + 1, remaining, seen =>
    match discover edges remaining seen with
    | none => seen
    | some visit =>
      let remaining' := remaining.filter fun p => !productContains [visit.1] p.1 p.2
      scan edges fuel remaining' (visit :: seen)

/-- Explore from a typed entry with any packet-indexed edge function. -/
def visits (edges : ProductConfig R T → List (ProductEdge S R T))
    (entry : ProductConfig R T) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    List (Visit S R T) :=
  let remaining := (left.configs.product right.configs).filter fun p => !productContains [entry] p.1 p.2
  scan edges remaining.length remaining [(entry, [])]

inductive Result (S : RequestSignature Φ) (R T : List Syntax.Ty) where
  | accepted (pairs : List (ProductConfig R T))
  | mismatch (pair : ProductConfig R T) (path : List (ProductEdge S R T))

end ProductSearch

/-- Scan the reachable synchronized pairs for this caller, keeping their reply paths. -/
def Table.productVisits [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    List (ProductSearch.Visit S R T) :=
  ProductSearch.visits (g.productEdges h caller caller' replies) (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) left right

/-- Start with the entry pair and inspect its reachable typed product.
A mismatch carries the shared reply path from the entry in forward order. -/
def Table.searchProduct [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    ProductSearch.Result S R T :=
  let seen := g.productVisits h caller caller' replies left right
  match seen.find? fun v => !g.productLocal h caller caller' replies v.1 with
  | none => .accepted (seen.map Prod.fst)
  | some (pair, path) => .mismatch pair path

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
