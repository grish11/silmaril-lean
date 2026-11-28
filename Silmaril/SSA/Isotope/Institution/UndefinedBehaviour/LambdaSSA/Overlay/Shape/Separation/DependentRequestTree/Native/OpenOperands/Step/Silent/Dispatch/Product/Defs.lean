module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs

/-! # Reachable products of packet-indexed packed dispatchers -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Category.FiniteIteration hiding Table
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives model)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty}

/-- Silent hops have already been resolved at each whole typed packet.
Only equal exposed requests contribute typed reply edges. -/
def Table.productEdges (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (pair : ProductConfig R T) : List (ProductEdge S R T) :=
  (g.head left a pair.1).productEdges replies (h.head right b pair.2)

def Table.productVisits (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    List (ProductSearch.Visit S R T) :=
  ProductSearch.visits (g.productEdges h a b replies left right) (⟨g.entry, a⟩, ⟨h.entry, b⟩) left right

def Table.productMismatch? (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option (ProductSearch.Visit S R T) :=
  (g.productVisits h a b replies left right).find? fun v =>
    !(g.head left a v.1.1).checkPair replies (fun _ _ => true) (h.head right b v.1.2)

/-- A sufficient carrier bound over all typed caller packets is the
maximum number of distinct reachable pairs, including their entry pair. -/
def Table.cutoff (g : Table S R) (h : Table S T) (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) : Nat :=
  ((callers.packets.map fun a => (g.productVisits h (decodeLeft a) (decodeRight a) replies left right).length).max?).getD 0

/-- A Boolean verdict follows exact readback at both original endpoints.
The reachable product decides the cutoff comparison directly. -/
def Table.checkEntries? (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option Bool :=
  if g.checkNative raw && h.checkNative raw' then
    some (callers.packets.all fun a => (g.productMismatch? h (decodeLeft a) (decodeRight a) replies left right).isNone)
  else none

/-- Compare the original decorated packed CFGs over all typed caller
packets and deterministic interpreters at the specified store universe. -/
def Table.DeterministicRefines (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry)) : Prop :=
  ∀ (σ : Type v) (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ),
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
