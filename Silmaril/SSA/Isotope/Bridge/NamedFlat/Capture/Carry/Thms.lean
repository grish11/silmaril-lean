module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Typed
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Tree

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region BlockInput splitTransfer)

universe u v w x
variable {F : Type v} {blocks exits n : Nat}

theorem graph_hasType {τ : Type u} [TypeFormers τ] [HasTy F τ]
    {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}
    {g : FiniteCFG F blocks exits n} (typed : g.HasType β R D) (slot : Fin n) :
    (graph g slot).HasType β (packetTypes R β slot) D :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graph_hasType typed slot

/-- Adding and decoding the caller field preserves the weak ITree at every
caller environment, including the original order and values of outward exits.
The internal simulation uses the existing iterator's uniformity law. -/
theorem graph_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n) (slot : Fin n) (env : Env α) :
    region raw env (graph g slot).erase = region raw env g.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graph_tree raw g slot env

/-- Iterated product typing keeps the caller context and ordered exits. -/
theorem graphList_hasType {τ : Type u} [TypeFormers τ] [HasTy F τ]
    {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}
    {g : FiniteCFG F blocks exits n} (typed : g.HasType β R D) (slots : List (Fin n)) :
    (graphList g slots).HasType β (packetTypesList R β slots) D :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graphList_hasType typed slots

/-- Extend an internal entry packet with the selected caller fields.
An outward entry transfer keeps its original value and label. -/
theorem graphList_entry_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n)
    (slots : List (Fin n)) (env : Env α) :
    region raw env (graphList g slots).entry.erase =
      (region raw env g.entry.erase >>= fun out =>
        pure (out.1, if out.1 < blocks then packValue env slots out.2 else out.2)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graphList_entry_tree raw g slots env

/-- The actual row decoders project the supplied fields out of the ordered
packet. The row preserves outward transfers and re-encodes internal ones. -/
theorem graphList_row_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n)
    (slots : List (Fin n)) (env : Env α) (p : BlockInput α blocks) :
    (region raw (extend env (packValue env slots p.2)) ((graphList g slots).block p.1).erase >>=
      fun out => pure (splitTransfer blocks out)) =
    ((region raw (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)) >>=
      fun out => pure (out.map id (fun q => (q.1, packValue env slots q.2)))) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graphList_row_tree raw g slots env p

/-- Composing the single-packet simulations preserves the existing weak
ITree for the actual table at every caller environment. -/
theorem graphList_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n) (slots : List (Fin n)) (env : Env α) :
    region raw env (graphList g slots).erase = region raw env g.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graphList_tree raw g slots env

end Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
