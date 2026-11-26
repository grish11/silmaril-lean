module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded

open Silmaril.Elgot (iter liftPure)
open Silmaril.SSA.LambdaRTL (CFG obs)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table ReplyEnumeration ConfigurationEnumeration)

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} [HasTy P.Instr Syntax.Ty]
  {I : Interface κ V K} {fields : K → List (V × Ty κ)}
  {source target : CFG V K P.Instr} {N : RequestSignature P.Instr}
  {R T : List Syntax.Ty} {E : Type → Type}
  {a : Admission P I fields source} {b : Admission P I fields target}
  {g : Table N R} {h : Table N T}
  {caller : Syntax.Payload (R.get g.entry)} {caller' : Syntax.Payload (T.get h.entry)}
  {result : TwoRequest.Tag → Transfer α} {query : Query N E} {instr : Primitive E P.Instr α} {input : V × Nat → Value α}

/-- At each encoded transfer, the original mutable step has the same query
and encoded successful continuation. A lookup miss observes the selected
fields of the actual final store in the original ordered exit. -/
theorem Corresponds.mutable_step (c : Corresponds a g caller query instr input result) (state : Cursor R)
    (pending : CFG.Cyclic.Transfer V K (Value α))
    (encoded : c.encode state =
      let m := treeModel instr
      let selected := fun k => (fields k).map Prod.fst
      CFG.Cyclic.Versioning.encodePacketLocal m (CFG.Cyclic.LiveOut.attach selected source)
        (CFG.Cyclic.LiveOut.encode m selected source pending)) :
    let m := treeModel instr
    let selected := fun k => (fields k).map Prod.fst
    let outgoing := fun p => FiniteCFG.packedTreeOutput
      (treeExitNumber I.exits (obs (CFG.Cyclic.LiveOut.project m selected p)))
    let again := fun p => CFG.Cyclic.Versioning.encodePacketLocal m (CFG.Cyclic.LiveOut.attach selected source)
      (CFG.Cyclic.LiveOut.encode m selected source p)
    (step g caller query result state >>= liftPure (Sum.map id c.encode)) =
      Sum.map outgoing again <$> CFG.Cyclic.step m source.blocks pending :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.mutable_step c state pending encoded

/-- Lift the exact entry and local step equations through the existing
cyclic runner. The result uses the original named table and exit projection. -/
theorem Corresponds.observe_eq (c : Corresponds a g caller query instr input result) :
    LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) source
      (fun reg => input (reg, 0)) =
      iter (step g caller query result) (atBlock ⟨g.entry, caller⟩) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.observe_eq c

/-- An accepted guarded certificate with ordinary target exits yields equality
of the two original named weak trees in the common query model. Both local
correspondences must cover every typed state and reply. -/
theorem observe_eq_of_checkProduct [DecidableEq P.Instr]
    (left : Corresponds a g caller query instr input) (right : Corresponds b h caller' query instr input)
    (replies : ReplyEnumeration N) (pairs : List (Packet R × Packet T))
    (checked : g.checkProduct h caller caller' replies pairs = true)
    (ordinary : ∀ i, h.selected i = false) :
    LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) source (fun reg => input (reg, 0)) =
      LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) target (fun reg => input (reg, 0)) :=
  left.observe_eq.trans <|
    (Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.iter_eq_of_checkProduct
      g h caller caller' query unitExit replies pairs checked ordinary).trans right.observe_eq.symm

/-- A successful search supplies the existing closed certificate. Its
inventory and traversal obligations are exactly those of native search. -/
theorem observe_eq_of_searchProduct [DecidableEq P.Instr]
    (left : Corresponds a g caller query instr input) (right : Corresponds b h caller' query instr input)
    (replies : ReplyEnumeration N) (leftInventory : ConfigurationEnumeration R)
    (rightInventory : ConfigurationEnumeration T) (pairs : List (Packet R × Packet T))
    (accepted : g.searchProduct h caller caller' replies leftInventory rightInventory = .accepted pairs)
    (ordinary : ∀ i, h.selected i = false) :
    LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) source (fun reg => input (reg, 0)) =
      LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) target (fun reg => input (reg, 0)) := by
  have sound := g.searchProduct_correct h caller caller' replies leftInventory rightInventory
  rw [accepted] at sound
  exact observe_eq_of_checkProduct left right replies pairs sound.1 ordinary

section Packed

variable [AtomValues κ]
variable {result : TwoRequest.Tag → Transfer (Sigma (AtomValues.carrier (κ := κ)))}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "A" => Region.packedInputType I.context.toList

/-- Use the original typed input store to compare the actual packed dispatcher
and the guarded execution under the same compatible model. -/
theorem Corresponds.packed_eq (M : Model (κ := κ) E P.Instr) (x : Ty.denote C A)
    (c : Corresponds a g caller query M.raw (store I.version.names I.context x) result)
    (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) a.program.code =
      iter (step g caller query result) (atBlock ⟨g.entry, caller⟩) :=
  (a.packed_tree M x ambient).trans
    ((congrArg (LiveOut.observeRaw M.raw I.exits (fun k => (fields k).map Prod.fst) source)
      (funext (store_version_zero I.names I.context x))).symm.trans c.observe_eq)

end Packed

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
