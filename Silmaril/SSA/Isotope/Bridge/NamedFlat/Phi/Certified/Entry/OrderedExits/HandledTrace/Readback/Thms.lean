module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Execution

/-! # Derive the public observation from local alignment and exact readback -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

section Alignment

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Readback (Alignment resultCodec)

universe u v w

/-- Local alignment preserves weak execution with the ordered packed exit
tag and encoded payload. -/
theorem Readback.Alignment.packed {Events : Type w → Type w} {F : Type v} {α β : Type u}
    {blocks publicBlocks exits publicExits captures publicCaptures : Nat}
    {source : FiniteCFG F blocks exits captures} {target : FiniteCFG F publicBlocks publicExits publicCaptures}
    {left : Primitive Events F α} {right : Primitive Events F β}
    {leftEnv : Env α} {rightEnv : Env β} {atom : α → β}
    (align : Alignment source target left right leftEnv rightEnv atom) :
    resultCodec atom <$> (region left leftEnv source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (region right rightEnv target.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.packed align

end Alignment

open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (HasTrace)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree.TraceInstitution (Sat)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature Program)
open NamedFlat.Entry.Record (Input)
open Readback (Alignment resultCodec)

variable {κ V Reg K : Type 1} [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{0, 0} κ}
  {I : NamedFlat.Entry.Interface κ Reg (Option K)} {fields : Option K → List (Reg × Ty κ)}
  {C : Captures V I.context} {signature : PrimitiveSignature P.Instr}
  {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {program : Program signature inputs outputs} {input : Fin a}

local notation "Atoms" => AtomValues.carrier (κ := κ)

/-- Discharge the whole-run observation equation using the flat table
recovered by exact reverse readback. Re-admission and public capture
agreement remain checked premises. Alignment checks the entry packet and
each decoded local packet under the two actual closure environments. -/
def PublicMatch.ofReadback (source : Admission P I fields C)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields source.code)
    (recompiled : NamedFlat.Entry.LiveOut.Admission P I fields lowered.source)
    (M : Model (κ := κ) (Event signature.Request signature.Reply) P.Instr)
    (record : Input I.context) (atom : Sigma Atoms → Atom)
    (packet : Denote (inputs input)) (entry : Program.PackedEntry program input)
    (publicAmbient publicRecord : Env Atom) (ambient : Env (Sigma Atoms))
    (agrees : entry.recordAgrees packet publicRecord)
    (align : Alignment source.code entry.target M.raw signature.primitive
      (NamedFlat.Entry.inputEnv I.context record) publicRecord atom) :
    PublicMatch source M record packet (resultCodec atom) entry publicAmbient publicRecord ambient :=
  ⟨lowered, recompiled, agrees,
    Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.observation
      source lowered recompiled M record atom entry publicAmbient publicRecord ambient align⟩

/-- A whole-interface verdict needs a checked alignment for every public
entry and packet, together with a supplied φ record for each. -/
theorem refinement?_iff_source [DecidableEq P.Instr]
    {W : Type 1} [DecidableEq W] {D : Captures W I.context}
    {source : Admission P I fields C} {target : Admission P I fields D}
    {M : Model (κ := κ) (Event signature.Request signature.Reply) P.Instr}
    {left right : Program signature inputs outputs}
    (record : ∀ i, Denote (inputs i) → Input I.context)
    (observeResult : Transfer (Sigma Atoms) → Transfer Atom)
    {leftEntry : ∀ i, Program.PackedEntry left i} {rightEntry : ∀ i, Program.PackedEntry right i}
    {leftRecord rightRecord : ∀ i, Denote (inputs i) → Env Atom}
    {leftAmbient rightAmbient : Env Atom} {ambient : Env (Sigma Atoms)}
    (l : ∀ i packet, PublicMatch source M (record i packet) packet observeResult (leftEntry i)
      leftAmbient (leftRecord i packet) ambient)
    (r : ∀ i packet, PublicMatch target M (record i packet) packet observeResult (rightEntry i)
      rightAmbient (rightRecord i packet) ambient) :
    left.refinement? right = true ↔
      ∀ i packet (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature),
        Sat policy ⟨_, observeResult <$> source.observe M (record i packet),
          HasTrace (observeResult <$> target.observe M (record i packet))⟩ :=
  (Iff.of_eq decide_eq_true_eq).trans <| forall_congr' fun i => forall_congr' fun packet =>
    refinementAt?_iff_source (l i packet) (r i packet)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
