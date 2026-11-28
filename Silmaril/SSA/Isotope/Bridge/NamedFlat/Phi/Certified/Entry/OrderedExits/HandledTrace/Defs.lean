module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Execution.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs

/-! # Align checked ordered φ execution with a finite public packed entry -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Transfer region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered (Model)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature Program)
open NamedFlat.Entry.Record (Input)

variable {κ V Reg K : Type 1} [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution.Signature.{0, 0} κ}
  {I : NamedFlat.Entry.Interface κ Reg (Option K)} {fields : Option K → List (Reg × Ty κ)}
  {C : Captures V I.context} {signature : PrimitiveSignature P.Instr}
  {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {program : Program signature inputs outputs} {input : Fin a}

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "Events" => Event signature.Request signature.Reply

/-- The exact re-admission refers to the attached output of the reverse
certificate. The public program can use another private state space. Its
checked packed tree must realize the same observation at this packet, with
the stated capture agreement and a common result encoding. -/
structure PublicMatch (source : Admission P I fields C)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context)
    (packet : Denote (inputs input)) (observeResult : Transfer (Sigma Atoms) → Transfer Atom)
    (entry : Program.PackedEntry program input)
    (publicAmbient publicRecord : Env Atom) (ambient : Env (Sigma Atoms)) where
  lowered : NamedFlat.Entry.Reverse.Lowered I fields source.code
  recompiled : NamedFlat.Entry.LiveOut.Admission P I fields lowered.source
  agrees : entry.recordAgrees packet publicRecord
  observes : observeResult <$> region M.raw (extend ambient (encodeValue Atoms _ record))
    recompiled.program.code = entry.observe publicAmbient publicRecord

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
