module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs

/-! # Typed φ admission at the ordered live-out exit interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Record (Input)

universe u v
variable {κ V Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq Reg] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

/-- The actual ordered φ lowering, accepted at the supplied block profile
and each exit's old payload and ordered live-out record type. -/
structure Admission (P : FlatInstitution.Signature.{u, v} κ)
    (I : NamedFlat.Entry.Interface κ Reg (Option K)) (fields : Option K → List (Reg × Ty κ))
    (C : Captures V I.context) where
  source : Phi.Graph V K P.Instr
  inputs : List V
  arrivals : Phi.GlobalSSA.Certificate V K
  checked : Phi.OrderedExits.check source I.exits inputs arrivals = true
  internal : Fin (Versioning.compile (Phi.OrderedExits.lower source)).blocks.length → Ty κ
  code : FiniteCFG P.Instr (Versioning.compile (Phi.OrderedExits.lower source)).blocks.length I.exits.length I.slots
  elaborated : NamedFlat.compile (Phi.OrderedExits.lower source) I.exits C.names = some code
  typed : code.HasType I.context internal (NamedFlat.Entry.LiveOut.exitInterface I fields).external

/-- Check the ordered exit partition and the arrival table, then run the
existing typed elaborator at the stated packet and exit profiles. -/
def admit [DecidableEq κ] (I : NamedFlat.Entry.Interface κ Reg (Option K))
    (fields : Option K → List (Reg × Ty κ)) (C : Captures V I.context)
    (graph : Phi.Graph V K P.Instr) (inputs : List V) (arrivals : Phi.GlobalSSA.Certificate V K)
    (internal : Fin (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length → Ty κ) :
    Option (Admission P I fields C) :=
  if checked : Phi.OrderedExits.check graph I.exits inputs arrivals = true then
    (NamedFlat.compileTyped (Phi.OrderedExits.lower graph) I.exits C.names I.context internal
      (NamedFlat.Entry.LiveOut.exitInterface I fields).external).map fun result =>
        ⟨graph, inputs, arrivals, checked, internal, result.val, result.property.1, result.property.2⟩
  else none

/-- Apply the existing packet-local reverse checker to the actual table. -/
def Admission.reverseChecked [DecidableEq P.Instr] (a : Admission P I fields C)
    (registers : NamedFlat.Entry.Reverse.Registers Reg)
    (internal : Fin (Versioning.compile (Phi.OrderedExits.lower a.source)).blocks.length → Option K) :
    Option (NamedFlat.Entry.Reverse.Lowered I fields a.code) :=
  NamedFlat.Entry.Reverse.lowerChecked I fields registers internal a.code

variable [AtomValues κ] {Events : Type u → Type u}

/-- Observe the independent φ runner, retaining the declared exit order. -/
noncomputable def Admission.observe (a : Admission P I fields C)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :=
  Phi.OrderedExits.run (treeModel M.raw) a.source (C.store record) >>= fun p =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber I.exits p))

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
