module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Defs

/-! # Certified predecessor-indexed φ comparisons at supplied typed records -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph lower)
open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)

universe u v
variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}

/-- Distinct version-zero fields at a supplied record. The private packet
name, when selected, has unit type because the φ input store fixes it to unit. -/
structure Captures (V : Type (u + 1)) (β : BoundCtx (Ty κ) n) where
  names : Fin n → Option V
  distinct : Function.Injective names
  privateUnit : ∀ i, names i = none → β.get i = .unit

/-- Relabel the selected names while retaining the exact input record type. -/
def Captures.rename (I : Captures V β) (r : V ≃ W) : Captures W β where
  names i := (I.names i).map r
  distinct := (Option.map_injective r.injective).comp I.distinct
  privateUnit i eq := I.privateUnit i (by simpa using eq)

/-- The sole external φ exit is the explicit return `none`. -/
def Captures.named (I : Captures V β) (K : Type (u + 1)) (D : Fin 1 → Ty κ) :
    NamedFlat.Entry.Interface κ (Option V) (Option K) :=
  ⟨n, β, I.names, I.distinct, [none], D⟩

variable [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {P : FlatInstitution.Signature.{u, v} κ} {D : Fin 1 → Ty κ} {I : Captures V β} {Jc : Captures W β}

/-- The original normalized φ source with the actual checked open table. -/
structure Admitted (P : FlatInstitution.Signature.{u, v} κ) (I : Captures V β) (K : Type (u + 1))
    [DecidableEq K] (D : Fin 1 → Ty κ) where
  source : Graph V K P.Instr
  inputs : List V
  internal : Fin (blockCount source) → Ty κ
  admission : Admission source inputs I.names β internal D

/-- Package an original admission, including one produced from a transported
SSA arrival certificate. -/
def Admitted.ofAdmission {source : Graph V K P.Instr} {inputs : List V}
    {R : Fin (blockCount source) → Ty κ} (admitted : Admission source inputs I.names β R D) :
    Admitted P I K D :=
  ⟨source, inputs, R, admitted⟩

/-- Reuse the actual lowering's admitted lexical table. -/
def Admitted.toSSA (a : Admitted P I K D) : NamedFlat.Entry.SSA P (I.named K D).version :=
  .ofElaborated (Versioning.compile (lower a.source)) a.admission.elaborated a.admission.typed

/-- Each side may have different capture names and internal block labels,
with a common typed record and explicit return profile. -/
abbrev Sentence (P : FlatInstitution.Signature.{u, v} κ) (I : Captures V β) (Jc : Captures W β)
    (K J : Type (u + 1)) [DecidableEq K] [DecidableEq J] (D : Fin 1 → Ty κ) :=
  Admitted P I K D × Admitted P Jc J D

def toNamed (s : Sentence P I I K K D) : NamedFlat.Entry.SSASentence P (I.named K D).version :=
  (s.1.toSSA, s.2.toSSA)

/-- Use the two certified named tables in the existing typed-entry room. -/
def toFlat (s : Sentence P I Jc K J D) : EntryInstitution.Sentence P β :=
  ⟨1, D, s.1.toSSA.table, s.2.toSSA.table⟩

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "Record" => Ty.denote C (Region.packedInputType β.toList)

def Captures.store (I : Captures V β) (record : Record) : V → Value (Sigma C) :=
  fun name => NamedFlat.Entry.store I.names β record (some name)

/-- Observe the independent φ runner, with the institution's exit tag. -/
noncomputable def Admitted.observe (a : Admitted P I K D)
    (M : Model (κ := κ) Events P.Instr) (record : Record) :=
  PureCapture.sourceObservation M.raw a.source (I.store record)

def Satisfies (M : Model (κ := κ) Events P.Instr) (s : Sentence P I Jc K J D) : Prop :=
  ∀ record, TraceLE (s.1.observe M record) (s.2.observe M record)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
