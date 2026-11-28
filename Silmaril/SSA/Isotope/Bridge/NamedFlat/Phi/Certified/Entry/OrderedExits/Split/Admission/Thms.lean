module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Admission.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

universe u v
variable {κ V W Reg K : Type (u + 1)}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context} {Events : Type u → Type u}
  {plan : Plan V W K K} {a : Admission P I fields C}

local notation "Atoms" => AtomValues.carrier (κ := κ)

/-- The generated typed admission inherits the independent source observation
at the supplied record and ordered exits. -/
theorem GeneratedSplit.observe_eq (split : GeneratedSplit plan a)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :
    a.observe M record = split.target.observe M record :=
  a.split_observe_eq plan split.target split.checked split.exits M record

variable [DecidableEq Reg]

/-- Use the accepted reverse checker outputs on the original and generated
tables to compare the actual emitted mutable runs. -/
theorem GeneratedSplit.reverse_eq (split : GeneratedSplit plan a)
    (left : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (right : NamedFlat.Entry.Reverse.Lowered I fields split.target.code)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :
    NamedFlat.Entry.LiveOut.observe M I fields left.source record =
      NamedFlat.Entry.LiveOut.observe M I fields right.source record :=
  a.split_reverse_eq plan split.target split.checked split.exits left right M record

/-- Use successful typed re-admissions of the actual mutable graphs to
compare the packed executions. -/
theorem GeneratedSplit.roundTrip_eq (split : GeneratedSplit plan a)
    (left : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (right : NamedFlat.Entry.Reverse.Lowered I fields split.target.code)
    (leftRecompiled : NamedFlat.Entry.LiveOut.Admission P I fields left.source)
    (rightRecompiled : NamedFlat.Entry.LiveOut.Admission P I fields right.source)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    region M.raw (extend ambient (encodeValue Atoms _ record)) leftRecompiled.program.code =
      region M.raw (extend ambient (encodeValue Atoms _ record)) rightRecompiled.program.code :=
  a.split_roundTrip_eq plan split.target split.checked split.exits left right leftRecompiled rightRecompiled
    M record ambient

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
