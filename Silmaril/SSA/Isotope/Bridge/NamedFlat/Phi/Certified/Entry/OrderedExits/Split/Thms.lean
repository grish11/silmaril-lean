module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

universe u v w

theorem checkSplit_sound {V W K J : Type w} {F : Type v}
    [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [DecidableEq F]
    {plan : Plan V W K J} {original : Graph V K F} {split : Graph W J F}
    (ok : checkSplit plan original split = true) : CheckedSplit plan original split := by
  simp only [checkSplit, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ⟨ok.1.1, ok.1.2, ok.2⟩

variable {κ V W Reg K : Type (u + 1)}
  [DecidableEq V] [DecidableEq W] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context} {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)

omit [DecidableEq Reg] in
/-- A checked split preserves the independent source execution on the same
typed record. The capture names follow the register equivalence. The exit
list is fixed positionally by the label embedding. -/
theorem Admission.split_observe_eq (plan : Plan V W K K) (a : Admission P I fields C)
    (b : Admission P I fields (C.rename plan.register)) (checked : CheckedSplit plan a.source b.source)
    (exits : I.exits.map (Option.map plan.label) = I.exits)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :
    a.observe M record = b.observe M record :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.observe_eq
    plan a b checked exits M record

/-- The two actual emitted mutable graphs agree at the original input and
ordered exits, including the projected live-out values. -/
theorem Admission.split_reverse_eq (plan : Plan V W K K) (a : Admission P I fields C)
    (b : Admission P I fields (C.rename plan.register)) (checked : CheckedSplit plan a.source b.source)
    (exits : I.exits.map (Option.map plan.label) = I.exits)
    (left : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (right : NamedFlat.Entry.Reverse.Lowered I fields b.code)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :
    NamedFlat.Entry.LiveOut.observe M I fields left.source record =
      NamedFlat.Entry.LiveOut.observe M I fields right.source record :=
  (a.observe_reverse left M record).symm.trans
    ((a.split_observe_eq plan b checked exits M record).trans (b.observe_reverse right M record))

/-- The actual packed programs from the two successful re-admissions agree
at the same input, exit order and live-out profile. -/
theorem Admission.split_roundTrip_eq (plan : Plan V W K K) (a : Admission P I fields C)
    (b : Admission P I fields (C.rename plan.register)) (checked : CheckedSplit plan a.source b.source)
    (exits : I.exits.map (Option.map plan.label) = I.exits)
    (left : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (right : NamedFlat.Entry.Reverse.Lowered I fields b.code)
    (leftRecompiled : NamedFlat.Entry.LiveOut.Admission P I fields left.source)
    (rightRecompiled : NamedFlat.Entry.LiveOut.Admission P I fields right.source)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    region M.raw (extend ambient (encodeValue Atoms _ record)) leftRecompiled.program.code =
      region M.raw (extend ambient (encodeValue Atoms _ record)) rightRecompiled.program.code :=
  (a.observe_roundTrip left leftRecompiled M record ambient).symm.trans
    ((a.split_observe_eq plan b checked exits M record).trans
      (b.observe_roundTrip right rightRecompiled M record ambient))

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
