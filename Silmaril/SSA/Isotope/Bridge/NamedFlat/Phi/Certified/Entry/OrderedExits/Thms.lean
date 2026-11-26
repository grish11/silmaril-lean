module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

universe u v
variable {κ V Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context} {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)

omit [DecidableEq Reg] in
/-- The actual typed packed table preserves the predecessor-snapshot
observation at the declared exit positions. -/
theorem Admission.observe_packed (a : Admission P I fields C) (M : Model (κ := κ) Events P.Instr)
    (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    a.observe M record =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry a.typed).code :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.observe_packed a M record ambient

/-- For accepted reverse readback, the emitted mutable run has the same
ordered exit observation, including the selected final register fields. -/
theorem Admission.observe_reverse (a : Admission P I fields C)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :
    a.observe M record = NamedFlat.Entry.LiveOut.observe M I fields lowered.source record :=
  (a.observe_packed M record (fun _ => .unit)).trans
    (lowered.packed_observe M a.typed record (fun _ => .unit))

/-- After successful ordinary typed re-admission at its supplied block
profiles, the actual packed reversion preserves those same observations. -/
theorem Admission.observe_roundTrip (a : Admission P I fields C)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (recompiled : NamedFlat.Entry.LiveOut.Admission P I fields lowered.source)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    a.observe M record = region M.raw (extend ambient (encodeValue Atoms _ record)) recompiled.program.code :=
  (a.observe_packed M record ambient).trans (lowered.packed_roundTrip M a.typed recompiled record ambient)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
