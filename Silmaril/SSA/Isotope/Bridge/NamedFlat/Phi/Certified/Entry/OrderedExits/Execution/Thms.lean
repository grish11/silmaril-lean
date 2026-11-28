module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Exact.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Execution.Thms

/-! # Whole-run semantics of checked body-local ordered φ lowering -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree singletonDenote_tree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)
open NamedFlat.Entry.Reverse (Lowered Registers Register lowerWith lowerCheckedWith
  lowerCheckedWith_emitted observeAttached observeAttached_eq)

universe u v
variable {κ V Reg K : Type (u + 1)}
  [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context} {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "Exit" => Region.packedExitType
  (List.ofFn (NamedFlat.Entry.Interface.external (NamedFlat.Entry.LiveOut.exitInterface I fields)))

/-- Exact typed readback connects the actual attached RTL runner to the
independent predecessor-snapshot φ runner. No rank or fuel is involved. -/
theorem Admission.observe_attached (a : Admission P I fields C) (output : Lowered I fields a.code)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) :
    a.observe M record = observeAttached M I fields output.source record :=
  (a.observe_reverse output M record).trans (observeAttached_eq M I fields output.source record).symm

omit [DecidableEq Reg] in
/-- Evaluate the actual typed packed program under the compatible primitive
interpretation. The encoded result keeps the original ordered exit tag. -/
theorem Admission.observe_denote (a : Admission P I fields C)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    a.observe M record =
      ((show ModelTree Events (Ty.denote Atoms Exit) from ((Program.ofCFGEntry a.typed).denote M).of record) >>=
        fun value => pure (0, encodeValue Atoms Exit value)) :=
  let _ := M.instructions
  (a.observe_packed M record ambient).trans
    (singletonDenote_tree M.raw M.compatible (Program.ofCFGEntry a.typed).typed record ambient).symm

/-- Conditional whole-run agreement for actual body-local reverse emission.
The checker supplies packet closure and the exact flat table with attached
ordered exits. The one supplied record initializes both capture stores,
and the same model interprets primitives along all cyclic paths. -/
theorem Admission.bodyLocal_commutes [DecidableEq P.Instr] (a : Admission P I fields C)
    {entry : Registers Reg} {locals : Fin _ → Nat → Reg} {labels : Fin _ → Option K}
    {output : Lowered I fields a.code}
    (accepted : lowerCheckedWith I fields entry locals labels a.code = some output)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    lowerWith entry locals I.names labels (fun i => I.exits[i]) a.code = some output.source ∧
      a.observe M record = observeAttached M I fields output.source record ∧
      a.observe M record =
        ((show ModelTree Events (Ty.denote Atoms Exit) from ((Program.ofCFGEntry a.typed).denote M).of record) >>=
          fun value => pure (0, encodeValue Atoms Exit value)) :=
  ⟨lowerCheckedWith_emitted accepted, a.observe_attached output M record, a.observe_denote M record ambient⟩

/-- A successful typed re-admission of the same attached table gives the
corresponding encoded typed result at the original ordered exit interface. -/
theorem Admission.observe_recompiled_denote (a : Admission P I fields C)
    (output : Lowered I fields a.code)
    (recompiled : NamedFlat.Entry.LiveOut.Admission P I fields output.source)
    (M : Model (κ := κ) Events P.Instr) (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    a.observe M record =
      ((show ModelTree Events (Ty.denote Atoms Exit) from (recompiled.program.denote M).of record) >>=
        fun value => pure (0, encodeValue Atoms Exit value)) :=
  (a.observe_reverse output M record).trans (recompiled.denote_tree M record ambient).symm

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
