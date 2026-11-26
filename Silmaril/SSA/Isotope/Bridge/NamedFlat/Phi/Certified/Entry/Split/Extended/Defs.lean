module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Thms

/-! # View a generated split at its actual extended capture context -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input reindex)
open PureCapture.Local.Split (Generated extendedNames extendedTypes originalSlots)

universe u v

variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}

/-- Check the layout requirements of the supplied-entry institution on the
exact names and types returned by split generation. -/
def ExtendedLayout (plan : Plan V W K J) (I : Captures V β) (extra : List (Option W × Ty κ)) : Prop :=
  (∀ i j, extendedNames plan I.names extra i = extendedNames plan I.names extra j → i = j) ∧
    (∀ i, extendedNames plan I.names extra i = none → (extendedTypes β extra).get i = .unit)

instance [DecidableEq W] [DecidableEq κ]
    (plan : Plan V W K J) (I : Captures V β) (extra : List (Option W × Ty κ)) :
    Decidable (ExtendedLayout plan I extra) := by
  unfold ExtendedLayout
  infer_instance

def ExtendedLayout.captures {plan : Plan V W K J} {I : Captures V β} {extra : List (Option W × Ty κ)}
    (layout : ExtendedLayout plan I extra) : Captures W (extendedTypes β extra) :=
  ⟨extendedNames plan I.names extra, fun _ _ => layout.1 _ _, layout.2⟩

variable {I : Captures V β} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {P : FlatInstitution.Signature.{u, v} κ}

/-- Keep the actual checked split admission at the larger entry profile. -/
def Admitted.ofExtended (original : Admitted P I K D) (plan : Plan V W K J)
    (result : Generated plan original.source original.inputs I.names β D)
    (layout : ExtendedLayout plan I result.extra) : Admitted P layout.captures J D :=
  .ofAdmission result.admitted

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

/-- Recover the original record using the checked embedding of retained
slots. The larger record supplies the values of extra fields. -/
def retainedRecord (β : BoundCtx (Ty κ) n) (extra : List (Option W × Ty κ))
    (record : Input (extendedTypes β extra)) : Input β :=
  reindex (originalSlots β extra) record

/-- The actual packed program of the admitted table at its own typed record. -/
noncomputable def Admitted.observePacked (a : Admitted P I K D)
    (M : Model (κ := κ) Events P.Instr) (record : Input β) (ambient : Env (Sigma C)) :=
  region M.raw (extend ambient (encodeValue C _ record)) (Program.ofCFGEntry a.toSSA.table.typed).code

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
