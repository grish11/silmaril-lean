module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Reverse.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

universe u v
variable {κ V K Reg Label : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  [DecidableEq V] [DecidableEq K] [DecidableEq Reg] [DecidableEq Label] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {C : Captures V β} {Events : Type u → Type u}
  {I : ReverseInterface κ Reg Label n}

local notation "A" => AtomValues.carrier (κ := κ)

/-- The independent predecessor-snapshot evaluator and the emitted mutable
runner agree at the same supplied record. The selected exit fields appear
in the order of the φ result's explicit return record. -/
theorem Admitted.observe_reverse (a : Admitted P C K I.external) (lowered : ReverseLowered I a)
    (M : Model (κ := κ) Events P.Instr) (record : Input β) :
    a.observe M record =
      NamedFlat.Entry.LiveOut.observe M (I.named β) (fun _ => I.liveOut) lowered.source record :=
  (a.observe_toFlat M record (fun _ => .unit)).trans
    (lowered.packed_observe M a.toSSA.table.typed record (fun _ => .unit))

/-- Reuse a successful ordinary typed re-admission of the emitted RTL.
The reversion may use its own internal packet profile. -/
theorem Admitted.observe_reverse_roundTrip (a : Admitted P C K I.external)
    (lowered : ReverseLowered I a)
    (recompiled : NamedFlat.Entry.LiveOut.Admission P (I.named β) (fun _ => I.liveOut) lowered.source)
    (M : Model (κ := κ) Events P.Instr) (record : Input β) (ambient : Env (Sigma A)) :
    a.observe M record = region M.raw (extend ambient (encodeValue A _ record)) recompiled.program.code :=
  (a.observe_toFlat M record ambient).trans
    (lowered.packed_roundTrip M a.toSSA.table.typed recompiled record ambient)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
