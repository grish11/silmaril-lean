module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Satisfaction

/-! # Satisfaction of the checked translation at the same typed record -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open CategoryTheory (Discrete)
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  {I : Captures V β} {Jc : Captures W β} {D : Fin 1 → Ty κ}
  [AtomValues κ] [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "A" => Region.packedInputType β.toList
local notation "Record" => Ty.denote C A

theorem Captures.store_rename (I : Captures V β) (rename : V ≃ W) (record : Record) :
    (I.rename rename).store record = I.store record ∘ rename.symm :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.store_rename I rename record

/-- Each supplied slot agrees with the independent runner's capture projection. -/
theorem Captures.inputEnv_eq (I : Captures V β) (record : Record) (i : Fin n) :
    NamedFlat.Entry.inputEnv β record i.val = captureEnv I.names (I.store record) i.val :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.capture_agrees I record i

/-- A source store can supply additional names. The typed entry calculation
depends only on the values in the selected capture slots. -/
theorem Admitted.observe_toFlat_of_capture (a : Admitted P I K D)
    (M : Model (κ := κ) Events P.Instr) (record : Record) (ambient : Env (Sigma C))
    (store : V → Value (Sigma C))
    (agrees : ∀ i : Fin n, NamedFlat.Entry.inputEnv β record i.val = captureEnv I.names store i.val) :
    PureCapture.sourceObservation M.raw a.source store =
      region M.raw (extend ambient (encodeValue C A record))
        (Program.ofCFGEntry a.toSSA.table.typed).code :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.observe_entry_of_capture
    a M record ambient store agrees

/-- Evaluation of the translated typed table uses exactly the supplied record
and preserves the independent φ observation. -/
theorem Admitted.observe_toFlat (a : Admitted P I K D) (M : Model (κ := κ) Events P.Instr)
    (record : Record) (ambient : Env (Sigma C)) :
    a.observe M record = region M.raw (extend ambient (encodeValue C A record))
      (Program.ofCFGEntry a.toSSA.table.typed).code :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.observe_entry a M record ambient

/-- The independent φ runner agrees with the named observation at exactly the
same supplied typed input record and the singleton numbered exit. -/
theorem Admitted.observe_toSSA (a : Admitted P I K D) (M : Model (κ := κ) Events P.Instr)
    (record : Record) :
    a.toSSA.observe M record = a.observe M record :=
  (NamedFlat.Entry.SSA.observe_tree M a.toSSA record (fun _ => .unit)).trans
    (a.observe_toFlat M record (fun _ => .unit)).symm

/-- For a common named interface, the original φ comparison translates to
the admitted named lexical comparison with satisfaction in both directions. -/
theorem toNamed_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : Sentence P I I K K D) :
    NamedFlat.Entry.ssaSatisfies M (toNamed s) ↔ Satisfies M s := by
  change (∀ record : Record, TraceLE (s.1.toSSA.observe M record) (s.2.toSSA.observe M record)) ↔
    Satisfies M s
  exact forall_congr' fun record => by rw [s.1.observe_toSSA, s.2.observe_toSSA]

/-- The two sides may select different names for their common record fields.
Each uses its own checked named table and the same typed exit profile. -/
theorem toFlat_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : Sentence P I Jc K J D) :
    EntryInstitution.Satisfies Events M (toFlat s) ↔ Satisfies M s :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.flat_satisfies M s

/-- Reuse the existing institutional packing of the admitted entry tables. -/
theorem toPacked_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : Sentence P I Jc K J D) :
    (PackedInstitution.room Events P A).Sat (Discrete.mk M)
      (EntryInstitution.packSentence (toFlat s)) ↔ Satisfies M s :=
  (EntryInstitution.packing_satisfaction Events M _).trans (toFlat_satisfies_iff M s)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
