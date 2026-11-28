module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
public import Silmaril.Semantics.ITree.Reindex.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (HasTrace HandledTrace TraceLE eq_iff_traceLE)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree.TraceInstitution (Sat)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature Program)
open NamedFlat.Entry.Record (Input)
open NamedFlat.Entry.Reverse (observeAttached)

variable {κ V Reg K : Type 1} [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{0, 0} κ}
  {I : NamedFlat.Entry.Interface κ Reg (Option K)} {fields : Option K → List (Reg × Ty κ)}
  {C : Captures V I.context} {signature : PrimitiveSignature P.Instr}
  {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}


variable {source : Admission P I fields C}
  {M : Model (κ := κ) (Event signature.Request signature.Reply) P.Instr} {record : Input I.context}
  {packet : Denote (inputs input)} {observeResult : Transfer (Sigma (AtomValues.carrier (κ := κ))) → Transfer Atom}
  {leftEntry : Program.PackedEntry left input} {rightEntry : Program.PackedEntry right input}
  {leftAmbient rightAmbient leftRecord rightRecord : Env Atom} {ambient : Env (Sigma (AtomValues.carrier (κ := κ)))}

/-- The public packed tree is the observation of the independent φ runner. -/
theorem PublicMatch.source_eq
    (matchEntry : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient) :
    observeResult <$> source.observe M record = leftEntry.observe leftAmbient leftRecord :=
  (congrArg (Functor.map observeResult)
    (source.observe_roundTrip matchEntry.lowered matchEntry.recompiled M record ambient)).trans matchEntry.observes

/-- The same public packed tree is the observation of the emitted mutable
RTL, with the ordered reads attached at its exits. -/
theorem PublicMatch.rtl_eq
    (matchEntry : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient) :
    observeResult <$> observeAttached M I fields matchEntry.lowered.source record =
      leftEntry.observe leftAmbient leftRecord :=
  (congrArg (Functor.map observeResult) (source.observe_attached matchEntry.lowered M record)).symm.trans
    matchEntry.source_eq

/-- For each policy and initial state the same trace and replay are
available on both sides of the checked execution square. -/
theorem PublicMatch.handledTrace_iff
    (matchEntry : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient)
    (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature)
    (state : policy.State) (trace : Program.ObservationTrace signature) :
    HandledTrace policy.step state (observeResult <$> source.observe M record) trace ↔
      HandledTrace policy.step state
        (observeResult <$> observeAttached M I fields matchEntry.lowered.source record) trace := by
  let same := eq_iff_traceLE.mp (matchEntry.source_eq.trans matchEntry.rtl_eq.symm)
  exact ⟨same.1.handledTrace, same.2.handledTrace⟩

section Comparison

variable {W : Type 1} [DecidableEq W] {D : Captures W I.context}
  {target : Admission P I fields D}

/-- Each handler gives the same directed judgment on the independent
φ observations and on the actual checked public packed entries. -/
theorem PublicMatch.sat_packed_iff
    (l : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient)
    (r : PublicMatch target M record packet observeResult rightEntry rightAmbient rightRecord ambient)
    (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature) :
    Sat policy
      ⟨_, observeResult <$> source.observe M record, HasTrace (observeResult <$> target.observe M record)⟩ ↔
    Sat policy (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) := by
  erw [l.source_eq, r.source_eq]
  rfl

/-- The existing all-replies verdict decides directed handled-trace
refinement of the independent source runners at the aligned packet.
Each shared policy keeps its own initial predicate and replay relation. -/
theorem refinementAt?_iff_source [DecidableEq P.Instr]
    (l : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient)
    (r : PublicMatch target M record packet observeResult rightEntry rightAmbient rightRecord ambient) :
    left.refinementAt? right input packet = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
        Sat policy
          ⟨_, observeResult <$> source.observe M record, HasTrace (observeResult <$> target.observe M record)⟩ :=
  (Program.refinementAt?_iff_valid_traceSat packet leftEntry rightEntry
    leftAmbient rightAmbient leftRecord rightRecord l.agrees r.agrees).trans
      (forall_congr' fun policy => (l.sat_packed_iff r policy).symm)

/-- An injective result encoding also reflects the trace order on the
original φ runtime values, including their packed exit tags. -/
theorem refinementAt?_iff_traceLE [DecidableEq P.Instr]
    (l : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient)
    (r : PublicMatch target M record packet observeResult rightEntry rightAmbient rightRecord ambient)
    (injective : Function.Injective observeResult) :
    left.refinementAt? right input packet = true ↔ TraceLE (source.observe M record) (target.observe M record) :=
  (left.refinementAt?_iff_packedOutput right input packet).trans <|
    (Iff.of_eq (congrArg₂ TraceLE ((leftEntry.observe_eq packet _ _ l.agrees).symm.trans l.source_eq.symm)
      ((rightEntry.observe_eq packet _ _ r.agrees).symm.trans r.source_eq.symm))).trans
      (by simpa only [← map_eq_pure_bind] using TraceLE.bind_pure_iff injective)

/-- At each shared policy the source and actual attached RTL give the same
directed verdict. The aligned re-admitted packed entries give that verdict
by the same equalities. -/
theorem PublicMatch.sat_rtl_iff
    (l : PublicMatch source M record packet observeResult leftEntry leftAmbient leftRecord ambient)
    (r : PublicMatch target M record packet observeResult rightEntry rightAmbient rightRecord ambient)
    (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature) :
    Sat policy
      ⟨_, observeResult <$> source.observe M record, HasTrace (observeResult <$> target.observe M record)⟩ ↔
    Sat policy
      ⟨_, observeResult <$> observeAttached M I fields l.lowered.source record,
        HasTrace (observeResult <$> observeAttached M I fields r.lowered.source record)⟩ := by
  erw [l.source_eq, r.source_eq, l.rtl_eq, r.rtl_eq]

end Comparison

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
