module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs
public import Silmaril.Logic.ITree.Institution.Trace.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Named

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program (PackedEntry MismatchDirection)

variable {F : Type} {signature : PrimitiveSignature F}

private theorem replay_all {R : Type 1} (trace : Trace (Event signature.Request signature.Reply) R) :
    Replay signature.traceModel.step () trace := by
  induction trace with
  | «prefix» | request _ | result _ => trivial
  | exchange _ _ _ ih => exact ⟨(), trivial, ih⟩

theorem handledTrace_iff {R : Type 1} (tree : Tree (Event signature.Request signature.Reply) R)
    (trace : Trace (Event signature.Request signature.Reply) R) :
    HandledTrace signature.traceModel.step () tree trace ↔ HasTrace tree trace :=
  ⟨And.left, fun seen => ⟨seen, replay_all trace⟩⟩

private theorem sat_iff {R : Type 1} (source target : Tree (Event signature.Request signature.Reply) R) :
    TraceInstitution.Sat signature.traceModel ⟨R, source, HasTrace target⟩ ↔ TraceLE source target :=
  ⟨fun sat trace seen => sat () trivial trace ((handledTrace_iff source trace).mpr seen),
    fun included _ _ trace seen => included trace seen.1⟩

variable {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

theorem sat_refinementSentence_iff
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModel⟩
      (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord) ↔
    let l := leftEntry.observe leftAmbient leftRecord
    let r := rightEntry.observe rightAmbient rightRecord
    match direction with
    | .leftToRight => TraceLE l r
    | .rightToLeft => TraceLE r l := by
  cases direction <;> exact sat_iff _ _

-- Return tagging leaves the exchange history used by Replay unchanged.
private theorem replay_map {E : Type → Type} {A B : Type 1} {H : Type} (f : A → B) (step : Handler H E) (h : H)
    (trace : Trace E A) :
    Replay step h (trace.map f) ↔ Replay step h trace := by
  induction trace generalizing h with
  | «prefix» | request _ | result _ => rfl
  | exchange _ _ _ ih =>
    simp only [Trace.map, Replay]
    exact ⟨fun ⟨h', allowed, rest⟩ => ⟨h', allowed, (ih h').mp rest⟩,
      fun ⟨h', allowed, rest⟩ => ⟨h', allowed, (ih h').mpr rest⟩⟩

private theorem handled_inclusion_map_iff {E : Type → Type} {A B : Type 1} {f : A → B} {H : Type}
    (injective : Function.Injective f) (step : Handler H E) (h : H) (source target : Tree E A) :
    (∀ trace, HandledTrace step h (source >>= fun x => pure (f x)) trace →
      HasTrace (target >>= fun x => pure (f x)) trace) ↔
    (∀ trace, HandledTrace step h source trace → HasTrace target trace) := by
  have mapped (tree : Tree E A) (p : Trace E A) :=
    hasTrace_bind_pure_map_iff injective tree p
  constructor
  · intro includeSource p seen
    exact (mapped target p).mp (includeSource (p.map f)
      ⟨(mapped source p).mpr seen.1, (replay_map f step h p).mpr seen.2⟩)
  · intro includeSource p seen
    obtain ⟨pre, has, rfl⟩ := (hasTrace_bind_pure_iff _ _ _).mp seen.1
    exact (mapped target pre).mpr (includeSource pre ⟨has, (replay_map f step h pre).mp seen.2⟩)

private theorem packed_handled_inclusion_iff {H : Type}
    (step : Handler H (Event signature.Request signature.Reply)) (h : H)
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord)
    (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    (∀ trace, HandledTrace step h (leftEntry.observe leftAmbient leftRecord) trace →
      HasTrace (rightEntry.observe rightAmbient rightRecord) trace) ↔
    (∀ trace, HandledTrace step h (Finite.evaluate left.step (left.start input packet)) trace →
      HasTrace (Finite.evaluate right.step (right.start input packet)) trace) := by
  rw [leftEntry.observe_eq _ _ _ leftAgrees, rightEntry.observe_eq _ _ _ rightAgrees,
    handled_inclusion_map_iff
      Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective,
    Program.observe_eq, Program.observe_eq,
    handled_inclusion_map_iff Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.render_injective]

theorem refinementAtUnder_traceSat [DecidableEq F] (admits : ∀ key, signature.Reply key → Bool)
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord)
    (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAtUnder? admits right input packet = true ↔
      TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModelUnder admits⟩
        (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) := by
  let step := Finite.replyHandler admits
  let source := leftEntry.observe leftAmbient leftRecord
  let target := rightEntry.observe rightAmbient rightRecord
  have sat : TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModelUnder admits⟩
      (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) ↔
      ∀ (trace : Trace (Event signature.Request signature.Reply) _), HandledTrace step () source trace → HasTrace target trace :=
    ⟨fun h p hp => h () trivial p hp, fun h x _ => by cases x; exact h⟩
  rw [sat, packed_handled_inclusion_iff step () packet leftEntry rightEntry _ _ _ _ leftAgrees rightAgrees]
  exact Finite.compareUnder_iff admits _ _ left.mem_states right.mem_states _ _ _ _

theorem refinementAtWithHandler_traceSatAt [DecidableEq F] {H : Type} [DecidableEq H] [Fintype H]
    (advance : H → ∀ key, signature.Reply key → Option H) (initial : H → Bool) (h : H)
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord)
    (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAtWithHandler? advance right input packet h = true ↔
      TraceInstitution.SatAt (signature.traceModelWithHandler advance initial)
        (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) h := by
  let step := Finite.statefulReplyHandler advance
  change _ ↔ ∀ trace, HandledTrace step h (leftEntry.observe leftAmbient leftRecord) trace →
    HasTrace (rightEntry.observe rightAmbient rightRecord) trace
  rw [packed_handled_inclusion_iff step h packet leftEntry rightEntry _ _ _ _ leftAgrees rightAgrees]
  exact Finite.compareWithHandler_iff advance _ _ _ left.mem_states right.mem_states Finset.mem_univ _ _ _ _ h

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution
