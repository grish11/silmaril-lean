module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Packed.Thms

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Elgot.ITree (HasTrace TraceLE eq_iff_traceLE hasTrace_bind_pure_map_iff)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope (BoundCtx)
open Silmaril (HasTy)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  (program : Program signature inputs outputs)

/-- An accepted elaboration and exact structural typing expose the same weak
tree through the packed dispatcher when the supplied record agrees with the
named input store. The ordered exit and its typed payload are tagged together. -/
theorem packed_observe {n : Nat} {β : BoundCtx PacketType n}
    (input : Fin a) (packet : Denote (inputs input)) (captures : Fin n → Register)
    {R : Fin (program.compile input).blocks.length → PacketType} {L : Fin program.exits.length → PacketType}
    {target : FiniteCFG F (program.compile input).blocks.length program.exits.length n}
    (accepted : elaborate (program.compile input) program.exits captures = some target)
    (typed : letI := signature.typing; target.HasType β R L)
    (ambient original : Silmaril.Isotope.LambdaSSA.Semantics.Env Atom)
    (inputsAgree : ∀ i, original i.val = Program.store (inputs := inputs) input packet (captures i)) :
    region signature.primitive (Silmaril.Isotope.LambdaSSA.Semantics.extend ambient (Capture.packEnv n original))
        ((letI := signature.typing; FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) =
      (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) := by
  let _ := signature.typing
  rw [Capture.packed_context_tree,
    ← run_tree signature.primitive _ _ captures accepted (Program.store (inputs := inputs) input packet) original inputsAgree]
  rfl

/-- Together with the packed entry equations this gives an exact packed
comparison. The output tag preserves both the exit position and payload. -/
theorem refinementAt?_iff_packedOutput [DecidableEq F] (right : Program signature inputs outputs)
    (input : Fin a) (packet : Denote (inputs input)) :
    program.refinementAt? right input packet = true ↔
      TraceLE (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result))
        (right.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  (program.refinementAt?_iff right input packet).trans
    (TraceLE.bind_pure_iff
      Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective).symm

/-- Using `packed_observe` for each admitted execution gives a decision for
equality of the actual packed weak trees. -/
theorem weakEqAt?_iff_packedOutput [DecidableEq F] (right : Program signature inputs outputs)
    (input : Fin a) (packet : Denote (inputs input)) :
    program.weakEqAt? right input packet = true ↔
      (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) =
        (right.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) := by
  simp only [weakEqAt?, Bool.and_eq_true, refinementAt?_iff_packedOutput, eq_iff_traceLE]

theorem PackedEntry.observe_eq {p : Program signature inputs outputs} {input : Fin a}
    (entry : PackedEntry p input) (packet : Denote (inputs input))
    (ambient original : Semantics.Env Atom) (agrees : entry.recordAgrees packet original) :
    entry.observe ambient original =
      (p.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  p.packed_observe input packet entry.captures entry.accepted entry.typed ambient original agrees

/-- Independent start packets are compared through their actual checked
packed dispatchers and the same ordered result encoding. -/
theorem refinementBetween?_iff_packed [DecidableEq F]
    {c : Nat} {rightInputs : Fin c → PacketType} (right : Program signature rightInputs outputs)
    {leftInput : Fin a} {rightInput : Fin c}
    (leftPacket : Denote (inputs leftInput)) (rightPacket : Denote (rightInputs rightInput))
    (leftEntry : PackedEntry program leftInput) (rightEntry : PackedEntry right rightInput)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees leftPacket leftRecord)
    (rightAgrees : rightEntry.recordAgrees rightPacket rightRecord) :
    program.refinementBetween? right leftInput leftPacket rightInput rightPacket = true ↔
      TraceLE (leftEntry.observe leftAmbient leftRecord) (rightEntry.observe rightAmbient rightRecord) := by
  rw [leftEntry.observe_eq _ _ _ leftAgrees, rightEntry.observe_eq _ _ _ rightAgrees,
    TraceLE.bind_pure_iff
      Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective]
  exact program.refinementBetween?_iff right leftInput leftPacket rightInput rightPacket

/-- Transport a directed witness at independent starts through both actual
packed runners, retaining the ordered exit tag inside the packed result. -/
theorem explainRefinementBetween?_sound_packed [DecidableEq F]
    {c : Nat} {rightInputs : Fin c → PacketType} {right : Program signature rightInputs outputs}
    {leftInput : Fin a} {rightInput : Fin c}
    {leftPacket : Denote (inputs leftInput)} {rightPacket : Denote (rightInputs rightInput)}
    {trace : ObservationTrace signature}
    (found : program.explainRefinementBetween? right leftInput leftPacket rightInput rightPacket = some trace)
    (leftEntry : PackedEntry program leftInput) (rightEntry : PackedEntry right rightInput)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees leftPacket leftRecord)
    (rightAgrees : rightEntry.recordAgrees rightPacket rightRecord) :
    HasTrace (leftEntry.observe leftAmbient leftRecord) (trace.map FiniteCFG.packedTreeOutput) ∧
      ¬ HasTrace (rightEntry.observe rightAmbient rightRecord) (trace.map FiniteCFG.packedTreeOutput) := by
  rw [leftEntry.observe_eq _ _ _ leftAgrees, rightEntry.observe_eq _ _ _ rightAgrees]
  simpa only [hasTrace_bind_pure_map_iff
    Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective] using
    (program.explainRefinementBetween?_spec right leftInput leftPacket rightInput rightPacket).2 trace found

theorem weakEq?_iff_packedOutput [DecidableEq F] (right : Program signature inputs outputs) :
    program.weakEq? right = true ↔ ∀ input packet,
      (program.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) =
        (right.observe input packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  (program.weakEq?_iff right).trans <| forall_congr' fun input => forall_congr' fun packet =>
    (program.weakEqAt?_iff right input packet).symm.trans
      (program.weakEqAt?_iff_packedOutput right input packet)

/-- Compare every entry's checked packed execution on the records supplied
for each typed input. Ordered exit tags are part of the equality. -/
theorem weakEq?_iff_packed [DecidableEq F] (right : Program signature inputs outputs)
    (leftEntry : ∀ input, PackedEntry program input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    program.weakEq? right = true ↔ ∀ input packet,
      (leftEntry input).observe leftAmbient (leftRecord input packet) =
        (rightEntry input).observe rightAmbient (rightRecord input packet) := by
  simp only [PackedEntry.observe_eq _ _ _ _ (leftAgrees _ _),
    PackedEntry.observe_eq _ _ _ _ (rightAgrees _ _), weakEq?_iff_packedOutput]

theorem firstMismatch?_sound_packed [DecidableEq F] {right : Program signature inputs outputs}
    {p : PacketAt inputs} (found : program.firstMismatch? right = some p)
    (leftEntry : PackedEntry program p.1) (rightEntry : PackedEntry right p.1)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees p.2 leftRecord) (rightAgrees : rightEntry.recordAgrees p.2 rightRecord) :
    leftEntry.observe leftAmbient leftRecord ≠ rightEntry.observe rightAmbient rightRecord := by
  rw [leftEntry.observe_eq _ _ _ leftAgrees, rightEntry.observe_eq _ _ _ rightAgrees]
  exact mt (program.weakEqAt?_iff_packedOutput right p.1 p.2).mpr
    (mt (program.weakEqAt?_iff right p.1 p.2).mp (program.firstMismatch?_sound found))

/-- Transport the particular distinguishing trace to checked packed
execution. The terminal result uses the dispatcher's ordered exit tag. -/
theorem explainMismatch?_sound_packed [DecidableEq F] {right : Program signature inputs outputs}
    {w : Mismatch signature inputs} (found : program.explainMismatch? right = some w)
    (leftEntry : PackedEntry program w.packet.1) (rightEntry : PackedEntry right w.packet.1)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees w.packet.2 leftRecord)
    (rightAgrees : rightEntry.recordAgrees w.packet.2 rightRecord) :
    w.direction.distinguishes (leftEntry.observe leftAmbient leftRecord)
      (rightEntry.observe rightAmbient rightRecord) (w.trace.map FiniteCFG.packedTreeOutput) := by
  have sound := ((program.explainMismatch?_spec right).2 w found).2
  rw [leftEntry.observe_eq _ _ _ leftAgrees, rightEntry.observe_eq _ _ _ rightAgrees]
  cases direction : w.direction <;> simpa only [direction, MismatchDirection.distinguishes,
    hasTrace_bind_pure_map_iff
      Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective] using sound

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program
