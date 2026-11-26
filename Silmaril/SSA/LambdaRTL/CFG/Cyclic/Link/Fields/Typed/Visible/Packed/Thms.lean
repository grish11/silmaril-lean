module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Packed.Thms

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Elgot.ITree (TraceLE eq_iff_traceLE)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
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

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program
