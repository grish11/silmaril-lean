module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {out : Cfg TargetOp (SourceLabel carried result) Input [result]}

/-- On any typed label family, the swap retains the branch decision and frame. -/
theorem Typed.swapAt?_eval {Labels : List Width → Type} {Result : List Width} {insertion : Nat}
    {before after : Block TargetOp Labels Γ Result}
    (swapped : Typed.swapAt? insertion before = some after) (env : Env Γ) :
    after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.swapAt_typed_eval swapped env

/-- Compare typed argument packets for all occurrences, including an untaken edge. -/
theorem Typed.swapAt?_edgePackets {Labels : List Width → Type} {Result : List Width} {insertion : Nat}
    {before after : Block TargetOp Labels Γ Result}
    (swapped : Typed.swapAt? insertion before = some after) (env : Env Γ) :
    after.eval evalOp Typed.edgePackets env = before.eval evalOp Typed.edgePackets env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.swapAt_edgePackets swapped env

/-- Exact agreement of entry code and block transfers gives agreement at every block fuel. -/
theorem Typed.run_eq_of_frames {Labels : List Width → Type} {Result : List Width}
    {source target : Cfg TargetOp Labels Input Result} (input : Env Input)
    (entry : target.entry = source.entry)
    (block : ∀ frame : Frame Labels,
      (target.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        (source.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input))
    (fuel : Nat) : target.run evalOp fuel input = source.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.run_eq_of_frames input entry block fuel

/-- The label-polymorphic swap specializes to the source-header swap. -/
theorem Typed.swapAt?_source (insertion : Nat) (code : Block TargetOp (SourceLabel carried result) Γ [result]) :
    Typed.swapAt? insertion code = Header.swapAt? insertion code :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.swapAt_source insertion code

/-- The local swap preserves the branch decision and the complete typed frame
or return value, for every header environment. -/
theorem swapAt?_eval {insertion : Nat}
    {before after : Block TargetOp (SourceLabel carried result) Γ [result]}
    (swapped : swapAt? insertion before = some after) (env : Env Γ) :
    after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.swapAt?_eval swapped env

/-- Successful emission uses the original CFG's binding sites and chosen cut. -/
theorem pickAndEmit?_spec
    {emit : Cfg TargetOp (SourceLabel carried result) Input [result] →
      Nat → Point (SourceLabel carried result) →
      Option (Cfg TargetOp (SourceLabel carried result) Input [result])}
    (picked : pickAndEmit? g index emit = some (cut, out)) :
    (∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut) ∧
    emit (lower g) index cut = some out :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndEmit?_spec picked

/-- The synthesized chooser reports an actual legal cut in the source CFG. -/
theorem chooseCut_sound {operands : List (Point (SourceLabel carried result))}
    {uses : List (Use (SourceLabel carried result))}
    (selected : chooseCut? g operands uses = some cut) :
    cut ∈ candidateCuts (lower g) blocks ∧ Legal (lower g) operands uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.chooseCut_sound selected

section HeaderReplacement

variable {cfg : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]}
variable (agrees : ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
  (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env)
include agrees

/-- Replacing a header with pointwise equal evaluation preserves every transfer. -/
theorem withHeader_frames (input : Env Input) :
    (withHeader cfg header).entry = cfg.entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      ((withHeader cfg header).block frame.label).eval evalOp (fun term env => term.eval env)
          (frame.args.append input) =
        (cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.withHeader_frames agrees input

theorem withHeader_run_eq (input : Env Input) (fuel : Nat) :
    (withHeader cfg header).run evalOp fuel input = cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.withHeader_run_eq agrees input fuel

theorem withHeader_denotePart (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (withHeader cfg header)).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.withHeader_denotePart agrees input

end HeaderReplacement

/-- The emitted move uses the synthesized legal cut for the actual binding.
The adjacent earlier cut retains its index after removal. -/
theorem pickAndMove?_placement (picked : pickAndMove? g index = some (cut, out)) :
    cut.block = headerId ∧ cut.cut + 1 = index ∧ afterRemoval index cut.cut = cut.cut ∧
    cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_placement picked

/-- A selected cut outside the supported adjacent earlier position is refused,
including either cut that reinserts the binding at its original index. -/
theorem pickAndMove?_refuses (outside : ¬ (cut.block = headerId ∧
    afterRemoval index cut.cut + 1 = index))
    {saved : Width} {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    (selected : chooseCut? g binding.operands binding.uses = some cut) :
    pickAndMove? g index = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_refuses outside found selected

/-- The preheader agrees syntactically and each block agrees on its exact
successor frame or return. This includes feedback and exit arguments. -/
theorem pickAndMove?_frames (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_frames picked input

theorem pickAndMove?_run_eq (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) (fuel : Nat) :
    out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_run_eq picked input fuel

theorem pickAndMove?_budget (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_budget picked input budget

/-- Partial observations agree, including their domains of definition. -/
theorem pickAndMove?_denotePart (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_denotePart picked input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
