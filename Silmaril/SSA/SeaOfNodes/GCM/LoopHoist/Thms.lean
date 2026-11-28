module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Correctness

/-! # Certified preheader placement, routing and loop observations -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {tree : DominatorTree (lower g)}
variable {cut : Point (SourceLabel carried result)} {output : Output Input carried result}

/-- Successful motion uses the enumerated preheader cut chosen by the
checked natural-loop ranking for the actual first header binding. -/
theorem pickAndHoist?_placement (picked : pickAndHoist? g tree = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧
      LoopForest.choosePlacement tree blocks (operandSites operands) (useSites 0 1 rest) = some cut ∧
      Legal (lower g) (operandSites operands) (useSites 0 1 rest) cut :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_placement picked

/-- The entry supplies one saved value. Every header transfer repeats that
value, alongside the original latch word. Exit transfers keep their original
payload. -/
theorem pickAndHoist?_routes (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) :
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args) (captured : Operands Input args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧ capture? operands = some captured ∧
      let value := evalOp op (captured.eval input)
      output.2.entry.eval evalOp (fun term env => Terminator.eval env term) input =
        ((lower g).entry.eval evalOp (fun term env => Terminator.eval env term) input).map
          (carryFrame value) id ∧
      ∀ frame : Frame (SourceLabel carried result),
        let routed := carryFrame value frame
        (output.2.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
          (routed.args.append input) =
          (((lower g).block frame.label).eval evalOp (fun term env => Terminator.eval env term)
            (frame.args.append input)).map (carryFrame value) id :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_routes picked input

/-- The emitted CFG has the same observation at every CF fuel budget. -/
theorem pickAndHoist?_run_eq (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_run_eq picked input fuel

/-- One unit of backedge budget still corresponds to one header traversal.
The preheader, final header test and exit account for three extra blocks. -/
theorem pickAndHoist?_budget (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_budget picked input budget

/-- The emitted CFG preserves and reflects all finite source-loop returns. -/
theorem pickAndHoist?_returns_iff (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, output.2.run evalOp fuel input = some (.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_returns_iff picked input value

variable {index : Nat}

/-- Translating captured operands to the entry scope preserves their values. -/
theorem evalCaptureOrigins {Γ args : List Width} (origins : Origins Input Γ)
    (operands : Operands Γ args) {captured : Operands Input args}
    (found : captureOrigins? origins operands = some captured)
    (env : Env Γ) (input : Env Input) (agree : CapturesAgree origins env input) :
    operands.eval env = captured.eval input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.evalCaptureOrigins origins operands found env input agree

/-- A typed rename with agreeing environments preserves operand evaluation. -/
theorem evalRenameOperands {Γ Δ args : List Width} (rename : Rename Γ Δ)
    (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (operands : Operands Γ args) :
    (For.renameOperands rename operands).eval target = operands.eval source :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.evalRename rename source target same operands

/-- Successful emission consumes the selected preheader cut and the
actual current binding with captured operands. -/
theorem hoistCodeWith?_spec
    {entry : Block TargetOp (SourceLabel carried result) Input [result]}
    {header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]}
    {choose : List (Point (SourceLabel carried result)) → List (Use (SourceLabel carried result)) →
      Option (Point (SourceLabel carried result))}
    (picked : hoistCodeWith? entry header index choose = some (cut, output)) :
    ∃ binding : Binding Input (carried :: Input) output.1 carried result,
      findBinding index 0 headerOrigins header = some ⟨output.1, binding⟩ ∧
      choose binding.operands binding.uses = some cut ∧
      cut = ⟨none, 0⟩ ∧
      ∃ operands : Operands Input binding.args,
        binding.captured? = some operands ∧
        output.2 = emitHeader entry binding.op operands (binding.rewrite Var.there .here) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.hoistCodeWith?_spec picked

/-- Reuse the preheader and header routing proof for any matching CFG
with the canonical exit. -/
theorem emitHeader_routes {saved : Width}
    {cfg : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (exit : cfg.block .exit = .terminator (.ret (.cons .here .nil)))
    (binding : Binding Input (carried :: Input) saved carried result)
    (found : findBinding index 0 headerOrigins (cfg.block .header) = some ⟨saved, binding⟩)
    (operands : Operands Input binding.args) (captured : binding.captured? = some operands)
    (input : Env Input) :
    Routes cfg (emitHeader cfg.entry binding.op operands (binding.rewrite Var.there .here))
      input (evalOp binding.op (operands.eval input)) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.emitHeader_routes exit binding found operands captured input

theorem routes_run_eq {saved : Width}
    {cfg : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {target : Cfg TargetOp (Label saved carried result) Input [result]} {input : Env Input}
    {value : BitVec saved.val} (routing : Routes cfg target input value) (fuel : Nat) :
    target.run evalOp fuel input = cfg.run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.routes_run_eq routing fuel

/-- Prefixing the header's packet preserves the runner at every fuel if
entry and block transfers commute with that prefix. -/
theorem routesWith_run_eq {saved : Width} {extra : List Width}
    {source : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {target : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])}
    (routing : RoutesWith source target input values) (fuel : Nat) :
    target.run evalOp fuel input = source.run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.runEqOfRoutes routing fuel

/-- The nominated binding uses the legal preheader cut selected from its
actual typed operand and use sites. -/
theorem pickBindingAndHoist?_placement (picked : pickBindingAndHoist? g tree index = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
    ∃ binding : Binding Input (carried :: Input) output.1 carried result,
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      LoopForest.choosePlacement tree blocks binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickBindingAndHoist?_placement picked

/-- The entry and all block transfers preserve the source values and
carry the nominated producer result through feedback. -/
theorem pickBindingAndHoist?_routes (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) :
    ∃ (binding : Binding Input (carried :: Input) output.1 carried result)
      (operands : Operands Input binding.args),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      binding.captured? = some operands ∧
      Routes (lower g) output.2 input (evalOp binding.op (operands.eval input)) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickBindingAndHoist?_routes picked input

/-- The nominated rewrite preserves observations at every CF fuel budget. -/
theorem pickBindingAndHoist?_run_eq (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickBindingAndHoist?_run_eq picked input fuel

/-- The emitted CFG still uses fuel `budget + 3` for the native backedge budget. -/
theorem pickBindingAndHoist?_budget (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickBindingAndHoist?_budget picked input budget

/-- The nominated rewrite preserves and reflects finite native loop returns. -/
theorem pickBindingAndHoist?_returns_iff
    (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, output.2.run evalOp fuel input = some (.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickBindingAndHoist?_returns_iff picked input value

variable {consumerIndex : Nat} {moved : SliceOutput Input carried result}

/-- The ranker admits both moved definitions at the same preheader cut.
The consumer sites treat the internal operand as a preheader value. -/
theorem pickSliceAndHoist?_placement (picked : pickSliceAndHoist? g tree consumerIndex = some moved) :
    ∃ (index : Nat)
      (slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result),
      consumerIndex = index + 1 ∧
      findSlice index 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      (⟨none, 0⟩ : Point (SourceLabel carried result)) ∈ candidateCuts (lower g) blocks ∧
      Legal (lower g) slice.prerequisiteSites slice.prerequisiteUses ⟨none, 0⟩ ∧
      Legal (lower g) slice.consumerSites slice.consumerUses ⟨none, 0⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAndHoist?_placement picked

/-- Entry computes the prerequisite, then the consumer. Every header transfer
carries both results, and the exit payload agrees with the source. -/
theorem pickSliceAndHoist?_routes (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) :
    ∃ (index : Nat)
      (slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result),
      consumerIndex = index + 1 ∧
      findSlice index 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      RoutesWith (lower g) moved.cfg input (slice.savedValues input) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAndHoist?_routes picked input

/-- Moving the slice preserves observations at every CF fuel budget. -/
theorem pickSliceAndHoist?_run_eq (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAndHoist?_run_eq picked input fuel

/-- The native backedge budget still corresponds to CF fuel `budget + 3`. -/
theorem pickSliceAndHoist?_budget (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAndHoist?_budget picked input budget

/-- Moving the slice preserves and reflects finite native loop returns. -/
theorem pickSliceAndHoist?_returns_iff (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, moved.cfg.run evalOp fuel input = some (.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAndHoist?_returns_iff picked input value

variable {prerequisiteIndex gap : Nat}

/-- Both definitions are legal at the same ranked preheader cut. The
prerequisite check includes uses in retained bindings. -/
theorem pickSliceAcrossAndHoist?_placement
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved) :
    ∃ slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result,
      findSliceAcross prerequisiteIndex gap 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      (⟨none, 0⟩ : Point (SourceLabel carried result)) ∈ candidateCuts (lower g) blocks ∧
      Legal (lower g) slice.prerequisiteSites slice.prerequisiteUses ⟨none, 0⟩ ∧
      Legal (lower g) slice.consumerSites slice.consumerUses ⟨none, 0⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAcrossAndHoist?_placement picked

/-- The emitted CFG reproduces the source transfers with the two saved
values, including across retained header bindings. -/
theorem pickSliceAcrossAndHoist?_routes
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved) (input : Env Input) :
    ∃ slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result,
      findSliceAcross prerequisiteIndex gap 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      RoutesWith (lower g) moved.cfg input (slice.savedValues input) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAcrossAndHoist?_routes picked input

/-- The emitted CFG agrees with the source at every fuel budget. -/
theorem pickSliceAcrossAndHoist?_run_eq
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAcrossAndHoist?_run_eq picked input fuel

/-- The native backedge budget corresponds to CF fuel `budget + 3`. -/
theorem pickSliceAcrossAndHoist?_budget
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAcrossAndHoist?_budget picked input budget

/-- The non-adjacent rewrite preserves and reflects finite native returns. -/
theorem pickSliceAcrossAndHoist?_returns_iff
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved)
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, moved.cfg.run evalOp fuel input = some (.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickSliceAcrossAndHoist?_returns_iff picked input value

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
