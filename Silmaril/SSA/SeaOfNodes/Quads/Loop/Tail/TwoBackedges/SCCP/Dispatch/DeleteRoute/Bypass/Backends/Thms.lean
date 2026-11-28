module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Thms

/-! End-to-end observations for both backends from one checked admission. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}
variable {p : Program Op regs (.data result)} [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)} {targets : Targets p}
variable {input : Bank (regs := regs) model}

/-- The artifacts agree with the separate compilers, and the exposed side
is the unique feedback occurrence marked by the least solution. -/
theorem compile_components (success : compile p facts = .ok targets) :
    Bypass.MLIR.CF.compile p facts = some targets.cf ∧
      Numbered.compile model p facts = some targets.numbered ∧
      incomingIndex (.feedback targets.retained) ∈ (solve model p facts).1 ∧
      incomingIndex (.feedback !targets.retained) ∉ (solve model p facts).1 :=
  Proofs.compile_components success

/-- Each error identifies the exact marking that prevented singleton admission. -/
theorem compile_error_iff (reason : Refusal) :
    compile p facts = .error reason ↔
      match reason with
      | .bothMarked =>
        incomingIndex (.feedback true) ∈ (solve model p facts).1 ∧
          incomingIndex (.feedback false) ∈ (solve model p facts).1
      | .neitherMarked =>
        incomingIndex (.feedback true) ∉ (solve model p facts).1 ∧
          incomingIndex (.feedback false) ∉ (solve model p facts).1 :=
  Proofs.compile_error_iff reason

/-- Compare the three observations at budgets permitting the same number
of feedback visits. Includes exhaustion. -/
theorem compile_run (success : compile p facts = .ok targets) (covered : TupleCovers facts input)
    (limit : Nat) :
    let observed := p.source.runFrom model (3 * limit + 2) 0 input
    targets.cf.run evalOp (2 * limit + 3) (encodeValues input) =
      observed.map (fun value => Env.cons value .nil) ∧
    targets.numbered.run (Join.model model) limit input =
      observed.map (fun value => (Tuple.cons value .nil : Tuple (Join.model model).Val [.value (.data result)])) :=
  ⟨Bypass.MLIR.CF.compile_run (compile_components success).1 covered limit,
    Numbered.compile_run (compile_components success).2.1 covered limit⟩

/-- Each backend preserves and reflects finite returns at its own bound. -/
theorem compile_returns_iff (success : compile p facts = .ok targets) (covered : TupleCovers facts input)
    (value : Word result) :
    let native := ∃ fuel, p.source.runFrom model fuel 0 input = some value
    ((∃ fuel, targets.cf.run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔ native) ∧
      (targets.numbered.Returns (Join.model model) input (.cons value .nil) ↔ native) :=
  ⟨Bypass.MLIR.CF.compile_returns_iff (compile_components success).1 covered value,
    Numbered.compile_returns_iff (compile_components success).2.1 covered value⟩

/-- Both targets exhaust at every finite bound exactly when the original
source has no finite return. -/
theorem compile_noReturn_iff (success : compile p facts = .ok targets) (covered : TupleCovers facts input) :
    let absent := ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value
    (targets.cf.Diverges evalOp (encodeValues input) ↔ absent) ∧
      ((∀ fuel, targets.numbered.run (Join.model model) fuel input = none) ↔ absent) :=
  ⟨Bypass.MLIR.CF.compile_diverges_iff (compile_components success).1 covered,
    Numbered.compile_noReturn_iff (compile_components success).2.1 covered⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends
