module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

/-! # Exact CF operands and numbered γ banks at the inner shared tail -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Edge)
open Outer.MLIR.CF.Phi (arguments terminal)
open Outer.MLIR.CF.Phi.Readback (operands operands_arguments successor)
open Diamond.MLIR.CF (Label siteFrame destinationFrame source_site_eval)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Prefix.Routes src entry)

theorem readRows_exists : ∃ rows, readRows p = some rows :=
  Proofs.rows_exist p

/-- The observer stops at the actual shared-tail connection. Restoring the
original continuation yields the exact inner arm of the outer-profile emitter. -/
theorem inner_wiring :
    Prefix.innerRegion p = afterInner p (fun incoming => .ofBase (p.suffix.quads.lowerFrom incoming .jump)) :=
  rfl

theorem legacy_inner_wiring (legacy : Shared.Program src entry) :
    Shared.Numbered.innerRegion legacy = afterInner (Prefix.ofProgram legacy)
      (fun incoming => .ofBase (legacy.suffix.quads.lowerFrom incoming .jump)) :=
  rfl

theorem gamma_run (old : Bank (regs := regs) model) (fuel : Nat) :
    (gamma p).run (Join.model model) fuel (headerBank p old) =
      some (p.prefixBank model old (occurrence (side p old))) :=
  Proofs.gamma_run p old fuel

variable {p} (rows : Rows p)

/-- The original slot recovers exactly its typed CF successor from Φ. -/
theorem Rows.edge_roundtrip (taken : Bool) :
    successor (p.innerEdgeOccurrence taken).2 (terminal (predecessor p taken)).2 =
      some (rows.rebuild taken) := by
  have rebuilt : rows.rebuild taken = ⟨.site p.meet, rows.operands taken⟩ := by
    change Edge.mk (Label.site p.meet) (Outer.MLIR.CF.Phi.Readback.operands (arguments (rows.operands taken))) = _
    rw [operands_arguments]
  rw [rebuilt]
  exact Proofs.rebuild_slot p rows taken

/-- Both rows independently read all their reaching definitions from
one post-body environment, even if the conditional's slots share a label. -/
theorem Rows.bank_eq (taken : Bool) (input old : Bank (regs := regs) model) :
    rows.bank taken input old = encodeValues (p.prefixBank model old (occurrence taken)) := by
  change (Outer.MLIR.CF.Phi.Readback.operands (arguments (rows.operands taken))).eval (arrivalEnv p taken input old) = _
  rw [operands_arguments]
  exact Option.some.inj (by simpa only [rows.checked, Option.map_some] using Proofs.incoming_packet p input old taken)

theorem Rows.first_tail (taken : Bool) (input old : Bank (regs := regs) model) :
    ((cfg p).block (.site p.meet)).eval evalOp (fun term env => term.eval env)
        ((rows.bank taken input old).append (encodeValues input)) =
      let bank := (src p.meet).body.eval model (p.prefixBank model old (occurrence taken))
      .inl (destinationFrame bank ((src p.meet).terminator.select model bank)) := by
  rw [rows.bank_eq]
  exact source_site_eval (entry := entry) input _ p.meet

/-- On an activation entering the outer-true region, the actual CF run
resumes at the inner-tail label with the reconstructed bank. -/
theorem Rows.from_header (input old : Bank (regs := regs) model) (fuel : Nat)
    (entered : ((headerBank p old).get p.outerTest).down = true) :
    (cfg p).runFrom evalOp (fuel + p.prefixVisits (occurrence (side p old)) + 1)
        (encodeValues input) (siteFrame p.header old) =
      (cfg p).runFrom evalOp (fuel + 1) (encodeValues input) (rows.frame (side p old) input old) := by
  rw [Rows.frame, rows.bank_eq]
  exact Proofs.from_header p input old fuel entered

/-- Compare the actual inner γ packet with the selected CF/Φ packet. -/
theorem Rows.numbered_bank (input old : Bank (regs := regs) model) (fuel : Nat) :
    ((gamma p).run (Join.model model) fuel (headerBank p old)).map (encodeValues (ins := regs)) =
      some (rows.bank (side p old) input old) := by
  rw [gamma_run, rows.bank_eq]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi
