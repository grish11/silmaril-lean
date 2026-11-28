module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri.Correctness

/-! Finite coloured completion of the actual guarded numbered artifact. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri

open SeaOfNodes.Diamond (ValueSort Val dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Graph)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open Join (Opcode)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable {facts : Tuple (Fact Word) (dataPorts regs)} {outs : List (Diamond.Ty Width)}

/-- The numbered graph supplies the net directly. A firing trace and a
numbered run witness the same exact root packet at independent bounds. -/
theorem finishes_iff_numbered (target : Target regs result) (input : Bank (regs := regs) model)
    (packet : Tuple (Val Word) [.value (.data result)]) :
    Finishes (Join.model model) target.2 input packet ↔
      ∃ fuel, target.2.run (Join.model model) fuel input = some packet :=
  finishes_iff (Join.model model) target.2 input packet

/-- Every finite completed firing trace publishes the packet of any
successful numbered run from the same input. -/
theorem completed_packet_eq (target : Target regs result) (input : Bank (regs := regs) model)
    {completed expected : Tuple (Val Word) [.value (.data result)]} {fuel : Nat}
    (fired : Finishes (Join.model model) target.2 input completed)
    (returned : target.2.run (Join.model model) fuel input = some expected) : completed = expected :=
  Proofs.completed_packet_eq target input fired returned

/-- Completion of the actual linked graph is equivalent to completion of its
selected child. Both start from the original bank. -/
theorem attach_finishes_iff (test : Selector regs) (childSigs : Fin 2 → List (List (Diamond.Ty Width)))
    (children : ∀ i, Graph (Opcode Op) (dataPorts regs) [] (childSigs i) outs)
    (input : Bank (regs := regs) model) (packet : Tuple (Val Word) outs) :
    Finishes (Join.model model) (attach test childSigs children) input packet ↔
      let selected := ((test.2.toGraph.run (Join.model model) input).get .head).down
      Finishes (Join.model model) (children selected) input packet := by
  simp only [finishes_iff, Graph.Returns, attach_run]

theorem no_completion_iff_numbered (target : Target regs result) (input : Bank (regs := regs) model) :
    (∀ packet, ¬ Finishes (Join.model model) target.2 input packet) ↔
      ∀ fuel, target.2.run (Join.model model) fuel input = none := by
  simp only [finishes_iff_numbered, not_exists, Option.eq_none_iff_forall_ne_some]
  exact forall_comm

variable [BankDecidableEq Word (dataPorts regs)] {target : Target regs result}

/-- The exact singleton root packet corresponds to a finite source return
at any sufficient source budget. -/
theorem compile_finishes_iff (success : compile p facts = .ok target)
    (input : Bank (regs := regs) model) (word : Word result) :
    Finishes (Join.model model) target.2 input (.cons word .nil) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some word :=
  (finishes_iff_numbered target input _).trans (compile_returns_iff success input word)

/-- This is absence of finite completion from the initial marking. -/
theorem compile_no_completion_iff (success : compile p facts = .ok target)
    (input : Bank (regs := regs) model) :
    (∀ packet, ¬ Finishes (Join.model model) target.2 input packet) ↔
      ¬ ∃ word fuel, p.source.runFrom model fuel 0 input = some word :=
  (no_completion_iff_numbered target input).trans (compile_noReturn_iff success input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri
