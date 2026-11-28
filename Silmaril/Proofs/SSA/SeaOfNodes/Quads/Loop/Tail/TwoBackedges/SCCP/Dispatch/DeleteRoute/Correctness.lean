module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Proofs

open Diamond (Model Signature ValueSort dataPorts)
open Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)} {concrete : Bank (regs := regs) m}

theorem terminator_map (checked : Checked m p input) (index : Fin 4) :
    mapTerminator (keptBlock checked.side) (compact checked index).terminator =
      (checked.source (keptBlock checked.side index)).terminator := by
  obtain ⟨side, marked, excluded⟩ := checked
  cases side <;> fin_cases index <;> rfl

omit [BankDecidableEq m.value (dataPorts regs)] in
private theorem select_map {n k : Nat} (embed : Fin n → Fin k)
    (term : Tail.Terminator regs out n) (bank : Bank (regs := regs) m) :
    (mapTerminator embed term).select m bank = mapDestination embed (term.select m bank) := by
  cases term with
  | transfer => rfl
  | branch test yes no =>
    by_cases taken : (bank.get test).down = true <;> simp [mapTerminator, Tail.Terminator.select, taken]

theorem runFrom_retained (checked : Checked m p input) (fuel : Nat) (index : Fin 4)
    (bank : Bank (regs := regs) m) :
    (compact checked).runFrom m fuel index bank =
      checked.source.runFrom m fuel (keptBlock checked.side index) bank := by
  induction fuel generalizing index bank with
  | zero => rfl
  | succ fuel ih =>
    have body : (compact checked index).body = (checked.source (keptBlock checked.side index)).body := rfl
    simp only [Tail.Source.runFrom, ← body, ← terminator_map checked index, select_map]
    cases (compact checked index).terminator.select m ((compact checked index).body.eval m bank) with
    | jump target => exact ih target _
    | ret port => rfl

theorem feedback_arrival (checked : Checked m p input) (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old)
    (continues : ((p.header.eval m old).get p.again).down = true) :
    p.step m old =
      .inr (checked.side, ((compact checked (predecessor .backedge)).body.eval m (p.header.eval m old))) := by
  have selected := checked.dispatch_eq covered arrived continues
  have body : (compact checked (predecessor .backedge)).body = p.feedback checked.side := by
    obtain ⟨side, marked, excluded⟩ := checked
    cases side <;> rfl
  simp [Program.step, continues, selected, body]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Proofs
