module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Proofs

open Diamond (Model Signature ValueSort dataPorts)
open Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out}

private theorem specialized_header (side : Bool) (fuel : Nat) (old : Bank (regs := regs) m)
    (selected : ((p.header.eval m old).get p.again).down = true →
      ((p.header.eval m old).get p.select).down = side) :
    (specialize p side).runFrom m (fuel + 1) 1 old =
      match p.step m old with
      | .inl result => some result
      | .inr (_, next) => (specialize p side).runFrom m (fuel - 2) 1 next := by
  let current := p.header.eval m old
  have header : (specialize p side).runFrom m (fuel + 1) 1 old =
      if (current.get p.again).down then (specialize p side).runFrom m fuel 2 current
      else some (current.get p.result) := by
    simp only [Tail.Source.runFrom,
      show specialize p side 1 = ⟨p.header, .branch p.again (.jump 2) (.ret p.result)⟩ from rfl,
      Tail.Terminator.select, current]
    by_cases next : ((p.header.eval m old).get p.again).down = true <;> simp [next]
  rw [header]
  by_cases continues : (current.get p.again).down = true
  · have original : p.step m old = .inr (side, (p.feedback side).eval m current) := by
      simp [Program.step, current, continues, selected continues]
    rw [original]
    simp only [continues, ite_true]
    cases fuel with
    | zero => rfl
    | succ fuel => cases fuel with
      | zero => rfl
      | succ fuel => cases side <;> rfl
  · have original : p.step m old = .inl (current.get p.result) := by
      simp [Program.step, current, continues]
    rw [original]
    simp [continues]

variable [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)} {concrete : Bank (regs := regs) m}

theorem dispatch_eq (checked : Checked m p input) (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old)
    (continues : ((p.header.eval m old).get p.again).down = true) :
    ((p.header.eval m old).get p.select).down = checked.side := by
  have marked := solve_dispatch_marked m p covered arrived continues
  by_contra different
  rw [Bool.eq_not_of_ne different] at marked
  exact checked.excluded marked

private theorem run_header_eq (checked : Checked m p input) (covered : TupleCovers input concrete)
    (fuel : Nat) {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old) :
    checked.source.runFrom m fuel 1 old = p.source.runFrom m fuel 1 old := by
  induction fuel using Nat.strong_induction_on generalizing via count old with
  | ind fuel smaller =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      change (specialize p checked.side).runFrom m (fuel + 1) 1 old = _
      rw [specialized_header checked.side fuel old (dispatch_eq checked covered arrived), p.source_header]
      cases taken : p.step m old with
      | inl result => rfl
      | inr feedback =>
        obtain ⟨side, next⟩ := feedback
        exact smaller (fuel - 2) (by omega) (.feedback arrived taken)

theorem runFrom_eq (checked : Checked m p input) (covered : TupleCovers input concrete) (fuel : Nat) :
    checked.source.runFrom m fuel 0 concrete = p.source.runFrom m fuel 0 concrete := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change checked.source.runFrom m fuel 1 (p.preheader.eval m concrete) = _
    rw [p.source_entry]
    exact run_header_eq checked covered fuel .entry

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Proofs
