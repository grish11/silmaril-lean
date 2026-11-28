module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Proofs

open SeaOfNodes.Diamond (Model Val ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open RVSDG (Port Tuple)
open Join (Block)
open Blocks (Bank)

universe u v w

theorem operand_reads {T : Type u} {F : T → Type w} {head : T} {ports operands : List T}
    (uses : Tuple (Port ports) operands) (value : F head) (bank : Tuple F ports) :
    (uses.map (G := Port (head :: ports)) (fun _ p => .tail p)).map
      (fun _ p => (Tuple.cons value bank).get p) = uses.map (fun _ p => bank.get p) := by
  induction uses with
  | nil => rfl
  | cons p _ ih => exact congrArg (Tuple.cons (bank.get p)) ih

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {fresh out : ValueSort Data}

theorem covers_iff {value : Data → Type w} (inputFacts : Tuple (Fact value) (dataPorts regs))
    (input : Tuple (Val value) (dataPorts (fresh :: regs))) :
    TupleCovers (facts fresh inputFacts) input ↔ TupleCovers inputFacts (project input) := by
  cases input with
  | cons head rest =>
    refine ⟨fun h _ p => h (.tail p), ?_⟩
    intro h t p
    cases p with
    | head => exact True.intro
    | tail p => exact h p

variable (m : Model.{u, v, w} Op)

theorem block_eval (block : Block Op regs) (value : sortValue m.value fresh) (bank : Bank (regs := regs) m) :
    Block.eval (block.map (quad fresh)) m (.cons value bank) = .cons value (block.eval m bank) := by
  induction block generalizing bank with
  | nil => rfl
  | cons q rest ih =>
    have step : (quad fresh q).eval m (.cons value bank) = .cons value (q.eval m bank) := by
      exact congrArg (fun inputs =>
        Tuple.cons (F := Val m.value) (t := .value fresh) value (write q.dest (m.run q.op inputs) bank))
        (operand_reads (F := Val m.value) (head := .value fresh) q.operands value bank)
    simp only [Block.eval, List.map_cons, List.foldl_cons] at ih ⊢
    rw [step, ih]

private theorem step_cons (p : Program Op regs out)
    (value : sortValue m.value fresh) (bank : Bank (regs := regs) m) :
    (program fresh p).step m (.cons value bank) =
      match p.step m bank with
      | .inl word => .inl word
      | .inr (side, next) => .inr (side, .cons value next) := by
  simp only [Program.step, program, block_eval]
  let current := p.header.eval m bank
  let side := (current.get p.select).down
  let next := (p.feedback side).eval m current
  let word := current.get p.result
  change (if (current.get p.again).down then Sum.inr (side, Tuple.cons (F := Val m.value) (t := .value fresh) value next) else Sum.inl word) =
    (match (if (current.get p.again).down then Sum.inr (side, next) else Sum.inl word) with
    | .inl word => Sum.inl word
    | .inr (side, next) => Sum.inr (side, Tuple.cons (F := Val m.value) (t := .value fresh) value next))

  cases (current.get p.again).down <;> rfl

private theorem header_run (p : Program Op regs out) (fuel : Nat)
    (value : sortValue m.value fresh) (bank : Bank (regs := regs) m) :
    (program fresh p).source.runFrom m fuel 1 (.cons value bank) =
      p.source.runFrom m fuel 1 bank := by
  induction fuel using Nat.strong_induction_on generalizing bank with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_header, Program.source_header, step_cons]
      cases p.step m bank with
      | inl _ => rfl
      | inr edge =>
        obtain ⟨side, next⟩ := edge
        exact ih (fuel - 2) (by omega) next

theorem source_run (p : Program Op regs out) (fuel : Nat) (input : Bank (regs := fresh :: regs) m) :
    (program fresh p).source.runFrom m fuel 0 input = p.source.runFrom m fuel 0 (project input) := by
  cases input with
  | cons value bank =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_entry, Program.source_entry]
      change (program fresh p).source.runFrom m fuel 1
        (Block.eval (p.preheader.map (quad fresh)) m (.cons value bank)) =
          p.source.runFrom m fuel 1 (p.preheader.eval m bank)
      rw [block_eval m p.preheader value bank]
      exact header_run m p fuel value (p.preheader.eval m bank)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Proofs
