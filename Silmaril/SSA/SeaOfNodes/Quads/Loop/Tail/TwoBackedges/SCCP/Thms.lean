module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.BlockFacts

/-! Least solution and native coverage for a pure quad loop with two backedges. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP

open Diamond (Model Signature ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers TupleLE)
open Semantics.Dataflow (Flat)
open SeaOfNodes.Loop.SCCP (BankFacts BankDecidableEq BankCovers)
open Blocks (Bank)
open Join (Block)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

/-- The compiled producer interpreter reads the same ordered flat writes. -/
theorem blockFacts_fold (m : Model.{u, v, w} Op) (block : Block Op regs)
    (entry : Tuple (Fact m.value) (dataPorts regs)) :
    blockFacts m block entry = block.foldl (fun bank q => quadFacts m q bank) entry :=
  Proofs.blockFacts_fold m block entry

theorem blockFacts_mono (block : Block Op regs) {a b : Tuple (Fact m.value) (dataPorts regs)}
    (le : TupleLE a b) : TupleLE (blockFacts m block a) (blockFacts m block b) :=
  Proofs.blockFacts_mono block le

theorem successors_mono {a b s t : Flat (ULift.{w} Bool)} (again : a ≤ b) (select : s ≤ t) :
    successors a s ⊆ successors b t :=
  Proofs.successors_mono again select

/-- The compiled abstract block covers the actual ordered source block. -/
theorem blockFacts_cover (block : Block Op regs)
    {facts : Tuple (Fact m.value) (dataPorts regs)} {old : Bank (regs := regs) m}
    (covers : TupleCovers facts old) : TupleCovers (blockFacts m block facts) (block.eval m old) :=
  Proofs.blockFacts_cover block covers

/-- The Φ result is the least upper bound of the individually marked columns. -/
theorem phiFacts_le_iff {value : Data → Type w} [BankDecidableEq value (dataPorts regs)]
    (marks : Marked) (column : Incoming → BankFacts value (dataPorts regs))
    (upper : BankFacts value (dataPorts regs)) :
    phiFacts marks column ≤ upper ↔ ∀ edge, incomingIndex edge ∈ marks → column edge ≤ upper :=
  Proofs.phiFacts_le_iff marks column upper

variable (m) (p : Program Op regs out) [BankDecidableEq m.value (dataPorts regs)]
variable (input : Tuple (Fact m.value) (dataPorts regs))

theorem transfer_mono : Monotone (transfer m p input) :=
  Proofs.transfer_mono

def transferHom : State m.value regs out →o State m.value regs out :=
  ⟨transfer m p input, transfer_mono m p input⟩

/-- Run the existing finite-height iterator from optimistic bottom. -/
def solve : State m.value regs out :=
  (height m.value regs out).solve (transferHom m p input)

theorem solve_fixed : transfer m p input (solve m p input) = solve m p input :=
  (height m.value regs out).solve_fixed (transferHom m p input)

theorem solve_isLeast : IsLeast {state | transfer m p input state = state} (solve m p input) :=
  (height m.value regs out).solve_isLeast (transferHom m p input)

attribute [local irreducible] solve

variable {input} {concrete : Bank (regs := regs) m}

/-- Every finite native header arrival has its exact incoming occurrence
marked and its entire bank covered. -/
theorem solve_arrives (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old) :
    incomingIndex via ∈ (solve m p input).1 ∧ BankCovers (solve m p input).2.1 old :=
  Proofs.fixed_arrives (solve_fixed m p input) covered arrived

/-- Every dispatch reached from a covered header arrival selects a marked
feedback occurrence, irrespective of whether the execution later returns. -/
theorem solve_dispatch_marked (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old)
    (continues : ((p.header.eval m old).get p.again).down = true) :
    incomingIndex (.feedback ((p.header.eval m old).get p.select).down) ∈ (solve m p input).1 := by
  let side := ((p.header.eval m old).get p.select).down
  have taken : p.step m old = .inr (side, (p.feedback side).eval m (p.header.eval m old)) := by simp [Program.step, continues, side]
  exact (solve_arrives m p covered (.feedback arrived taken)).1

/-- Every actual bounded source return marks exit and is covered by the
inferred result. The source fuel counts native blocks. -/
theorem solve_source_return (covered : TupleCovers input concrete)
    {fuel : Nat} {result : sortValue m.value out}
    (returned : p.source.runFrom m fuel 0 concrete = some result) :
    exitIndex ∈ (solve m p input).1 ∧ (solve m p input).2.2.Covers result :=
  Proofs.fixed_source_return (solve_fixed m p input) covered returned

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP
