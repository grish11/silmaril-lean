module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.Semantics.Dataflow.FiniteHeight.Thms
public import Silmaril.Semantics.Dataflow.Flat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Bank
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Equations
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Soundness

/-! Finite-height solution and coverage of native loop execution. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers TupleLE tupleFacts)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)
open Semantics.Dataflow.FiniteHeight (HeightBound)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

/-- The Φ fact is the least upper bound of the operands at marked arrivals. -/
theorem phiFact_le_iff {α : Type*} [DecidableEq α] (edges : Executable) (entry feedback upper : Flat α) :
    phiFact edges entry feedback ≤ upper ↔
      ∀ edge, incomingIndex edge ∈ edges → edge.select entry feedback ≤ upper :=
  Proofs.phiFact_le_iff edges entry feedback upper

/-- Each coordinate joins only the operands at marked occurrences. -/
theorem phiFacts_le_iff {value : Data → Type w} {ports : List (Ty Data)} [BankDecidableEq value ports]
    (edges : Executable) (entry feedback upper : BankFacts value ports) :
    phiFacts edges entry feedback ≤ upper ↔
      ∀ edge, incomingIndex edge ∈ edges → edge.select entry feedback ≤ upper :=
  Proofs.phiFacts_le_iff edges entry feedback upper

theorem bankTuple_tupleFacts {value : Data → Type w} {ports : List (Ty Data)}
    (facts : Tuple (Fact value) ports) : bankTuple (tupleFacts facts) = facts :=
  Proofs.bankTuple_tupleFacts facts

theorem tupleFacts_mono {value : Data → Type w} {ports : List (Ty Data)}
    {lhs rhs : Tuple (Fact value) ports} (le : TupleLE lhs rhs) : tupleFacts lhs ≤ tupleFacts rhs :=
  Proofs.tupleFacts_mono le

theorem bankTuple_mono {value : Data → Type w} {ports : List (Ty Data)}
    {lhs rhs : BankFacts value ports} (le : lhs ≤ rhs) : TupleLE (bankTuple lhs) (bankTuple rhs) :=
  Proofs.bankTuple_mono le

theorem bankCovers_of_tuple {value : Data → Type w} {ports : List (Ty Data)}
    {facts : Tuple (Fact value) ports} {concrete : Tuple (Val value) ports}
    (covered : TupleCovers facts concrete) : BankCovers (tupleFacts facts) concrete :=
  Proofs.bankCovers_of_tuple covered

theorem bankCovers_mono {value : Data → Type w} {ports : List (Ty Data)}
    {lhs rhs : BankFacts value ports} {concrete : Tuple (Val value) ports}
    (le : lhs ≤ rhs) (covered : BankCovers lhs concrete) : BankCovers rhs concrete :=
  Proofs.bankCovers_mono le covered

/-- The abstract guard covers the native guard read on the same old bank. -/
theorem headerGuard_cover {m : Model.{u, v, w} Op}
    (g : Graph Op inputs carried entrySigs headerSigs out)
    {input : Tuple (Fact m.value) (dataPorts inputs)} {entry : Tuple (Val m.value) (dataPorts inputs)}
    (covered : TupleCovers input entry) {bank : BankFacts m.value (dataPorts carried)}
    {old : Tuple (Val m.value) (dataPorts carried)} (hold : BankCovers bank old) :
    let args := appendTuple old entry
    (headerFacts m g input bank).guard.Covers (Diamond.read m g.predicate args (g.header.eval m args PUnit.unit)) :=
  (Proofs.headerFacts_cover (g := g) covered hold).1

/-- The abstract feedback column covers the native column read on the
same old bank. This is the producer-table coverage used by the solver. -/
theorem headerFeedback_cover {m : Model.{u, v, w} Op}
    (g : Graph Op inputs carried entrySigs headerSigs out)
    {input : Tuple (Fact m.value) (dataPorts inputs)} {entry : Tuple (Val m.value) (dataPorts inputs)}
    (covered : TupleCovers input entry) {bank : BankFacts m.value (dataPorts carried)}
    {old : Tuple (Val m.value) (dataPorts carried)} (hold : BankCovers bank old) :
    let args := appendTuple old entry
    BankCovers (headerFacts m g input bank).feedback (g.latch m .backedge args (g.header.eval m args PUnit.unit)) :=
  (Proofs.headerFacts_cover (g := g) covered hold).2.1

/-- Equal initial latches and steps on original arrivals give equal bounded observations. -/
theorem evalBackedges_eq_of_steps {m : Model.{u, v, w} Op}
    {g : Graph Op inputs carried entrySigs headerSigs out}
    {targetEntry targetHeader : List (List (Ty Data))}
    (target : Graph Op inputs carried targetEntry targetHeader out)
    {entry : Tuple (Val m.value) (dataPorts inputs)} (initial : target.initial m entry = g.initial m entry)
    (steps : ∀ {via count old}, Arrives m g entry via count old → target.step m entry old = g.step m entry old)
    (budget : Nat) :
    target.evalBackedges m budget entry = g.evalBackedges m budget entry :=
  Proofs.evalBackedges_eq_of_steps target initial steps budget

/-- Three control insertions and two strict increases at each carried or exit port suffice. -/
def height (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) :
    HeightBound (State value carried out) :=
  (HeightBound.finset (Fin 3)).prod
    ((HeightBound.pi fun i => Flat.height (Val value (dataPorts carried)[i])).prod
      (Flat.height (sortValue value out)))

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

theorem transfer_mono : Monotone (transfer m g input) :=
  Proofs.transfer_mono g input

def transferHom : State m.value carried out →o State m.value carried out :=
  ⟨transfer m g input, transfer_mono m g input⟩

/-- Run the cyclic equations to the certified least fixed point. -/
def solve : State m.value carried out :=
  (height m.value carried out).solve (transferHom m g input)

theorem solve_fixed : transfer m g input (solve m g input) = solve m g input :=
  (height m.value carried out).solve_fixed (transferHom m g input)

theorem solve_isLeast : IsLeast {state | transfer m g input state = state} (solve m g input) :=
  (height m.value carried out).solve_isLeast (transferHom m g input)

-- The coverage theorems use the fixed-point law without unfolding the iteration.
attribute [local irreducible] solve

variable {input} {entry : Tuple (Val m.value) (dataPorts inputs)}

/-- The analysis marks and covers every finite arrival, even if the run never returns. -/
theorem solve_arrives (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) :
    incomingIndex via ∈ (solve m g input).1 ∧ BankCovers (solve m g input).2.1 old :=
  Proofs.fixed_arrives (solve_fixed m g input) covered arrived

/-- Each actual header step from a covered latch follows a marked edge, and
its returned value or entire next bank is covered. -/
theorem solve_step (covered : TupleCovers input entry)
    {old : Tuple (Val m.value) (dataPorts carried)}
    (hold : BankCovers (solve m g input).2.1 old) :
    match g.step m entry old with
    | .inl result => exitIndex ∈ (solve m g input).1 ∧ (solve m g input).2.2.Covers result
    | .inr next => incomingIndex .backedge ∈ (solve m g input).1 ∧ BankCovers (solve m g input).2.1 next :=
  Proofs.fixed_step (state := solve m g input) (old := old) (solve_fixed m g input) covered hold

/-- A finite return from a covered latch, with an exact native backedge count. -/
theorem solve_returnsAfter (covered : TupleCovers input entry)
    {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)} {result : sortValue m.value out}
    (hold : BankCovers (solve m g input).2.1 old) (run : g.ReturnsAfter m entry count old result) :
    exitIndex ∈ (solve m g input).1 ∧ (solve m g input).2.2.Covers result :=
  Proofs.fixed_returnsAfter (state := solve m g input) (old := old) (solve_fixed m g input) covered hold run

/-- A native finite return marks the exit occurrence and agrees with an
inferred constant. The result is independent of any concrete execution fuel. -/
theorem solve_returns (covered : TupleCovers input entry)
    {result : sortValue m.value out} (run : g.Returns m entry result) :
    exitIndex ∈ (solve m g input).1 ∧ (solve m g input).2.2.Covers result :=
  let ⟨count, trace⟩ := run
  solve_returnsAfter m g (input := input) (entry := entry) (old := g.initial m entry) (count := count)
    (result := result) covered (solve_arrives m g covered .entry).2 trace

end Silmaril.SSA.SeaOfNodes.Loop.SCCP
