module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Proofs

open SeaOfNodes.Diamond (ValueSort Val dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple Port Wires Origin Locals)
open Join (Opcode)
open Join.Finite (lastBank lastBank_read)
open Semantics.Dataflow (Flat)
open Blocks (Bank)

variable {regs slots : List (ValueSort Width)} {past : List (List (Diamond.Ty Width))}
variable {outs : List (Diamond.Ty Width)}

theorem gamma_inputs (tag : Origin (dataPorts regs) past (.control 2))
    (childSigs : Fin 2 → List (List (Diamond.Ty Width))) (input : Bank (regs := regs) model)
    (locals : Locals (Val Word) past) :
    (gammaNode (outs := outs) tag childSigs).inputs.read input locals =
      .cons (SeaOfNodes.Diamond.read model tag input locals) input := by
  have bank : Wires.read (tabulate (dataPorts regs) (fun port => Origin.arg (past := past) port)) input locals = input := by
    rw [read_tabulate model]
    exact tabulate_get_eq input
  exact congrArg (Tuple.cons (SeaOfNodes.Diamond.read model tag input locals)) bank

private abbrev tagValues (b : Bool) : Tuple (Val Word) Tag := .cons ⟨index b⟩ .nil

private theorem flag_eval (b : Bool) (input : Bank (regs := regs) model)
    (locals : Locals (Val Word) past) :
    (flag b).eval (Join.model model) input locals = .cons ⟨index b⟩ .nil :=
  lastBank_read model input locals (tagValues b)

private theorem andThen_eval (tag : Origin (dataPorts regs) past (.control 2)) (next : Selector regs)
    (input : Bank (regs := regs) model) (locals : Locals (Val Word) past) (b : Bool)
    (picked : SeaOfNodes.Diamond.read model tag input locals = ⟨index b⟩) :
    (andThen tag next).eval (Join.model model) input locals =
      if b then next.2.run (Join.model model) input else .cons ⟨index false⟩ .nil := by
  change (lastBank past Tag).read input (locals.snoc
    (RVSDG.Shape.eval (Join.model model) (RVSDG.Shape.gamma 0)
      (fun i bank => by exact (checkArm next (show Fin 2 from i)).run (Join.model model) bank)
      ((gammaNode tag (checkSigs next)).inputs.read input locals))) = _
  rw [gamma_inputs, picked]
  cases b
  · exact (lastBank_read model input locals ((flag false).run (Join.model model) input)).trans
      (flag_eval (past := []) false input PUnit.unit)
  · exact lastBank_read model input locals (next.2.run (Join.model model) input)

private theorem predicate_run (port : Port (dataPorts regs) (.value .predicate))
    (expected : Bool) (next : Selector regs) (input : Bank (regs := regs) model) :
    (predicateCheck port expected next).2.run (Join.model model) input =
      if expected = (input.get port).down then next.2.run (Join.model model) input
      else .cons ⟨index false⟩ .nil := by
  let packet : Tuple (Val Word) PredicatePacket :=
    .cons ⟨if (input.get port).down then index expected else index !expected⟩
      (.cons (input.get port) .nil)
  let tag := (lastBank [] PredicatePacket (args := dataPorts regs)).get .head
  change (andThen tag next).eval (Join.model model) input (Locals.snoc (past := []) PUnit.unit packet) = _
  have picked : SeaOfNodes.Diamond.read model tag input (Locals.snoc (past := []) PUnit.unit packet) =
      ⟨index (decide (expected = (input.get port).down))⟩ := by
    change packet.get .head = _
    cases read : (input.get port).down <;> cases expected <;> simp [packet, read] <;> rfl
  simpa only [decide_eq_true_eq] using andThen_eval tag next input _ _ picked

private theorem compare_tag {width : Width} (actual expected : Word width) :
    (if actual.ult expected then 0 else if expected.ult actual then 0 else 1 : Fin 2) =
      index (decide (expected = actual)) := by
  rcases Nat.lt_trichotomy actual.toNat expected.toNat with lt | equal | gt
  · have diff : expected ≠ actual := fun eq => Nat.ne_of_gt lt (congrArg BitVec.toNat eq)
    simp [index, BitVec.ult_eq_decide, lt, diff]
  · have eq : expected = actual := BitVec.eq_of_toNat_eq equal.symm
    subst expected
    simp [index, BitVec.ult_eq_decide]
  · have diff : expected ≠ actual := fun eq => Nat.ne_of_lt gt (congrArg BitVec.toNat eq)
    simp [index, BitVec.ult_eq_decide, gt, Nat.not_lt_of_gt gt, diff]

private theorem word_run {width : Width} (port : Port (dataPorts regs) (.value (.data width)))
    (expected : Word width) (next : Selector regs) (input : Bank (regs := regs) model) :
    (wordCheck port expected next).2.run (Join.model model) input =
      let actual : Word width := input.get port
      if expected = actual then next.2.run (Join.model model) input
      else .cons ⟨index false⟩ .nil := by
  let word : List (Diamond.Ty Width) := [.value (.data width)]
  let pred : List (Diamond.Ty Width) := [.value .predicate]
  let actual : Word width := input.get port
  let lo : Val Word (.value .predicate) := ⟨actual.ult expected⟩
  let hi : Val Word (.value .predicate) := ⟨expected.ult actual⟩
  let packet : Tuple (Val Word) WordPacket :=
    .cons ⟨if lo.down then 0 else if hi.down then 0 else 1⟩ (.cons lo (.cons hi .nil))
  let locals : Locals (Val Word) [word, pred, pred, WordPacket] :=
    (Tuple.cons expected .nil, Tuple.cons lo .nil, Tuple.cons hi .nil, packet, PUnit.unit)
  let tag := (lastBank [word, pred, pred] WordPacket (args := dataPorts regs)).get .head
  change (andThen tag next).eval (Join.model model) input locals = _
  have picked : SeaOfNodes.Diamond.read model tag input locals = ⟨index (decide (expected = actual))⟩ :=
    congrArg ULift.up (compare_tag actual expected)
  simpa only [decide_eq_true_eq] using andThen_eval tag next input locals _ picked

private theorem covers_cons {slot : ValueSort Width} {slots : List (ValueSort Width)}
    {fact : Fact Word (.value slot)} {value : Val Word (.value slot)}
    {facts : Tuple (Fact Word) (dataPorts slots)} {input : Bank (regs := slots) model} :
    TupleCovers (.cons fact facts) (.cons value input) ↔ fact.Covers value ∧ TupleCovers facts input :=
  ⟨fun covered => ⟨covered .head, fun port => covered (.tail port)⟩, by
    rintro ⟨head, tail⟩ t port
    cases port with
    | head => exact head
    | tail port => exact tail port⟩

private theorem checks_run (facts : Tuple (Fact Word) (dataPorts slots))
    (source : ∀ {s}, Port (dataPorts slots) (.value s) → Port (dataPorts regs) (.value s))
    (input : Bank (regs := regs) model) (pending : Bank (regs := slots) model)
    (reads : ∀ {s} (port : Port (dataPorts slots) (.value s)),
      input.get (source port) = pending.get port) :
    (TupleCovers facts pending → (checks facts source).2.run (Join.model model) input = tagValues true) ∧
    (¬ TupleCovers facts pending → (checks facts source).2.run (Join.model model) input = tagValues false) := by
  induction slots with
  | nil =>
    cases facts
    cases pending
    exact ⟨fun _ => flag_eval (past := []) true input PUnit.unit, fun uncovered =>
      (uncovered (fun port => nomatch port)).elim⟩
  | cons slot slots ih =>
    cases facts with
    | cons fact facts =>
      cases pending with
      | cons value pending =>
        let rest := fun {s} (port : Port (dataPorts slots) (.value s)) => source (.tail port)
        have tail := ih facts rest pending (fun port => reads (.tail port))
        let next := checks facts rest
        have head : input.get (source .head) = value := reads .head
        cases fact with
        | bottom =>
          exact ⟨fun covered => (show False from covered .head).elim,
            fun _ => flag_eval (past := []) false input PUnit.unit⟩
        | overdefined =>
          have covers := covers_cons (fact := (.overdefined : Fact Word (.value slot)))
            (value := value) (facts := facts) (input := pending)
          exact ⟨fun covered => tail.1 (covers.mp covered).2, fun uncovered =>
            tail.2 (fun covered => uncovered (covers.mpr ⟨trivial, covered⟩))⟩
        | constant expected =>
          have covers := covers_cons (fact := .constant expected) (value := value)
            (facts := facts) (input := pending)
          have observed (covered : expected = value) :
              (checks (slots := slot :: slots) (.cons (.constant expected) facts) source).2.run
                (Join.model model) input = next.2.run (Join.model model) input := by
            cases slot with
            | predicate =>
              change (predicateCheck (source .head) expected.down next).2.run (Join.model model) input = _
              rw [predicate_run]
              have same : expected.down = (input.get (source .head)).down :=
                congrArg ULift.down (covered.trans head.symm)
              exact ite_eq_left same
            | data width =>
              change (wordCheck (source .head) expected next).2.run (Join.model model) input = _
              exact (word_run (source .head) expected next input).trans
                (ite_eq_left (covered.trans head.symm))
          have rejected (uncovered : expected ≠ value) :
              (checks (slots := slot :: slots) (.cons (.constant expected) facts) source).2.run
                (Join.model model) input = tagValues false := by
            cases slot with
            | predicate =>
              change (predicateCheck (source .head) expected.down next).2.run (Join.model model) input = _
              rw [predicate_run]
              exact ite_eq_right (fun h => uncovered ((ULift.ext h).trans head))
            | data width =>
              change (wordCheck (source .head) expected next).2.run (Join.model model) input = _
              exact (word_run (source .head) expected next input).trans
                (ite_eq_right (fun (h : expected = input.get (source .head)) => uncovered (h.trans head)))
          refine ⟨fun covered => (observed (covers.mp covered).1).trans
            (tail.1 (covers.mp covered).2), fun uncovered => ?_⟩
          by_cases equal : expected = value
          · exact (observed equal).trans (tail.2 fun yes => uncovered (covers.mpr ⟨equal, yes⟩))
          · exact rejected equal

theorem selector_run [BankDecidableEq Word (dataPorts regs)]
    (facts : Tuple (Fact Word) (dataPorts regs)) (input : Bank (regs := regs) model) :
    ((selector facts).2.toGraph).run (Join.model model) input =
      .cons ⟨index (@decide _ (decideTupleCovers facts input))⟩ .nil := by
  rw [RVSDG.Term.run_toGraph]
  have executed := checks_run facts (fun port => port) input input (fun _ => rfl)
  cases choice : decideTupleCovers facts input with
  | isFalse uncovered => exact executed.2 uncovered
  | isTrue covered => exact executed.1 covered

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Proofs
