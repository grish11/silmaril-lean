module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Proofs

open SeaOfNodes.Diamond (ValueSort Val dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Tail.Diamond.MLIR.CF (entryNames entryNames_agree)
open Silmaril.MLIR.Arith (Width Env Var)
open Silmaril.MLIR.CF (Terminator Edge Frame)
open Silmaril.MLIR.Pure (Operands i1)
open Silmaril.MLIR.SCF.For (weakenVar)
open Semantics.Dataflow (Flat)
open RVSDG (Port Tuple)
open Blocks (Bank)

variable {Labels : List Width → Type} {Result : List Width}

private theorem cover_cons {slot : ValueSort Width} {regs : List (ValueSort Width)}
    {fact : Fact Word (.value slot)} {value : Val Word (.value slot)}
    {facts : Tuple (Fact Word) (dataPorts regs)} {input : Bank (regs := regs) model} :
    TupleCovers (.cons fact facts) (.cons value input) ↔ fact.Covers value ∧ TupleCovers facts input :=
  ⟨fun h => ⟨h .head, fun port => h (.tail port)⟩, by
    rintro ⟨head, tail⟩ t port
    cases port with
    | head => exact head
    | tail port => exact tail port⟩

private theorem bits_eq {slot : ValueSort Width} (expected actual : sortValue Word slot) :
    valueBits expected = valueBits actual ↔ expected = actual := by
  cases slot with
  | data => rfl
  | predicate =>
    cases expected with
    | up expected =>
      cases actual with
      | up actual =>
        change BitVec.ofBool expected = BitVec.ofBool actual ↔ ULift.up expected = ULift.up actual
        rw [BitVec.ofBool_eq_iff_eq, ULift.up.injEq]

private theorem unsigned_eq {w : Width} (actual expected : Word w) :
    BitVec.ofBool true + (BitVec.ofBool (expected.ult actual) + BitVec.ofBool (actual.ult expected)) =
      BitVec.ofBool (decide (expected = actual)) := by
  rcases Nat.lt_trichotomy actual.toNat expected.toNat with lt | equal | gt
  · have diff : expected ≠ actual := fun eq => Nat.ne_of_gt lt (congrArg BitVec.toNat eq)
    simp [BitVec.ult_eq_decide, lt, Nat.not_lt_of_gt lt, diff]
  · have eq : expected = actual := BitVec.eq_of_toNat_eq equal.symm
    subst expected
    simp [BitVec.ult_eq_decide]
  · have diff : expected ≠ actual := fun eq => Nat.ne_of_lt gt (congrArg BitVec.toNat eq)
    simp [BitVec.ult_eq_decide, gt, Nat.not_lt_of_gt gt, diff]

private theorem bit_mul (a b : Bool) :
    BitVec.ofBool a * BitVec.ofBool b = BitVec.ofBool (a && b) := by
  cases a <;> cases b <;> rfl

private theorem same_choice {α : Type} {p q : Prop} {decP : Decidable p} {decQ : Decidable q}
    {yes no : α} (agree : p ↔ q) : @ite α p decP yes no = @ite α q decQ yes no :=
  @ite_congr _ _ _ _ _ _ _ decP decQ (propext agree) (fun _ => rfl) (fun _ => rfl)

open scoped Classical in
private theorem eval_tests (accept reject : Labels []) {regs : List (ValueSort Width)} {Γ : List Width}
    (facts : Tuple (Fact Word) (dataPorts regs)) (input : Bank (regs := regs) model)
    (env : Env Γ) (names : ∀ {s}, Port (dataPorts regs) (.value s) → Var Γ (valueWidth s))
    (ok : Var Γ i1) (prior : Bool) (priorBits : env.get ok = BitVec.ofBool prior)
    (reads : ∀ {s} (port : Port (dataPorts regs) (.value s)),
      env.get (names port) = valueBits (input.get port)) :
    (tests (Result := Result) accept reject facts names ok).eval evalOp (fun term env => Terminator.eval env term) env =
      .inl (if prior = true ∧ TupleCovers facts input then ⟨accept, .nil⟩ else ⟨reject, .nil⟩) := by
  induction regs generalizing Γ prior with
  | nil =>
    cases facts
    cases input
    have covered : TupleCovers (.nil : Tuple (Fact Word) []) (.nil : Tuple (Val Word) []) :=
      fun port => nomatch port
    cases prior <;> simp [tests, Silmaril.MLIR.Pure.Code.eval, Terminator.eval, Edge.eval, Operands.eval, priorBits, covered]
  | cons slot regs ih =>
    cases facts with
    | cons fact facts =>
      cases input with
      | cons value input =>
        have tailReads : ∀ {s} (port : Port (dataPorts regs) (.value s)),
            env.get (names (.tail port)) = valueBits (input.get port) := fun port => reads (.tail port)
        rw [tests.eq_def, cover_cons]
        cases fact with
        | bottom => simp [Silmaril.MLIR.Pure.Code.eval, Terminator.eval, Edge.eval, Operands.eval, Flat.Covers]
        | overdefined =>
          change (tests (Result := Result) accept reject facts (fun port => names (.tail port)) ok).eval
            evalOp (fun term env => Terminator.eval env term) env = _
          rw [ih facts input env _ ok prior priorBits tailReads]
          simp [Flat.Covers]
        | constant expected =>
          have headRead : env.get (names .head) = valueBits value := reads .head
          let x := env.get (names .head)
          let y := valueBits expected
          let lt := BitVec.ofBool (x.ult y)
          let gt := BitVec.ofBool (y.ult x)
          let okBits : BitVec 1 := env.get ok
          let eqBits : BitVec 1 := BitVec.ofBool true + (gt + lt)
          let compared : Env ([i1, i1, i1, i1, i1, valueWidth slot] ++ Γ) :=
            .cons eqBits (.cons (BitVec.ofBool true) (.cons (gt + lt) (.cons gt (.cons lt (.cons y env)))))
          let next : Env (i1 :: [i1, i1, i1, i1, i1, valueWidth slot] ++ Γ) :=
            .cons (eqBits * okBits) compared
          let nextNames : ∀ {s}, Port (dataPorts regs) (.value s) →
              Var (i1 :: [i1, i1, i1, i1, i1, valueWidth slot] ++ Γ) (valueWidth s) :=
            fun port => .there (weakenVar (names (.tail port)) [i1, i1, i1, i1, i1, valueWidth slot])
          change (tests (Result := Result) accept reject facts nextNames .here).eval evalOp
            (fun term env => Terminator.eval env term) next = _
          have nextBits : next.get .here = BitVec.ofBool (decide (y = x) && prior) := by
            change (BitVec.ofBool true + (BitVec.ofBool (y.ult x) + BitVec.ofBool (x.ult y))) * okBits = _
            have okRead : okBits = BitVec.ofBool prior := priorBits
            rw [unsigned_eq, okRead, bit_mul]
          rw [ih facts input next nextNames .here _ nextBits (fun port => tailReads port)]
          have decoded : y = x ↔ (Flat.constant expected).Covers value := by
            change y = x ↔ expected = value
            have read : x = valueBits value := headRead
            rw [read]
            exact bits_eq (slot := slot) expected value
          have condition : ((decide (y = x) && prior) = true ∧ TupleCovers facts input) ↔
              prior = true ∧ (Flat.constant expected).Covers value ∧ TupleCovers facts input := by
            rw [Bool.and_eq_true, decide_eq_true_eq, decoded]
            exact ⟨fun ⟨⟨eq, ready⟩, tail⟩ => ⟨ready, eq, tail⟩,
              fun ⟨ready, eq, tail⟩ => ⟨⟨eq, ready⟩, tail⟩⟩
          apply congrArg Sum.inl
          exact same_choice condition

theorem entry_eval (accept reject : Labels []) {regs : List (ValueSort Width)}
    [BankDecidableEq Word (dataPorts regs)] (facts : Tuple (Fact Word) (dataPorts regs))
    (input : Bank (regs := regs) model) :
    (entry (Result := Result) facts accept reject).eval evalOp (fun term env => Terminator.eval env term) (encodeValues input) =
      .inl (if @decide _ (decideTupleCovers facts input) then ⟨accept, .nil⟩ else ⟨reject, .nil⟩) := by
  rw [entry, Silmaril.MLIR.Pure.Code.eval]
  rw [eval_tests accept reject facts input _ _ .here true rfl (entryNames_agree input)]
  cases decideTupleCovers facts input <;> simp_all

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Proofs
