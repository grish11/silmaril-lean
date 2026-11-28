module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.CF.Ordered (Block runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (i1)

variable {cells : Nat} {args : List ValueSort}

theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Block.eval (evalBody input) ((lower cells graph).block Label.header) .nil initial =
      match observeActivation graph input initial with
      | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, final)
      | .inr next => (.inl ⟨Label.header, .nil⟩, next) := by
  change (let (raw, final) := runActivation graph input initial
    let values : Env (i1 :: resultTypes) :=
      .cons (BitVec.ofBool ((raw.get .head).down != 0)) (.cons (raw.get (.tail .head)) .nil)
    (((lower cells graph).block Label.header).terminator.eval values, final)) = _
  unfold observeActivation
  rcases runActivation graph input initial with ⟨values, final⟩
  cases values with
  | cons selector words =>
    change (Sum.inl (if (BitVec.ofBool (selector.down != 0)).getLsbD 0 then
      (⟨Label.header, .nil⟩ : Frame Label)
    else ⟨Label.exit, .cons (words.get .head) .nil⟩), final) = _
    by_cases exits : selector.down = 0 <;> simp [exits]

private def fromHeader (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) :=
  let cfg := lower cells graph
  let (result, final) := runBlock cfg.block (Block.eval (evalBody input))
    .nil fuel (cfg.block Label.header) .nil initial
  result.map fun values => (values.get .here, final)

private theorem fromHeader_succ (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) :
    fromHeader graph input (fuel + 1) initial =
      match observeActivation graph input initial with
      | .inl result => if fuel = 0 then none else some result
      | .inr next => fromHeader graph input fuel next := by
  let cfg := lower cells graph
  let eval {scope} (block : Block (Body cells args) Label scope resultTypes) (env : Env scope) :=
    Block.eval (evalBody input) block env
  change (let (outcome, final) := eval (cfg.block Label.header) .nil initial
    let (result, final) : Option (Env resultTypes) × Buffer cells := match outcome with
      | .inl frame => runBlock cfg.block eval .nil fuel (cfg.block frame.label) (frame.args.append .nil) final
      | .inr result => (some result, final)
    result.map fun (values : Env resultTypes) => (values.get .here, final)) = _
  rw [show eval (cfg.block Label.header) .nil initial = _ from header_transition graph input initial]
  cases observeActivation graph input initial with
  | inl result =>
    cases result with
    | mk word final => cases fuel <;> rfl
  | inr next => rfl

private theorem fromHeader_one (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) : fromHeader graph input 1 initial = none := by
  rw [fromHeader_succ]
  cases observeActivation graph input initial <;> rfl

private theorem exact_of_exit (graph : Graph args) (input : Tuple (Val cells) args)
    {initial : Buffer cells} {observed result : Word × Buffer cells}
    (step : observeActivation graph input initial = .inl observed) (budget : Nat) :
    some observed = some result ↔ ∃ count ≤ budget, runAfter graph input count initial = some result := by
  constructor
  · intro h
    exact ⟨0, Nat.zero_le _, by simpa only [runAfter, step, Sum.elim_inl] using h⟩
  · rintro ⟨count, _, evaluated⟩
    cases count with
    | zero => simpa only [runAfter, step, Sum.elim_inl] using evaluated
    | succ _ => simp [runAfter, step] at evaluated

private theorem fromHeader_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) (result : Word × Buffer cells) :
    fromHeader graph input (budget + 2) initial = some result ↔
      ∃ count ≤ budget, runAfter graph input count initial = some result := by
  induction budget generalizing initial with
  | zero =>
    rw [fromHeader_succ]
    cases step : observeActivation graph input initial with
    | inl observed => exact exact_of_exit graph input step 0
    | inr next =>
      change fromHeader graph input 1 next = some result ↔ _
      rw [fromHeader_one]
      simp [runAfter, step]
  | succ budget ih =>
    rw [show budget + 1 + 2 = (budget + 2) + 1 by rfl, fromHeader_succ]
    cases step : observeActivation graph input initial with
    | inl observed => exact exact_of_exit graph input step _
    | inr next =>
      change fromHeader graph input (budget + 2) next = some result ↔ _
      rw [ih next]
      constructor
      · rintro ⟨count, bounded, evaluated⟩
        exact ⟨count + 1, Nat.succ_le_succ bounded, by simpa only [runAfter, step, Sum.elim_inr] using evaluated⟩
      · rintro ⟨count, bounded, evaluated⟩
        cases count with
        | zero => simp [runAfter, step] at evaluated
        | succ count =>
          exact ⟨count, Nat.le_of_succ_le_succ bounded, by simpa only [runAfter, step, Sum.elim_inr] using evaluated⟩

theorem run_eq_some_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) (result : Word × Buffer cells) :
    run graph input budget initial = some result ↔
      ∃ count ≤ budget, runAfter graph input count initial = some result :=
  fromHeader_iff graph input budget initial result

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Proofs
