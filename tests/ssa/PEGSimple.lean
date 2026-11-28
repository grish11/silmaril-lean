module

import Silmaril.SSA.PEG.Simple.Thms
import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.SSA.PEG.Simple.Structured.Thms
import Silmaril.SSA.PEG.Thms
import Silmaril.SSA.PEG.Simple.Structured.Completion.Thms
import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Thms
import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Thms
import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Conditional.Thms
import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Recursive.Thms
import Silmaril.SSA.PEG.Rules.Thms
meta import Silmaril.SSA.PEG.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Completion.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Conditional.Defs
meta import Silmaril.SSA.PEG.Simple.While.Defs
meta import Silmaril.SSA.PEG.Simple.Defs

namespace Silmaril.SSA.PEG.Simple.Tests

open RVSDG (Port Tuple)

set_option backward.isDefEq.respectTransparency false

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | add : Op [.count, .count] .count
  | mul : Op [.count, .count] .count
  | pred : Op [.count] .count
  | positive : Op [.count] .bool
  | odd : Op [.count] .bool
  | not : Op [.bool] .bool
  | bad : Op [] .count

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .mul, .cons a (.cons b .nil) => some ⟨a.down * b.down⟩
    | .pred, .cons a .nil => some ⟨a.down - 1⟩
    | .positive, .cons a .nil => some ⟨decide (0 < a.down)⟩
    | .odd, .cons a .nil => some ⟨a.down % 2 == 1⟩
    | .not, .cons a .nil => some ⟨!a.down⟩
    | .bad, _ => none

private def entry (flag : Bool) (n : Nat) : Tuple model.Value [.bool, .count] :=
  .cons ⟨flag⟩ (.cons ⟨n⟩ .nil)

private def prependCount {ts : List (Ty Unit)} (n : Nat) (rest : Tuple model.Value ts) :
    Tuple model.Value (.count :: ts) :=
  .cons ⟨n⟩ rest

private def doubled {ctx : List (Ty Unit)} (slot : Port ctx .count) : Expr Op ctx .count :=
  .op .add (.cons (.var slot) (.cons (.var slot) .nil))

/-- A branch defines the same fresh slot on both paths. The next statement
uses that slot twice. The unchosen false arm has a partial primitive. -/
private def branchThenAssign : Program Op false [.bool, .count] .count where
  locals := [.count, .count, .bool, .count]
  body := .seq
    (.branch (.var .head) (.assign (doubled (.tail .head))) (.assign (.op .bad .nil)))
    (.assign (doubled .head))
  retvar := .head

private theorem branchReturns : branchThenAssign.Returns model (entry true 2) ⟨8⟩ := by
  refine ⟨.cons ⟨8⟩ (.cons ⟨4⟩ (entry true 2)), ?_, rfl⟩
  change Exec model (.seq (.branch (.var .head) (.assign (doubled (.tail .head)))
      (.assign (.op .bad .nil))) (.assign (doubled .head))) (entry true 2) _
  exact .seq (next := prependCount 4 (entry true 2))
    (.branchTrue rfl (.assign rfl)) (.assign rfl)

private noncomputable def observe {params : List (Ty Unit)} {t : Ty Unit}
    (p : Program Op false params t) (input : Tuple model.Value params) :
    Tuple (fun ty => Option (model.Value ty)) [t] :=
  p.translate.observe model
    (p.translate.denote model input (p.translate.demandWellFounded p.translate_wellFormed)) Index.zero

example : observe branchThenAssign (entry true 2) = .cons (some ⟨8⟩) .nil :=
  branchThenAssign.translate_returns model (entry true 2) branchReturns Index.zero

example : branchThenAssign.Fails model (entry false 2) := by
  change Exec model (.seq (.branch (.var .head) (.assign (doubled (.tail .head)))
      (.assign (.op .bad .nil))) (.assign (doubled .head))) (entry false 2) none
  exact .firstFailed (.branchFalse rfl (.assignFailed rfl))

-- Two parameters, the two arm expressions, three join results and the last instruction.
example : branchThenAssign.lower.nodes.length = 8 := by decide
example : refNumbers (branchThenAssign.translate.node ⟨0, by decide⟩).args = [1, 1] := by decide

private def chooseOld : Program Op false [.bool, .count] .count where
  locals := [.count]
  body := .branch (.var .head)
    (.seq (.assign (.op .bad .nil)) (.project (.cons .head .nil)))
    (.project (.cons (.tail .head) .nil))
  retvar := .head

example : observe chooseOld (entry false 31) = .cons (some ⟨31⟩) .nil := by
  refine chooseOld.translate_returns model (entry false 31) ?_ Index.zero
  exact ⟨.cons ⟨31⟩ .nil, .branchFalse rfl .project, rfl⟩

/-- The source still executes the discarded assignment. The PEG return
is allowed to depend only on the original parameter. -/
private def discardedFailure : Program Op false [.count] .count where
  locals := [.count]
  body := .seq (.assign (.op .bad .nil)) (.project (.cons (.tail .head) .nil))
  retvar := .head

private def seven : Tuple model.Value [.count] := .cons ⟨7⟩ .nil

example : discardedFailure.Fails model seven :=
  .firstFailed (.assignFailed rfl)

example : observe discardedFailure seven = .cons (some ⟨7⟩) .nil := by
  unfold observe Program.translate
  rw [Code.observe_toGraph]
  rfl

/-- The factorial body carries accumulator and counter. -/
private def factorialBody : Stmt Op false [.count, .count] [.count, .count] :=
  .seq (.assign (.op .mul (.cons (.var .head) (.cons (.var (.tail .head)) .nil))))
    (.seq (.assign (.op .pred (.cons (.var (.tail (.tail .head))) .nil)))
      (.project (.cons (.tail .head) (.cons .head .nil))))

private def factorialGuard : Expr Op [.count, .count] .bool :=
  .op .positive (.cons (.var (.tail .head)) .nil)

private def carry (acc n : Nat) : Tuple model.Value [.count, .count] :=
  .cons ⟨acc⟩ (.cons ⟨n⟩ .nil)

private def falling (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => falling (acc * (n + 1)) n

private theorem factorialStep (acc n : Nat) :
    Exec model factorialBody.enableWhile (carry acc (n + 1)) (some (carry (acc * (n + 1)) n)) :=
  .seq (next := prependCount (acc * (n + 1)) (carry acc (n + 1))) (.assign rfl)
    (.seq (next := prependCount n (prependCount (acc * (n + 1)) (carry acc (n + 1))))
      (.assign rfl) .project)

private theorem factorialExec (acc n : Nat) :
    Exec model (.while rfl factorialGuard factorialBody.enableWhile) (carry acc n)
      (some (carry (falling acc n) 0)) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih => exact .whileStep rfl (factorialStep acc n) (ih (acc * (n + 1)))

private def factorial : WhileProgram Op [.count, .count] .count where
  guard := factorialGuard
  body := factorialBody
  retvar := .head

/-- Manually wired Trans-While instance. Both θ nodes share the iteration
coordinate, and both live variables use the same pass node. -/
private def factorialRaw : RawGraph Op [.count, .count] [.count, .count] 11 1 where
  forest := ⟨fun _ => none⟩
  sort i := if i = 6 ∨ i = 7 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .theta 0, [2, 4]⟩
    | 1 => ⟨_, .theta 0, [3, 5]⟩
    | 2 => ⟨_, .param .head, []⟩
    | 3 => ⟨_, .param (.tail .head), []⟩
    | 4 => ⟨_, .op .mul, [0, 1]⟩
    | 5 => ⟨_, .op .pred, [1]⟩
    | 6 => ⟨_, .op .positive, [1]⟩
    | 7 => ⟨_, .op .not, [6]⟩
    | 8 => ⟨_, .pass 0, [7]⟩
    | 9 => ⟨_, .eval 0, [0, 8]⟩
    | 10 => ⟨_, .eval 0, [1, 8]⟩
  roots := [9, 10]

private def factorialGraph : Graph Op [.count, .count] [.count, .count] 11 1 :=
  factorialRaw.check.get (by decide)

private def factorialRank : DemandRank 11 1 :=
  [.phase fun i => match i with
    | 6 => 1
    | 7 => 2
    | 8 => 3
    | 9 | 10 => 4
    | _ => 0,
   .counter 0,
   .phase fun i => match i with
    | 0 | 1 => 1
    | 4 | 5 => 2
    | _ => 0]

private noncomputable def factorialValue (acc n : Nat) : factorialGraph.Valuation model :=
  factorialGraph.denote model (carry acc n)
    (factorialGraph.demandWellFounded_of_check factorialRank (by decide))

private theorem factorialEq (acc n : Nat) (q : Request 11 1) :
    factorialValue acc n q = factorialGraph.equation model (carry acc n) (factorialValue acc n) q :=
  factorialGraph.denote_solves model (carry acc n) _ q

private def clock (k : Nat) : Index 1 := fun _ => k

private theorem setClock (k j : Nat) : (clock k).set 0 j = clock j := by
  funext i
  have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst i
  rfl

/-- The executable loop body can also be sampled beyond the first exit.
Only the prefix through that exit is used below. -/
private def accumulator (acc n : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => accumulator acc n k * (n - k)

private theorem collectSingle (t : Ty Unit) (read : (slot : Fin [t].length) →
    Option (model.Value [t][slot])) :
    collect [t] read = (read 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases read 0 <;> rfl

private theorem collectPair (read : (slot : Fin [Ty.count, Ty.count].length) →
    Option (model.Value [Ty.count, Ty.count][slot])) :
    collect [.count, .count] read =
      (read 0).bind (fun x => (read (0 : Fin 1).succ).map (fun y => .cons x (.cons y .nil))) := by
  unfold collect
  rw [collectSingle]
  cases read 0 <;> cases read (0 : Fin 1).succ <;> rfl

private theorem factorialSamples (acc n k : Nat) :
    factorialValue acc n (0, clock k) = some ⟨accumulator acc n k⟩ ∧
    factorialValue acc n (1, clock k) = some ⟨n - k⟩ := by
  induction k with
  | zero =>
    exact ⟨(factorialEq acc n (0, clock 0)).trans (factorialEq acc n (2, clock 0)),
      (factorialEq acc n (1, clock 0)).trans (factorialEq acc n (3, clock 0))⟩
  | succ k ih =>
    have a := factorialEq acc n (0, clock (k + 1))
    have b := factorialEq acc n (1, clock (k + 1))
    change factorialValue acc n (0, clock (k + 1)) =
      factorialValue acc n (4, (clock (k + 1)).set 0 k) at a
    change factorialValue acc n (1, clock (k + 1)) =
      factorialValue acc n (5, (clock (k + 1)).set 0 k) at b
    rw [setClock] at a b
    have mul := factorialEq acc n (4, clock k)
    have pred := factorialEq acc n (5, clock k)
    change _ = (collect (F := model.Value) [.count, .count] _).elim none (model.run .mul) at mul
    change _ = (collect (F := model.Value) [.count] _).elim none (model.run .pred) at pred
    rw [collectPair] at mul
    rw [collectSingle] at pred
    change _ = ((factorialValue acc n (0, clock k)).bind
      (fun x => (factorialValue acc n (1, clock k)).map (fun y => .cons x (.cons y .nil)))).elim
        none (model.run .mul) at mul
    change _ = ((factorialValue acc n (1, clock k)).map (fun x => .cons x .nil)).elim
      none (model.run .pred) at pred
    rw [ih.1, ih.2] at mul
    rw [ih.2] at pred
    have dec : n - k - 1 = n - (k + 1) := by omega
    exact ⟨a.trans mul, b.trans (pred.trans (congrArg (fun x => some (ULift.up x)) dec))⟩

private theorem factorialExit (acc n k : Nat) :
    factorialValue acc n (7, clock k) = some ⟨decide (n ≤ k)⟩ := by
  have positive := factorialEq acc n (6, clock k)
  have exit := factorialEq acc n (7, clock k)
  change _ = (collect (F := model.Value) [.count] _).elim none (model.run .positive) at positive
  change _ = (collect (F := model.Value) [.bool] _).elim none (model.run .not) at exit
  rw [collectSingle] at positive exit
  change _ = ((factorialValue acc n (1, clock k)).map (fun x => .cons x .nil)).elim
    none (model.run .positive) at positive
  change _ = ((factorialValue acc n (6, clock k)).map (fun x => .cons x .nil)).elim
    none (model.run .not) at exit
  rw [exit, positive, (factorialSamples acc n k).2]
  change some (ULift.up (!decide (0 < n - k))) = some (ULift.up (decide (n ≤ k)))
  by_cases h : n ≤ k
  · have zero : n - k = 0 := by omega
    simp [h, zero]
  · have pos : 0 < n - k := by omega
    simp [h, pos]

private theorem factorialPass (acc n : Nat) :
    factorialValue acc n (8, clock 0) = some ⟨n⟩ := by
  have e := factorialEq acc n (8, clock 0)
  change _ =
    (firstTrue (fun k => (factorialValue acc n (7, (clock 0).set 0 k)).map ULift.down)).map ULift.up at e
  have stream : (fun k => (factorialValue acc n (7, (clock 0).set 0 k)).map ULift.down) =
      fun k => some (decide (n ≤ k)) := by
    funext k
    rw [setClock, factorialExit]
    rfl
  have least : firstTrue (fun k => some (decide (n ≤ k))) = some n := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨by simp, fun _ _ => rfl⟩, ?_⟩
    intro j hj hit
    have defined := ((monotonize_eq_some_iff _ _ _).mp hit).1
    simp [Nat.not_le_of_lt hj] at defined
  rw [e, stream, least]
  rfl

private theorem factorialEval (acc n : Nat) :
    factorialGraph.observe model (factorialValue acc n) (clock 0) =
      .cons (some ⟨accumulator acc n n⟩) (.cons (some ⟨0⟩) .nil) := by
  have a := factorialEq acc n (9, clock 0)
  have b := factorialEq acc n (10, clock 0)
  change _ = (factorialValue acc n (8, clock 0)).elim none
    (fun k => monotonize (fun j => factorialValue acc n (0, (clock 0).set 0 j)) k.down) at a
  change _ = (factorialValue acc n (8, clock 0)).elim none
    (fun k => monotonize (fun j => factorialValue acc n (1, (clock 0).set 0 j)) k.down) at b
  rw [factorialPass] at a b
  change _ = monotonize (fun j => factorialValue acc n (0, (clock 0).set 0 j)) n at a
  change _ = monotonize (fun j => factorialValue acc n (1, (clock 0).set 0 j)) n at b
  have accAtExit := (monotonize_eq_some_iff (fun j => factorialValue acc n (0, (clock 0).set 0 j))
    n (ULift.up (accumulator acc n n))).mpr
    ⟨by rw [setClock, (factorialSamples acc n n).1], fun j _ => by
      rw [setClock, (factorialSamples acc n j).1]
      rfl⟩
  have countAtExit := (monotonize_eq_some_iff (fun j => factorialValue acc n (1, (clock 0).set 0 j))
    n (ULift.up 0)).mpr
    ⟨by rw [setClock, (factorialSamples acc n n).2, Nat.sub_self], fun j _ => by
      rw [setClock, (factorialSamples acc n j).2]
      rfl⟩
  change (Tuple.cons (F := fun t => Option (model.Value t)) (t := .count)
    (factorialValue acc n (9, clock 0))
    (.cons (t := .count) (factorialValue acc n (10, clock 0)) .nil)) = _
  rw [a, b, accAtExit, countAtExit]

private theorem accumulatorShift (acc n k : Nat) :
    accumulator acc (n + 1) (k + 1) = accumulator (acc * (n + 1)) n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change accumulator acc (n + 1) (k + 1) * ((n + 1) - (k + 1)) =
      accumulator (acc * (n + 1)) n k * (n - k)
    rw [ih, Nat.succ_sub_succ_eq_sub]

private theorem accumulatorExit (acc n : Nat) :
    accumulator acc n n = falling acc n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => exact (accumulatorShift acc n n).trans (ih (acc * (n + 1)))

/-- Every successful execution of the factorial source agrees with the
manually wired graph's accumulator result. -/
private theorem factorialPreserves (acc n : Nat) {value : model.Value .count}
    (run : factorial.source.Returns model (carry acc n) value) :
    factorialGraph.observe model (factorialValue acc n) (clock 0) =
      .cons (some value) (.cons (some ⟨0⟩) .nil) := by
  obtain ⟨final, exec, returned⟩ := run
  have same := Option.some.inj (exec.deterministic (factorialExec acc n))
  subst final
  rw [factorialEval, accumulatorExit, ← returned]
  rfl

example : factorialGraph.observe model (factorialValue 1 10) (clock 0) =
    .cons (some ⟨3628800⟩) (.cons (some ⟨0⟩) .nil) :=
  factorialPreserves 1 10 ⟨carry 3628800 0, factorialExec 1 10, rfl⟩

example : factorialGraph.observe model (factorialValue 7 0) (clock 0) =
    .cons (some ⟨7⟩) (.cons (some ⟨0⟩) .nil) :=
  factorialPreserves 7 0 ⟨carry 7 0, factorialExec 7 0, rfl⟩

private noncomputable def automatic {params : List (Ty Unit)} {t : Ty Unit}
    (p : WhileProgram Op params t) (input : Tuple model.Value params) :
    Tuple (fun ty => Option (model.Value ty)) [t] :=
  (p.translate .not).observe model
    ((p.translate .not).denote model input (p.translate_demandWellFounded .not)) (clock 0)

private theorem factorialCompiled (acc n : Nat) :
    automatic factorial (carry acc n) = .cons (some ⟨falling acc n⟩) .nil :=
  factorial.translate_returns .not model (carry acc n) (fun _ => rfl)
    ⟨carry (falling acc n) 0, factorialExec acc n, rfl⟩ (clock 0)

example : automatic factorial (carry 1 10) = .cons (some ⟨3628800⟩) .nil :=
  factorialCompiled 1 10

example : automatic factorial (carry 7 0) = .cons (some ⟨7⟩) .nil :=
  factorialCompiled 7 0

/-- The guard and the body make independent choices. The unchosen body arm
applies a primitive that always fails. -/
private def branchingLoop : WhileProgram Op [.count, .count] .count where
  guard := factorialGuard
  body := .branch (.op .positive (.cons (.var .head) .nil)) factorialBody
    (.seq (.assign (.op .bad .nil))
      (.project (.cons (.tail .head) (.cons (.tail (.tail .head)) .nil))))
  retvar := .head

private theorem branchingReturns : branchingLoop.source.Returns model (carry 2 1) ⟨2⟩ := by
  refine ⟨carry 2 0, ?_, rfl⟩
  exact .whileStep rfl (.branchTrue rfl (factorialStep 2 0)) (.whileStop rfl)

example : automatic branchingLoop (carry 2 1) = .cons (some ⟨2⟩) .nil :=
  branchingLoop.translate_returns .not model (carry 2 1) (fun _ => rfl) branchingReturns (clock 0)

example : branchingLoop.source.Fails model (carry 0 1) :=
  .whileBodyFailed rfl (.branchFalse rfl (.firstFailed (.assignFailed rfl)))

example : factorial.rank.check (factorial.translate .not) = true := by decide
example : (branchingLoop.translate .not).WellFormed := branchingLoop.translate_wellFormed .not

private noncomputable def structured {params : List (Ty Unit)} {t : Ty Unit}
    (p : Program Op true params t) (input : Tuple model.Value params) :
    Tuple (fun ty => Option (model.Value ty)) [t] :=
  let g := Structured.translate p .not
  g.observe model (g.denote model input (Structured.translate_demandWellFounded p .not)) (fun _ => 17)

/-- The second while is selected by a branch and initialized using the first
while's exit. The alternative contains a failing primitive. -/
private def siblingLoops : Program Op true [.count, .count] .count where
  locals := [.count, .count]
  body := .seq factorial.source.body
    (.branch (.op .positive (.cons (.var .head) .nil))
      (.seq (.project (.cons .head (.cons .head .nil))) factorial.source.body)
      (.seq (.assign (.op .bad .nil))
        (.project (.cons (.tail .head) (.cons (.tail (.tail .head)) .nil)))))
  retvar := .head

private theorem siblingReturns : siblingLoops.Returns model (carry 1 3) ⟨4320⟩ := by
  refine ⟨carry 4320 0, ?_, rfl⟩
  exact .seq (next := carry 6 0) (factorialExec 1 3)
    (.branchTrue rfl (.seq (next := carry 6 6) .project (factorialExec 6 6)))

example : structured siblingLoops (carry 1 3) = .cons (some ⟨4320⟩) .nil :=
  Structured.translate_returns siblingLoops .not model (carry 1 3) (fun _ => rfl)
    siblingReturns (fun _ => 17)

private def triple (acc outer inner : Nat) : Tuple model.Value [.count, .count, .count] :=
  .cons ⟨acc⟩ (.cons ⟨outer⟩ (.cons ⟨inner⟩ .nil))

private def innerTest : Expr Op [.count, .count, .count] .bool :=
  .op .positive (.cons (.var (.tail (.tail .head))) .nil)

private def innerSlice : Stmt Op false [.count, .count, .count] [.count, .count, .count] :=
  .seq (.assign (.op .add (.cons (.var .head) (.cons (.var (.tail (.tail .head))) .nil))))
    (.seq (.assign (.op .pred (.cons (.var (.tail (.tail (.tail .head)))) .nil)))
      (.project (.cons (.tail .head) (.cons (.tail (.tail (.tail .head))) (.cons .head .nil)))))

private def innerBody := innerSlice.enableWhile

private def innerLoop : Stmt Op true [.count, .count, .count] [.count, .count, .count] :=
  .while rfl innerTest innerBody

private def innerResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => innerResult (acc + (k + 1)) k

private theorem innerTrace (acc outer k : Nat) :
    WhileTrace model innerTest innerBody k (triple acc outer k) (triple (innerResult acc k) outer 0) := by
  induction k generalizing acc with
  | zero => exact .stop rfl
  | succ k ih =>
    apply WhileTrace.step (next := triple (acc + (k + 1)) outer k) rfl ?_ (ih _)
    exact .seq (next := prependCount (acc + (k + 1)) (triple acc outer (k + 1))) (.assign rfl)
      (.seq (next := prependCount k (prependCount (acc + (k + 1)) (triple acc outer (k + 1))))
        (.assign rfl) .project)

private theorem innerExec (acc outer k : Nat) :
    Exec model innerLoop (triple acc outer k) (some (triple (innerResult acc k) outer 0)) :=
  (innerTrace acc outer k).exec

private def outerTest : Expr Op [.count, .count, .count] .bool :=
  .op .positive (.cons (.var (.tail .head)) .nil)

private def outerCapture :
    Tuple (Port ([.count, .count, .count] : List (Ty Unit))) [.count, .count, .count] :=
  .cons .head (.cons (.tail .head) (.cons (.tail .head) .nil))

private def outerCommit : Stmt Op false [.count, .count, .count] [.count, .count, .count] :=
  .seq (.assign (.op .pred (.cons (.var (.tail .head)) .nil)))
    (.project (.cons (.tail .head) (.cons .head (.cons (.tail (.tail (.tail .head))) .nil))))

private def outerBody : Stmt Op true [.count, .count, .count] [.count, .count, .count] :=
  .seq (.project outerCapture) (.seq innerLoop outerCommit.enableWhile)

private def outerResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => outerResult (innerResult acc (k + 1)) k

private theorem outerStep (acc k : Nat) :
    Exec model outerBody (triple acc (k + 1) 0) (some (triple (innerResult acc (k + 1)) k 0)) :=
  .seq (next := triple acc (k + 1) (k + 1)) .project
    (.seq (next := triple (innerResult acc (k + 1)) (k + 1) 0) (innerExec acc (k + 1) (k + 1))
      (.seq (next := prependCount k (triple (innerResult acc (k + 1)) (k + 1) 0))
        (.assign rfl) .project))

private theorem outerExec (acc k : Nat) :
    Exec model (.while rfl outerTest outerBody) (triple acc k 0)
      (some (triple (outerResult acc k) 0 0)) := by
  induction k generalizing acc with
  | zero => exact .whileStop rfl
  | succ k ih => exact .whileStep rfl (outerStep acc k) (ih _)

/-- The inner loop's trip count is the current outer counter. For an outer
input of three the inner exits occur at three, two and one, respectively. -/
private def nestedLoops : Program Op true [.count, .count, .count] .count where
  locals := [.count, .count, .count]
  body := .while rfl outerTest outerBody
  retvar := .head

private def nestedToken : Structured.Token.Nested.Form Op [.count, .count, .count]
    [.count, .count, .count] .count where
  guard := outerTest
  capture := outerCapture
  childGuard := innerTest
  childBody := Structured.Token.Body.ofStmt innerSlice
  commit := Structured.Token.Body.ofStmt outerCommit
  result := .head

example : nestedToken.source = nestedLoops := rfl

-- The two child traces have lengths two and one. The second starts with
-- the accumulator returned by the first and a fresh count of one.
example : WhileTrace model innerTest innerBody 2 (triple 0 2 2) (triple 3 2 0) ∧
    WhileTrace model innerTest innerBody 1 (triple 3 1 1) (triple 4 1 0) :=
  ⟨innerTrace 0 2 2, innerTrace 3 1 1⟩

private def nestedTokenBase : Index (nestedToken.program .not).nodes.length := fun _ => 0

private theorem nestedTokenReturns :
    nestedToken.observe .not model (triple 0 2 0) nestedTokenBase =
      .cons (some ⟨4⟩) (.cons (some ⟨true⟩) .nil) :=
  nestedToken.observe_of_returns .not model _ (fun _ => rfl) nestedTokenBase
    ⟨triple 4 0 0, outerExec 0 2, rfl⟩

example : nestedLoops.Returns model (triple 0 2 0) ⟨4⟩ := by
  have done : ((nestedToken.observe .not model (triple 0 2 0) nestedTokenBase).get
      (.tail .head)).isSome := by rw [nestedTokenReturns]; rfl
  obtain ⟨value, returned, roots⟩ :=
    nestedToken.returns_of_completion .not model _ (fun _ => rfl) nestedTokenBase done
  rw [nestedTokenReturns] at roots
  have eq := congrArg (fun xs : Tuple (fun t => Option (model.Value t)) [.count, .bool] =>
    xs.get .head) roots
  cases Option.some.inj eq
  exact returned

private def conditionalToken : Structured.Token.Nested.Conditional.Form Op [.count, .count, .count]
    [.count, .count, .count] .count where
  parent := nestedToken
  selectChild := .op .odd (.cons (.var (.tail .head)) .nil)
  skip := Structured.Token.Body.ofStmt outerCommit

-- Take with child count three, skip at two, then take with fresh count
-- one. The skipped step retains accumulator six.
private theorem mixedTrace : WhileTrace model outerTest conditionalToken.step 3
    (triple 0 3 0) (triple 7 0 0) :=
  .step (next := triple 6 2 0) rfl (.branchTrue rfl (outerStep 0 2))
    (.step (next := triple 6 1 0) rfl
      (.branchFalse rfl (outerCommit.runLoopFree_enableWhile (triple 6 2 0)))
      (.step (next := triple 7 0 0) rfl (.branchTrue rfl (outerStep 6 0)) (.stop rfl)))

private def conditionalBase : Index (conditionalToken.program .not).nodes.length := fun _ => 0

private theorem mixedObservation :
    conditionalToken.observe .not model (triple 0 3 0) conditionalBase =
      .cons (some ⟨7⟩) (.cons (some ⟨true⟩) .nil) :=
  conditionalToken.observe_of_returns .not model _ (fun _ => rfl) conditionalBase
    ⟨triple 7 0 0, mixedTrace.exec, rfl⟩

example : conditionalToken.source.Returns model (triple 0 3 0) ⟨7⟩ := by
  have done : ((conditionalToken.observe .not model (triple 0 3 0) conditionalBase).get
      (.tail .head)).isSome := by rw [mixedObservation]; rfl
  obtain ⟨value, returned, roots⟩ :=
    conditionalToken.returns_of_completion .not model _ (fun _ => rfl) conditionalBase done
  rw [mixedObservation] at roots
  have eq := congrArg (fun xs : Tuple (fun t => Option (model.Value t)) [.count, .bool] =>
    xs.get .head) roots
  cases Option.some.inj eq
  exact returned

example : Structured.Token.Recursive.observe nestedLoops .not model (triple 0 2 0) (fun _ => 0) =
    .cons (some ⟨4⟩) (.cons (some ⟨true⟩) .nil) :=
  Structured.Token.Recursive.observe_of_returns nestedLoops .not model _ (fun _ => rfl) _
    ⟨triple 4 0 0, outerExec 0 2, rfl⟩

example : Structured.Token.Recursive.observe conditionalToken.source .not model (triple 0 3 0) (fun _ => 0) =
    .cons (some ⟨7⟩) (.cons (some ⟨true⟩) .nil) :=
  Structured.Token.Recursive.observe_of_returns conditionalToken.source .not model _ (fun _ => rfl) _
    ⟨triple 7 0 0, mixedTrace.exec, rfl⟩

private def threeLevels : Program Op true [.count, .count, .count] .count :=
  ⟨[.count, .count, .count], .while rfl outerTest nestedLoops.body, .head⟩

private theorem deeperObservation :
    Structured.Token.Recursive.observe threeLevels .not model (triple 0 2 0) (fun _ => 0) =
      .cons (some ⟨4⟩) (.cons (some ⟨true⟩) .nil) :=
  Structured.Token.Recursive.observe_of_returns threeLevels .not model _ (fun _ => rfl) _
    ⟨triple 4 0 0, .whileStep rfl (outerExec 0 2) (.whileStop rfl), rfl⟩

example : threeLevels.Returns model (triple 0 2 0) ⟨4⟩ := by
  have done : ((Structured.Token.Recursive.observe threeLevels .not model (triple 0 2 0) (fun _ => 0)).get
      (.tail .head)).isSome := by rw [deeperObservation]; rfl
  obtain ⟨_, ran, roots⟩ := Structured.Token.Recursive.returns_of_completion threeLevels .not model _ (fun _ => rfl) _ done
  rw [deeperObservation] at roots
  have data := congrArg (fun xs : Tuple (fun t => Option (model.Value t)) [.count, .bool] =>
    xs.get .head) roots
  cases Option.some.inj data
  exact ran

-- The zero-trip loop retains the data input even when the preceding
-- strict assignment failed. Its marker must still sample the incoming one.
private def discardBeforeWhile : Program Op true [.count] .count :=
  ⟨[.count], .seq (.assign (.op .bad .nil))
    (.seq (.project (.cons (.tail .head) .nil))
      (.while rfl (.op .positive (.cons (.var .head) .nil)) (.project (.cons .head .nil)))), .head⟩

private def droppedGraph : Graph (Structured.Token.Opcode Op) [.count] [.count, .bool] 11 11 :=
  Structured.Token.Recursive.translate discardBeforeWhile .not

private def inputZero : Tuple model.Value [.count] := .cons ⟨0⟩ .nil
private def droppedBase : Index 11 := fun _ => 0
private def droppedRef (j : Fin 11) {t : Ty Unit} (typed : droppedGraph.sort j = t) :
    Ref droppedGraph.sort t := ⟨j, typed⟩

private noncomputable def droppedValues : droppedGraph.Valuation (Structured.Token.model model) :=
  droppedGraph.denote (Structured.Token.model model) inputZero
    (Structured.Token.Recursive.translate_demandWellFounded discardBeforeWhile .not)

private theorem droppedData :
    (Structured.Token.Recursive.observe discardBeforeWhile .not model inputZero droppedBase).get .head = some ⟨0⟩ := by
  have eq := droppedGraph.denote_solves (Structured.Token.model model) inputZero
    (Structured.Token.Recursive.translate_demandWellFounded discardBeforeWhile .not)
  change droppedGraph.Solves (Structured.Token.model model) inputZero droppedValues at eq
  have seed : Rules.readRef droppedValues (droppedRef 6 (t := .count) rfl) (droppedBase.set 2 0) = some ⟨0⟩ :=
    (Rules.theta_zero eq (r := droppedRef 6 (t := .count) rfl) (initial := droppedRef 10 rfl)
      (feedback := droppedRef 6 rfl) (loop := 2) HEq.rfl rfl).trans
      (Rules.at_label eq (r := droppedRef 10 rfl) (label := .param .head) (args := .nil) HEq.rfl _)
  have first : Rules.readRef droppedValues (droppedRef 2 (t := .count) rfl) droppedBase = some ⟨0⟩ := by
    rw [Rules.pass_at eq (r := droppedRef 2 rfl) (cond := droppedRef 3 rfl) (loop := 2) HEq.rfl]
    let flags := fun k => (Rules.readRef droppedValues (droppedRef 3 (t := .bool) rfl)
      (droppedBase.set 2 k)).map ULift.down
    have picked : firstTrue flags = some 0 := (firstTrue_eq_some_iff_samples flags 0).mpr ⟨by
      unfold flags
      rw [Rules.unary_at eq (r := droppedRef 3 rfl) (arg := droppedRef 4 rfl)
        (op := .source Op.not) HEq.rfl,
        Rules.unary_at eq (r := droppedRef 4 rfl) (arg := droppedRef 6 rfl)
          (op := .source Op.positive) HEq.rfl, seed]
      rfl, fun j prior => by omega⟩
    change (firstTrue flags).map ULift.up = _
    rw [picked]
    rfl
  change Rules.readRef droppedValues (droppedRef 1 (t := .count) rfl) droppedBase = _
  rw [Rules.eval_at eq (r := droppedRef 1 (t := .count) rfl) (source := droppedRef 6 rfl)
    (count := droppedRef 2 rfl) (loop := 2) HEq.rfl, first]
  change monotonize (fun k => Rules.readRef droppedValues (droppedRef 6 (t := .count) rfl)
    (droppedBase.set 2 k)) 0 = some ⟨0⟩
  exact (monotonize_eq_some_iff _ 0 _).mpr ⟨seed, fun j prior => by omega⟩

example : (Structured.Token.Recursive.observe discardBeforeWhile .not model inputZero droppedBase).get .head = some ⟨0⟩ ∧
    (Structured.Token.Recursive.observe discardBeforeWhile .not model inputZero droppedBase).get (.tail .head) = none := by
  refine ⟨droppedData, ?_⟩
  have failed : discardBeforeWhile.Fails model inputZero := .firstFailed (.assignFailed rfl)
  cases marker : (Structured.Token.Recursive.observe discardBeforeWhile .not model inputZero droppedBase).get
      (.tail .head) with
  | none => rfl
  | some bit =>
    have done : ((Structured.Token.Recursive.observe discardBeforeWhile .not model inputZero droppedBase).get
        (.tail .head)).isSome := by rw [marker]; rfl
    obtain ⟨_, ⟨_, ran, _⟩, _⟩ :=
      Structured.Token.Recursive.returns_of_completion discardBeforeWhile .not model inputZero (fun _ => rfl) droppedBase done
    cases failed.deterministic ran

example (acc n : Nat) : structured nestedLoops (triple acc n 0) =
    .cons (some ⟨outerResult acc n⟩) .nil :=
  Structured.translate_returns nestedLoops .not model (triple acc n 0) (fun _ => rfl)
    ⟨triple (outerResult acc n) 0 0, outerExec acc n, rfl⟩ (fun _ => 17)

example : structured nestedLoops (triple 0 3 0) = .cons (some ⟨10⟩) .nil :=
  Structured.translate_returns nestedLoops .not model (triple 0 3 0) (fun _ => rfl)
    ⟨triple 10 0 0, outerExec 0 3, rfl⟩ (fun _ => 17)

private def passParents {params : List (Ty Unit)} (p : Program Op true params .count) :
    List (Nat × Option Nat) :=
  let g := Structured.translate p .not
  (List.finRange (Structured.program p .not).nodes.length).filterMap fun i =>
    (Structured.passLoop (g.node i).label).map fun loop =>
      (loop.val, (g.forest.parent loop).map Fin.val)

#guard match passParents siblingLoops with
  | [(a, none), (b, none)] => a < b
  | _ => False

#guard match passParents nestedLoops with
  | [(outer, none), (inner, some parent)] => parent = outer ∧ outer < inner
  | _ => False

-- The structural admission also supplies existence and uniqueness for the
-- graph whose inner trip count changes with the enclosing iteration.
example :
    ∃! value, (Structured.translate nestedLoops .not).Solves model (triple 0 3 0) value :=
  (Structured.translate nestedLoops .not).existsUnique_solves_of_wellFormed model (triple 0 3 0)
    (Structured.translate_wellFormed nestedLoops .not)

example : (Structured.translate siblingLoops .not).Scoped :=
  (Structured.translate_wellFormed siblingLoops .not).loopScope

example : (Structured.translate nestedLoops .not).OuterFeedbackCycles :=
  (Structured.translate_wellFormed nestedLoops .not).outerFeedback

private def nestedIdentity : Program Op true [.bool] .bool where
  locals := [.bool]
  body := .while rfl (.var .head)
    (.while rfl (.var .head) (.project (.cons .head .nil)))
  retvar := .head

private def nestedId (i : Fin 9) : Fin (Structured.program nestedIdentity .not).nodes.length := i

/-- The outer θ depends on the inner exit. This cycle traverses the
inner eval's index edge and the shared pass. -/
private theorem nestedIndexCycle :
    let g := Structured.translate nestedIdentity .not
    Walk g.Edge (nestedId 7)
      [.feedback (nestedId 1), .index (nestedId 4), .sample (nestedId 4),
        .ordinary, .initial (nestedId 4)] (nestedId 7) := by
  dsimp only
  refine .cons (b := nestedId 3) ⟨⟨1, by decide⟩, rfl, rfl⟩ ?_
  refine .cons (b := nestedId 4) ⟨⟨1, by decide⟩, rfl, rfl⟩ ?_
  refine .cons (b := nestedId 5) ⟨⟨0, by decide⟩, rfl, rfl⟩ ?_
  refine .cons (b := nestedId 6) ⟨⟨0, by decide⟩, rfl, rfl⟩ ?_
  exact .cons ⟨⟨0, by decide⟩, rfl, rfl⟩ (.nil _)

example : (Structured.translate nestedIdentity .not).forest.StrictlyEncloses (nestedId 1) (nestedId 4) := by
  have wf := Structured.translate_wellFormed nestedIdentity .not
  obtain ⟨outer, encloses, feedback⟩ := wf.outerFeedback _ _ nestedIndexCycle
    (.index (nestedId 4)) (by simp) (nestedId 4) (.inr rfl)
  have onlyOuter : outer = nestedId 1 := by simpa using feedback
  rwa [onlyOuter] at encloses

end Silmaril.SSA.PEG.Simple.Tests

namespace Silmaril.SSA.PEG.Simple.Structured.Completion.Tests

open RVSDG (Tuple)
open Rules (readRef)

set_option backward.isDefEq.respectTransparency false

private inductive Op : InstructionSet Unit
  | positive : Op [.count] .bool
  | not : Op [.bool] .bool
  | pred : Op [.count] .count
  | probe : Op [.bool] .count

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .positive, .cons x .nil => some ⟨decide (0 < x.down)⟩
    | .not, .cons x .nil => some ⟨!x.down⟩
    | .pred, .cons x .nil => some ⟨x.down - 1⟩
    | .probe, .cons x .nil => if x.down then some ⟨0⟩ else none

private abbrev vars : List (Ty Unit) := [.count, .bool]

private def guard : Expr Op vars .bool := .op .positive (.cons (.var .head) .nil)

/-- The old counter feeds its update. The result of the strict probe is discarded. -/
private def tokenBody : Token.Body Op vars vars :=
  .seq (.assign (.op .probe (.cons (.var (.tail .head)) .nil)))
    (.seq (.assign (.op .pred (.cons (.var (.tail .head)) .nil)))
      (.project (.cons .head (.cons (.tail (.tail (.tail .head))) .nil))))

private def body : Stmt Op false vars vars := tokenBody.source

private def source := whileProgram guard body.enableWhile .head
private def graph : Graph Op vars [.count] 11 11 := translate source .not
private def input (count : Nat) (permit : Bool) : Tuple model.Value vars :=
  .cons ⟨count⟩ (.cons ⟨permit⟩ .nil)

private def key : Fin 11 := 2
private def base : Index 11 := fun _ => 0
private def sample (k : Nat) : Index 11 := base.set key k

private theorem setSample (a b : Nat) : (sample a).set key b = sample b := by
  funext j
  by_cases h : j = key <;> simp [sample, Index.set, h]

private def r (i : Fin 11) {t : Ty Unit} (typed : graph.sort i = t) : Ref graph.sort t :=
  ⟨i, typed⟩

private noncomputable def values (n : Nat) (permit : Bool) : graph.Valuation model :=
  graph.denote model (input n permit) (translate_demandWellFounded source .not)

private theorem solved (n : Nat) (permit : Bool) :
    graph.Solves model (input n permit) (values n permit) :=
  graph.denote_solves model (input n permit) _

-- Compute the live loop from the compiler's equations, independently of
-- source execution and for either value of the discarded probe's input.
private theorem countdown (n : Nat) (permit : Bool) (k : Nat) :
    readRef (values n permit) (r 7 (t := .count) rfl) (sample k) = some ⟨n - k⟩ := by
  have eq := solved n permit
  induction k with
  | zero =>
    rw [Rules.theta_zero eq (r := r 7 (t := .count) rfl) (initial := r 9 rfl) (feedback := r 4 rfl)
      (loop := key) HEq.rfl rfl]
    exact Rules.at_label eq (r := r 9 rfl) (label := .param .head) (args := .nil) HEq.rfl _
  | succ k ih =>
    rw [Rules.theta_succ eq (r := r 7 (t := .count) rfl) (initial := r 9 rfl) (feedback := r 4 rfl)
      (loop := key) HEq.rfl rfl,
      setSample, Rules.unary_at eq (r := r 4 rfl) (arg := r 7 rfl) (op := Op.pred) HEq.rfl, ih]
    change some (ULift.up (n - k - 1)) = some (ULift.up (n - (k + 1)))
    congr 2

private theorem exitFlag (n : Nat) (permit : Bool) (j : Nat) :
    readRef (values n permit) (r 3 rfl) (sample j) = some ⟨decide (n ≤ j)⟩ := by
  have eq := solved n permit
  rw [Rules.unary_at eq (r := r 3 rfl) (arg := r 6 rfl) (op := Op.not) HEq.rfl,
    Rules.unary_at eq (r := r 6 rfl) (arg := r 7 rfl) (op := Op.positive) HEq.rfl, countdown]
  change some (ULift.up (!decide (0 < n - j))) = some (ULift.up (decide (n ≤ j)))
  by_cases h : n ≤ j
  · simp [h, Nat.sub_eq_zero_of_le h]
  · have pos : 0 < n - j := by omega
    simp [h, pos]

private theorem firstPass (n : Nat) (permit : Bool) :
    readWhilePass guard body.enableWhile .head .not model (values n permit) base =
      some ⟨n⟩ := by
  change readRef (values n permit) (r 2 (t := .count) rfl) base = _
  rw [Rules.pass_at (solved n permit) (r := r 2 rfl) (cond := r 3 rfl) (loop := key) HEq.rfl]
  have stream : (fun j => (readRef (values n permit) (r 3 rfl) (sample j)).map ULift.down) =
      fun j => some (decide (n ≤ j)) := by
    funext j
    rw [exitFlag]
    rfl
  change (firstTrue (fun j => (readRef (values n permit) (r 3 rfl) (sample j)).map ULift.down)).map
    ULift.up = _
  have first : firstTrue (fun j => some (decide (n ≤ j))) = some n :=
    (firstTrue_eq_some_iff_samples _ n).mpr ⟨by simp, fun j lt => by simp [Nat.not_le_of_lt lt]⟩
  rw [stream, first]
  rfl

private theorem observed (n : Nat) (permit : Bool) :
    graph.observe model (values n permit) base = .cons (some ⟨0⟩) .nil := by
  have pass := firstPass n permit
  change readRef (values n permit) (r 2 (t := .count) rfl) base = _ at pass
  have evaluated := Rules.eval_at (solved n permit) (r := r 0 rfl) (source := r 7 rfl)
    (count := r 2 rfl) (loop := key) HEq.rfl base
  rw [pass] at evaluated
  change readRef (values n permit) (r 0 rfl) base =
    monotonize (fun j => readRef (values n permit) (r 7 rfl) (sample j)) n at evaluated
  have result := (monotonize_eq_some_iff
    (fun j => readRef (values n permit) (r 7 (t := .count) rfl) (sample j)) n (ULift.up 0)).mpr
    ⟨by rw [countdown, Nat.sub_self], fun j _ => by rw [countdown]; rfl⟩
  change Tuple.cons (F := fun t => Option (model.Value t)) (t := .count)
    (readRef (values n permit) (r 0 rfl) base) .nil = _
  rw [evaluated, result]

#guard checkWhilePrefix model guard body 2 (input 2 true)
#guard !checkWhilePrefix model guard body 2 (input 2 false)
#guard checkWhilePrefix model guard body 0 (input 0 false)

private theorem returnsFromPEG {n : Nat} {permit : Bool}
    (checked : checkWhilePrefix model guard body n (input n permit) = true) :
    source.Returns model (input n permit) ⟨0⟩ :=
  translate_while_returns_of_checkedPrefix guard body .head .not
    model (input n permit) (fun _ => rfl) base (firstPass n permit) checked (observed n permit)

example : source.Returns model (input 2 true) ⟨0⟩ := returnsFromPEG rfl
example : source.Returns model (input 0 false) ⟨0⟩ := returnsFromPEG rfl

private theorem fails : source.Fails model (input 2 false) :=
  .whileBodyFailed rfl (.firstFailed (.assignFailed rfl))

/-- A defined first pass and return survive the discarded probe's failure.
Figure 11's value observation alone cannot give a successful source run. -/
example : graph.observe model (values 2 false) base = .cons (some ⟨0⟩) .nil ∧
    readWhilePass guard body.enableWhile .head .not model (values 2 false) base = some ⟨2⟩ ∧
    ¬ source.Returns model (input 2 false) ⟨0⟩ := by
  refine ⟨observed 2 false, firstPass 2 false, ?_⟩
  rintro ⟨_, run, _⟩
  cases fails.deterministic run

private def tokenModel := Token.model model
private def tokenGraph : Graph (Token.Opcode Op) vars [.count, .bool] 16 16 :=
  Token.translate guard tokenBody .head .not

#guard (Structured.rank 16).check tokenGraph

private def tokenRef (i : Fin 16) {t : Ty Unit} (typed : tokenGraph.sort i = t) :
    Ref tokenGraph.sort t := ⟨i, typed⟩

private def tokenBase : Index 16 := fun _ => 0
private def tokenKey : Fin 16 := 3
private def tokenSample (k : Nat) : Index 16 := tokenBase.set tokenKey k

private noncomputable def tokenValues (n : Nat) (permit : Bool) : tokenGraph.Valuation tokenModel :=
  tokenGraph.denote tokenModel (input n permit)
    (Token.translate_demandWellFounded guard tokenBody .head .not)

private theorem tokenSolved (n : Nat) (permit : Bool) :
    tokenGraph.Solves tokenModel (input n permit) (tokenValues n permit) :=
  tokenGraph.denote_solves tokenModel (input n permit) _

-- Both ordered roots use the same pass, even on the failing input.
example : Rules.HasNode (tokenGraph.roots.get .head) (.eval tokenKey)
    (.cons (tokenRef 11 rfl) (.cons (tokenRef 3 rfl) .nil)) := HEq.rfl
example : Rules.HasNode (tokenGraph.roots.get (.tail .head)) (.eval tokenKey)
    (.cons (tokenRef 10 rfl) (.cons (tokenRef 3 rfl) .nil)) := HEq.rfl

private theorem tokenCounter (n : Nat) (permit : Bool) (k : Nat) :
    readRef (tokenValues n permit) (tokenRef 11 (t := .count) rfl) (tokenSample k) =
      some ⟨n - k⟩ := by
  have eq := tokenSolved n permit
  induction k with
  | zero =>
    rw [Rules.theta_zero eq (r := tokenRef 11 (t := .count) rfl) (initial := tokenRef 14 rfl)
      (feedback := tokenRef 6 rfl) (loop := tokenKey) HEq.rfl rfl]
    exact Rules.at_label eq (r := tokenRef 14 rfl) (label := .param .head) (args := .nil) HEq.rfl _
  | succ k ih =>
    have reset : (tokenSample (k + 1)).set tokenKey k = tokenSample k := by
      funext j
      by_cases h : j = tokenKey <;> simp [tokenSample, Index.set, h]
    rw [Rules.theta_succ eq (r := tokenRef 11 (t := .count) rfl) (initial := tokenRef 14 rfl)
      (feedback := tokenRef 6 rfl) (loop := tokenKey) HEq.rfl rfl,
      reset, Rules.unary_at eq (r := tokenRef 6 rfl) (arg := tokenRef 11 rfl)
        (op := .source Op.pred) HEq.rfl, ih]
    rfl

private theorem tokenPass (n : Nat) (permit : Bool) :
    readRef (tokenValues n permit) (tokenRef 3 (t := .count) rfl) tokenBase = some ⟨n⟩ := by
  have eq := tokenSolved n permit
  rw [Rules.pass_at eq (r := tokenRef 3 rfl) (cond := tokenRef 4 rfl) (loop := tokenKey) HEq.rfl]
  have stream : (fun j => (readRef (tokenValues n permit) (tokenRef 4 rfl) (tokenSample j)).map ULift.down) =
      fun j => some (decide (n ≤ j)) := by
    funext j
    rw [Rules.unary_at eq (r := tokenRef 4 rfl) (arg := tokenRef 9 rfl) (op := .source Op.not) HEq.rfl,
      Rules.unary_at eq (r := tokenRef 9 rfl) (arg := tokenRef 11 rfl)
        (op := .source Op.positive) HEq.rfl, tokenCounter]
    change some (!decide (0 < n - j)) = some (decide (n ≤ j))
    by_cases h : n ≤ j
    · simp [h, Nat.sub_eq_zero_of_le h]
    · have pos : 0 < n - j := by omega
      simp [h, pos]
  have first : firstTrue (fun j => some (decide (n ≤ j))) = some n :=
    (firstTrue_eq_some_iff_samples _ n).mpr ⟨by simp, fun j lt => by simp [Nat.not_le_of_lt lt]⟩
  change (firstTrue (fun j => (readRef (tokenValues n permit) (tokenRef 4 rfl) (tokenSample j)).map
    ULift.down)).map ULift.up = _
  rw [stream, first]
  rfl

private theorem tokenData (n : Nat) (permit : Bool) :
    (Token.observe guard tokenBody .head .not model (input n permit) tokenBase).get .head = some ⟨0⟩ := by
  change readRef (tokenValues n permit) (tokenRef 1 (t := .count) rfl) tokenBase = _
  rw [Rules.eval_at (tokenSolved n permit) (r := tokenRef 1 rfl) (source := tokenRef 11 rfl)
    (count := tokenRef 3 rfl) (loop := tokenKey) HEq.rfl, tokenPass]
  change monotonize (fun j => readRef (tokenValues n permit) (tokenRef 11 (t := .count) rfl)
    (tokenSample j)) n = _
  exact (monotonize_eq_some_iff _ _ _).mpr
    ⟨by rw [tokenCounter, Nat.sub_self], fun j _ => by rw [tokenCounter]; rfl⟩

private theorem twoTripSource : source.Returns model (input 2 true) ⟨0⟩ :=
  ⟨input 0 true, .whileStep (next := input 1 true) rfl (body.runLoopFree_enableWhile (input 2 true))
    (.whileStep (next := input 0 true) rfl (body.runLoopFree_enableWhile (input 1 true))
      (.whileStop rfl)), rfl⟩

example : Token.observe guard tokenBody .head .not model (input 2 true) tokenBase =
    .cons (some ⟨0⟩) (.cons (some ⟨true⟩) .nil) :=
  Token.observe_of_returns guard tokenBody .head .not model _ (fun _ => rfl) tokenBase twoTripSource

example : Token.observe guard tokenBody .head .not model (input 0 false) tokenBase =
    .cons (some ⟨0⟩) (.cons (some ⟨true⟩) .nil) :=
  Token.observe_of_returns guard tokenBody .head .not model _ (fun _ => rfl) tokenBase
    ⟨input 0 false, .whileStop rfl, rfl⟩

-- The ordinary pass and data are still defined at two and zero respectively.
-- The additional output detects precisely the execution failure.
example : readRef (tokenValues 2 false) (tokenRef 3 (t := .count) rfl) tokenBase = some ⟨2⟩ ∧
    Token.observe guard tokenBody .head .not model (input 2 false) tokenBase =
      .cons (some ⟨0⟩) (.cons none .nil) := by
  refine ⟨tokenPass 2 false, ?_⟩
  let observed := Token.observe guard tokenBody .head .not model (input 2 false) tokenBase
  have bot : observed.get (.tail .head) = none := by
    cases done : observed.get (.tail .head) with
    | none => rfl
    | some token =>
      have complete : (observed.get (.tail .head)).isSome := by rw [done]; rfl
      obtain ⟨_, ⟨_, run, _⟩, _⟩ := Token.returns_of_completion guard tokenBody
        .head .not model (input 2 false) (fun _ => rfl) tokenBase complete
      cases fails.deterministic run
  have value := tokenData 2 false
  change observed.get .head = some ⟨0⟩ at value
  change observed = _
  revert value bot
  cases observed with
  | cons root rest =>
    cases rest with
    | cons done rest =>
      cases rest
      intro bot value
      exact congrArg₂ (fun data token => Tuple.cons (F := fun t => Option (model.Value t))
        (t := .count) data (.cons token .nil)) value bot

section Conditional

-- Replaying the concrete dependent row types unfolds both arm layouts.
set_option maxHeartbeats 1000000

private abbrev branchVars : List (Ty Unit) := [.count, .bool, .bool]

private def branchGuard : Expr Op branchVars .bool := .op .positive (.cons (.var .head) .nil)

-- The arms have the same data outputs. Their discarded probes require
-- opposite values of the third input.
private def branchArm (yes : Bool) : Stmt Op false branchVars branchVars :=
  let permit : Expr Op branchVars .bool := .var (.tail (.tail .head))
  .seq (.assign (.op .probe (.cons (if yes then permit else .op .not (.cons permit .nil)) .nil)))
    (.project (.cons (.tail .head) (.cons (.tail (.tail .head)) (.cons (.tail (.tail (.tail .head))) .nil))))

private def branchStmt : Stmt Op false branchVars branchVars :=
  .seq (.branch (.var (.tail .head)) (branchArm true) (branchArm false))
    (.seq (.assign (.op .pred (.cons (.var .head) .nil)))
      (.project (.cons .head (.cons (.tail (.tail .head)) (.cons (.tail (.tail (.tail .head))) .nil)))))

private def branchSource := whileProgram branchGuard branchStmt.enableWhile .head
private def branchBody := Token.Body.ofStmt branchStmt
private def branchGraph : Graph (Token.Opcode Op) branchVars [.count, .bool] 26 26 :=
  Token.translate branchGuard branchBody .head .not

#guard (Structured.rank 26).check branchGraph

private def branchInput (n : Nat) (yes permit : Bool) : Tuple model.Value branchVars :=
  .cons ⟨n⟩ (.cons ⟨yes⟩ (.cons ⟨permit⟩ .nil))

private def br (i : Fin 26) {t : Ty Unit} (typed : branchGraph.sort i = t) : Ref branchGraph.sort t :=
  ⟨i, typed⟩

private def branchBase : Index 26 := fun _ => 0
private def branchKey : Fin 26 := 4
private def branchSample (k : Nat) : Index 26 := branchBase.set branchKey k

private noncomputable def branchValues (n : Nat) (side permit : Bool) : branchGraph.Valuation tokenModel :=
  branchGraph.denote tokenModel (branchInput n side permit)
    (Token.translate_demandWellFounded branchGuard branchBody .head .not)

private theorem branchSolved (n : Nat) (side permit : Bool) :
    branchGraph.Solves tokenModel (branchInput n side permit) (branchValues n side permit) :=
  branchGraph.denote_solves tokenModel (branchInput n side permit) _

example : Rules.HasNode (br 8 rfl) .phi
    (.cons (br 20 rfl) (.cons (br 15 rfl) (.cons (br 12 rfl) .nil))) := HEq.rfl

private theorem branchCountParam :
    Rules.HasNode (g := branchGraph) (br 23 (t := .count) rfl) (.param .head) .nil :=
  HEq.rfl

private theorem branchSideParam :
    Rules.HasNode (g := branchGraph) (br 24 (t := .bool) rfl) (.param (.tail .head)) .nil :=
  HEq.rfl

private theorem branchCountTheta : Rules.HasNode (g := branchGraph) (br 19 (t := .count) rfl) (.theta branchKey)
    (.cons (br 23 rfl) (.cons (br 7 rfl) .nil)) := HEq.rfl

private theorem branchSideTheta : Rules.HasNode (g := branchGraph) (br 20 (t := .bool) rfl) (.theta branchKey)
    (.cons (br 24 rfl) (.cons (br 10 rfl) .nil)) := HEq.rfl

private theorem branchCountPhi : Rules.HasNode (g := branchGraph) (br 9 (t := .count) rfl) .phi
    (.cons (br 20 rfl) (.cons (br 19 rfl) (.cons (br 19 rfl) .nil))) := HEq.rfl

private theorem branchSidePhi : Rules.HasNode (g := branchGraph) (br 10 (t := .bool) rfl) .phi
    (.cons (br 20 rfl) (.cons (br 20 rfl) (.cons (br 20 rfl) .nil))) := HEq.rfl

private theorem branchPred : Rules.HasNode (g := branchGraph) (br 7 (t := .count) rfl) (.op (.source Op.pred))
    (.cons (br 9 rfl) .nil) := HEq.rfl

private theorem branchSamples (n : Nat) (side permit : Bool) (k : Nat) :
    readRef (branchValues n side permit) (br 19 (t := .count) rfl) (branchSample k) = some ⟨n - k⟩ ∧
    readRef (branchValues n side permit) (br 20 (t := .bool) rfl) (branchSample k) = some ⟨side⟩ := by
  have eq := branchSolved n side permit
  induction k with
  | zero =>
    constructor
    · exact (Rules.theta_zero eq branchCountTheta rfl).trans
        (Rules.at_label eq branchCountParam (branchSample 0))
    · exact (Rules.theta_zero eq branchSideTheta rfl).trans
        (Rules.at_label eq branchSideParam (branchSample 0))
  | succ k ih =>
    have reset : (branchSample (k + 1)).set branchKey k = branchSample k := by
      funext j
      by_cases h : j = branchKey <;> simp [branchSample, Index.set, h]
    constructor
    · rw [Rules.theta_succ eq branchCountTheta rfl, reset,
        Rules.unary_at eq branchPred, Rules.phi_at eq branchCountPhi, ih.2]
      rw [Option.elim_some, ite_self, ih.1]
      rfl
    · rw [Rules.theta_succ eq branchSideTheta rfl, reset, Rules.phi_at eq branchSidePhi,
        ih.2, Option.elim_some, ite_self]

private theorem branchPass (n : Nat) (side permit : Bool) :
    readRef (branchValues n side permit) (br 4 (t := .count) rfl) branchBase = some ⟨n⟩ := by
  have eq := branchSolved n side permit
  rw [Rules.pass_at eq (r := br 4 rfl) (cond := br 5 rfl) (loop := branchKey) HEq.rfl]
  have stream : (fun j => (readRef (branchValues n side permit) (br 5 rfl) (branchSample j)).map
      ULift.down) = fun j => some (decide (n ≤ j)) := by
    funext j
    rw [Rules.unary_at eq (r := br 5 rfl) (arg := br 17 rfl) (op := .source Op.not) HEq.rfl,
      Rules.unary_at eq (r := br 17 rfl) (arg := br 19 rfl) (op := .source Op.positive) HEq.rfl,
      (branchSamples n side permit j).1]
    change some (!decide (0 < n - j)) = some (decide (n ≤ j))
    by_cases h : n ≤ j
    · simp [h, Nat.sub_eq_zero_of_le h]
    · have pos : 0 < n - j := by omega
      simp [h, pos]
  have first : firstTrue (fun j => some (decide (n ≤ j))) = some n :=
    (firstTrue_eq_some_iff_samples _ n).mpr ⟨by simp, fun j lt => by simp [Nat.not_le_of_lt lt]⟩
  change (firstTrue (fun j => (readRef (branchValues n side permit) (br 5 rfl) (branchSample j)).map
    ULift.down)).map ULift.up = _
  rw [stream, first]
  rfl

private noncomputable def branchObserve (n : Nat) (side permit : Bool) :=
  Token.observe branchGuard branchBody .head .not model (branchInput n side permit) branchBase

private theorem branchData (n : Nat) (side permit : Bool) :
    (branchObserve n side permit).get .head = some ⟨0⟩ := by
  change readRef (branchValues n side permit) (br 1 (t := .count) rfl) branchBase = _
  rw [Rules.eval_at (branchSolved n side permit) (r := br 1 rfl) (source := br 19 rfl)
    (count := br 4 rfl) (loop := branchKey) HEq.rfl, branchPass]
  change monotonize (fun j => readRef (branchValues n side permit) (br 19 (t := .count) rfl)
    (branchSample j)) n = _
  exact (monotonize_eq_some_iff _ _ _).mpr
    ⟨by rw [(branchSamples n side permit n).1, Nat.sub_self], fun j _ => by
      rw [(branchSamples n side permit j).1]; rfl⟩

private theorem permitAtStart (side permit : Bool) :
    readRef (branchValues 2 side permit) (br 21 (t := .bool) rfl) (branchSample 0) = some ⟨permit⟩ := by
  have eq := branchSolved 2 side permit
  rw [Rules.theta_zero eq (r := br 21 rfl) (initial := br 25 rfl)
    (feedback := br 11 rfl) (loop := branchKey) HEq.rfl rfl]
  exact Rules.at_label eq (r := br 25 rfl) (label := .param (.tail (.tail .head))) (args := .nil) HEq.rfl _

-- Actual PEG equations witness the bottom probe in each untaken arm.
example : readRef (branchValues 2 true true) (br 13 (t := .count) rfl) (branchSample 0) = none := by
  have eq := branchSolved 2 true true
  rw [Rules.unary_at eq (r := br 13 rfl) (arg := br 14 rfl) (op := .source Op.probe) HEq.rfl,
    Rules.unary_at eq (r := br 14 rfl) (arg := br 21 rfl) (op := .source Op.not) HEq.rfl, permitAtStart]
  rfl

example : readRef (branchValues 2 false false) (br 16 (t := .count) rfl) (branchSample 0) = none := by
  rw [Rules.unary_at (branchSolved 2 false false) (r := br 16 rfl) (arg := br 21 rfl)
    (op := .source Op.probe) HEq.rfl, permitAtStart]
  rfl

private theorem branchReturns (side : Bool) :
    branchSource.Returns model (branchInput 2 side side) ⟨0⟩ := by
  cases side <;>
    exact ⟨_, .whileStep (next := branchInput 1 _ _) rfl
      (branchStmt.runLoopFree_enableWhile (branchInput 2 _ _))
      (.whileStep (next := branchInput 0 _ _) rfl
        (branchStmt.runLoopFree_enableWhile (branchInput 1 _ _)) (.whileStop rfl)), rfl⟩

example (side : Bool) : branchObserve 2 side side = .cons (some ⟨0⟩) (.cons (some ⟨true⟩) .nil) :=
  Token.observe_of_returns branchGuard branchBody .head .not model _ (fun _ => rfl) branchBase
    (branchReturns side)

private theorem branchFails (side : Bool) : branchSource.Fails model (branchInput 2 side (!side)) := by
  cases side <;> exact .whileBodyFailed rfl (branchStmt.runLoopFree_enableWhile (branchInput 2 _ _))

example (side : Bool) : (branchObserve 2 side (!side)).get .head = some ⟨0⟩ ∧
    (branchObserve 2 side (!side)).get (.tail .head) = none := by
  refine ⟨branchData 2 side (!side), ?_⟩
  cases done : (branchObserve 2 side (!side)).get (.tail .head) with
  | none => rfl
  | some token =>
    have defined : ((branchObserve 2 side (!side)).get (.tail .head)).isSome := by rw [done]; rfl
    obtain ⟨value, ⟨_, run, _⟩, _⟩ := Token.returns_of_completion branchGuard branchBody .head .not
      model _ (fun _ => rfl) branchBase defined
    cases (branchFails side).deterministic run

example (side : Bool) : branchObserve 0 side (!side) = .cons (some ⟨0⟩) (.cons (some ⟨true⟩) .nil) :=
  Token.observe_of_returns branchGuard branchBody .head .not model _ (fun _ => rfl) branchBase
    ⟨branchInput 0 side (!side), .whileStop rfl, rfl⟩

end Conditional

end Silmaril.SSA.PEG.Simple.Structured.Completion.Tests

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Tests

open RVSDG (Tuple)
open Rules (readRef)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private inductive Op : InstructionSet Unit
  | not : Op [.bool] .bool
  | off : Op [] .bool
  | bad : Op [] .count

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .not, .cons b .nil => some ⟨!b.down⟩
    | .off, .nil => some ⟨false⟩
    | .bad, .nil => none

private def fixture : Form Op [.bool, .bool] [.bool] .bool where
  guard := .var .head
  capture := .cons (.tail .head) .nil
  childGuard := .var .head
  childBody := .seq (.assign (.op .bad .nil))
    (.seq (.assign (.op .off .nil)) (.project (.cons .head .nil)))
  commit := .seq (.assign (.op .off .nil)) (.project (.cons .head (.cons .head .nil)))
  result := .head

private def input (enter : Bool) : Tuple model.Value [.bool, .bool] := .cons ⟨enter⟩ (.cons ⟨true⟩ .nil)
private def graph : Graph (Opcode Op) [.bool, .bool] [.bool, .bool] 23 23 := fixture.translate .not
private def base : Index 23 := fun _ => 0

#guard (Structured.rank 23).check graph
#guard graph.forest.parent (fixture.childPass .not).id == some (fixture.outerPass .not).id

private def r (i : Fin 23) {t : Ty Unit} (typed : graph.sort i = t) : Ref graph.sort t := ⟨i, typed⟩
private abbrev tokenModel := Token.model model
private noncomputable def values : graph.Valuation tokenModel := fixture.values .not model (input true)

private theorem solved : graph.Solves tokenModel (input true) values :=
  graph.denote_solves tokenModel (input true) (fixture.translate_demandWellFounded .not)

private theorem outerLatch (k : Nat) :
    readRef values (r 18 (t := .bool) rfl) (base.set 3 k) = some ⟨decide (k = 0)⟩ := by
  have theta : Rules.HasNode (g := graph) (r 18 (t := .bool) rfl) (.theta 3)
      (.cons (r 21 rfl) (.cons (r 6 rfl) .nil)) := HEq.rfl
  cases k with
  | zero =>
    have param : Rules.HasNode (g := graph) (r 21 (t := .bool) rfl) (.param .head) .nil := HEq.rfl
    exact (Rules.theta_zero solved theta rfl).trans (Rules.at_label solved param _)
  | succ k =>
    have off : Rules.HasNode (g := graph) (r 6 (t := .bool) rfl) (.op (.source Op.off)) .nil := HEq.rfl
    exact (Rules.theta_succ solved theta rfl).trans (Rules.at_label solved off _)

private theorem onePass {p : Ref graph.sort .count} {flag latch : Ref graph.sort .bool}
    {key : Fin 23}
    (pass : Rules.HasNode (g := graph) p (.pass key) (.cons flag .nil))
    (neg : Rules.HasNode (g := graph) flag (.op (.source Op.not)) (.cons latch .nil))
    (latchAt : ∀ j, readRef values latch (base.set key j) = some ⟨decide (j = 0)⟩) :
    readRef values p base = some ⟨1⟩ := by
  rw [Rules.pass_at solved pass]
  have stream : (fun j => (readRef values flag (base.set key j)).map ULift.down) =
      fun j => some (!decide (j = 0)) := by
    funext j
    rw [Rules.unary_at solved neg, latchAt]
    rfl
  rw [stream]
  have first : firstTrue (fun j => some (!decide (j = 0))) = some 1 :=
    (firstTrue_eq_some_iff_samples _ 1).mpr ⟨rfl, fun j lt => by
      have zero : j = 0 := by omega
      subst j
      rfl⟩
  rw [first]
  rfl

private theorem outerPass :
    readRef values (r 3 (t := .count) rfl) base = some ⟨1⟩ :=
  onePass (p := r 3 rfl) (flag := r 4 rfl) (latch := r 18 rfl) (key := 3) HEq.rfl HEq.rfl outerLatch

private theorem childLatch (k : Nat) :
    readRef values (r 16 (t := .bool) rfl) (base.set 9 k) = some ⟨decide (k = 0)⟩ := by
  have theta : Rules.HasNode (g := graph) (r 16 (t := .bool) rfl) (.theta 9)
      (.cons (r 19 rfl) (.cons (r 12 rfl) .nil)) := HEq.rfl
  cases k with
  | zero =>
    have capture : Rules.HasNode (g := graph) (r 19 (t := .bool) rfl) (.theta 3)
      (.cons (r 22 rfl) (.cons (r 6 rfl) .nil)) := HEq.rfl
    have param : Rules.HasNode (g := graph) (r 22 (t := .bool) rfl) (.param (.tail .head)) .nil := HEq.rfl
    exact (Rules.theta_zero solved theta rfl).trans
      ((Rules.theta_zero solved capture rfl).trans (Rules.at_label solved param _))
  | succ k =>
    have off : Rules.HasNode (g := graph) (r 12 (t := .bool) rfl) (.op (.source Op.off)) .nil := HEq.rfl
    exact (Rules.theta_succ solved theta rfl).trans (Rules.at_label solved off _)

-- The child pass remains defined at this invocation. Its completion
-- marker is a separate observation from that finite pass count.
example : readRef values (fixture.childPass .not) base = some ⟨1⟩ :=
  onePass (p := r 9 rfl) (flag := r 10 rfl) (latch := r 16 rfl) (key := 9) HEq.rfl HEq.rfl childLatch

private theorem dataDefined : (fixture.observe .not model (input true) base).get .head = some ⟨false⟩ := by
  change readRef values (r 1 (t := .bool) rfl) base = _
  have eval : Rules.HasNode (g := graph) (r 1 (t := .bool) rfl) (.eval 3)
    (.cons (r 18 rfl) (.cons (r 3 rfl) .nil)) := HEq.rfl
  rw [Rules.eval_at solved eval, outerPass]
  change monotonize (fun k => readRef values (r 18 (t := .bool) rfl) (base.set 3 k)) 1 = some ⟨false⟩
  exact (monotonize_eq_some_iff _ _ _).mpr
    ⟨outerLatch 1, fun k _ => by rw [outerLatch]; rfl⟩

private theorem stepFails (enter : Bool) : Exec model fixture.step (input enter) none :=
  .seq .project (.firstFailed (.whileBodyFailed rfl (.firstFailed (.assignFailed rfl))))

-- One outer trip calls the child. Its discarded failure leaves data
-- defined but prevents the completion token from reaching the root.
example : (fixture.observe .not model (input true) base).get .head = some ⟨false⟩ ∧
    (fixture.observe .not model (input true) base).get (.tail .head) = none := by
  refine ⟨dataDefined, ?_⟩
  have failed : fixture.source.Fails model (input true) := .whileBodyFailed rfl (stepFails true)
  cases eq : (fixture.observe .not model (input true) base).get (.tail .head) with
  | none => rfl
  | some token =>
    have complete : ((fixture.observe .not model (input true) base).get (.tail .head)).isSome := by
      rw [eq]
      rfl
    obtain ⟨_, ⟨_, run, _⟩, _⟩ := fixture.returns_of_completion .not model _ (fun _ => rfl) base complete
    cases failed.deterministic run

-- The same child input would fail if the body were entered.
example : fixture.observe .not model (input false) base = .cons (some ⟨false⟩) (.cons (some ⟨true⟩) .nil) :=
  fixture.observe_of_returns .not model _ (fun _ => rfl) base ⟨input false, .whileStop rfl, rfl⟩

private def finish : Body Op [.bool, .bool] [.bool, .bool] :=
  .seq (.assign (.op .off .nil)) (.project (.cons .head (.cons .head .nil)))

private def choiceFixture : Conditional.Form Op [.bool, .bool] [.bool] .bool where
  parent := { fixture with capture := .cons .head .nil }
  selectChild := .var (.tail .head)
  skip := finish

private def choiceInput (take : Bool) : Tuple model.Value [.bool, .bool] :=
  .cons ⟨true⟩ (.cons ⟨take⟩ .nil)

private def stopStore : Tuple model.Value [.bool, .bool] :=
  .cons ⟨false⟩ (.cons ⟨false⟩ .nil)

private def choiceGraph : Graph (Opcode Op) [.bool, .bool] [.bool, .bool] 28 28 :=
  choiceFixture.translate .not
private def choiceBase : Index 28 := fun _ => 0

private def cr (i : Fin 28) {t : Ty Unit} (typed : choiceGraph.sort i = t) : Ref choiceGraph.sort t :=
  ⟨i, typed⟩

private noncomputable def choiceValues (take : Bool) : choiceGraph.Valuation tokenModel :=
  choiceFixture.values .not model (choiceInput take)

private theorem choiceSolved (take : Bool) : choiceGraph.Solves tokenModel (choiceInput take) (choiceValues take) :=
  choiceGraph.denote_solves tokenModel (choiceInput take) (choiceFixture.translate_demandWellFounded .not)

-- The child contains an actually bottom strict operation even on the
-- input whose branch skips the entire activation.
example : readRef (choiceValues false) (cr 19 (t := .count) rfl) choiceBase = none :=
  Rules.at_label (choiceSolved false) (r := cr 19 rfl) (label := .op (.source Op.bad)) (args := .nil)
    HEq.rfl choiceBase

example : choiceFixture.observe .not model (choiceInput false) choiceBase =
    .cons (some ⟨false⟩) (.cons (some ⟨true⟩) .nil) :=
  choiceFixture.observe_of_returns .not model _ (fun _ => rfl) choiceBase
    ⟨stopStore, .whileStep rfl (.branchFalse rfl (finish.source.runLoopFree_enableWhile (choiceInput false)))
      (.whileStop rfl), rfl⟩

private theorem choiceTheta : Rules.HasNode (g := choiceGraph) (cr 23 (t := .bool) rfl) (.theta 3)
    (.cons (cr 26 rfl) (.cons (cr 6 rfl) .nil)) := HEq.rfl

private theorem choiceLatchZero :
    readRef (choiceValues true) (cr 23 (t := .bool) rfl) (choiceBase.set 3 0) = some ⟨true⟩ := by
  have param : Rules.HasNode (g := choiceGraph) (cr 26 (t := .bool) rfl) (.param .head) .nil := HEq.rfl
  exact (Rules.theta_zero (choiceSolved true) choiceTheta rfl).trans
    (Rules.at_label (choiceSolved true) param _)

private theorem choiceLatchOne :
    readRef (choiceValues true) (cr 23 (t := .bool) rfl) (choiceBase.set 3 1) = some ⟨false⟩ := by
  have eq := choiceSolved true
  have selected : Rules.HasNode (g := choiceGraph) (cr 24 (t := .bool) rfl) (.theta 3)
    (.cons (cr 27 rfl) (.cons (cr 7 rfl) .nil)) := HEq.rfl
  have param : Rules.HasNode (g := choiceGraph) (cr 27 (t := .bool) rfl) (.param (.tail .head)) .nil := HEq.rfl
  have flag : readRef (choiceValues true) (cr 24 (t := .bool) rfl) (choiceBase.set 3 0) = some ⟨true⟩ :=
    (Rules.theta_zero eq selected rfl).trans (Rules.at_label eq param _)
  have join : Rules.HasNode (g := choiceGraph) (cr 6 (t := .bool) rfl) .phi
    (.cons (cr 24 rfl) (.cons (cr 11 rfl) (.cons (cr 9 rfl) .nil))) := HEq.rfl
  have off : Rules.HasNode (g := choiceGraph) (cr 11 (t := .bool) rfl) (.op (.source Op.off)) .nil := HEq.rfl
  have reset : (choiceBase.set 3 1).set 3 0 = choiceBase.set 3 0 := by
    funext j
    by_cases h : j = 3 <;> simp [Index.set, h]
  rw [Rules.theta_succ eq choiceTheta rfl, reset, Rules.phi_at eq join, flag]
  exact Rules.at_label eq off _

private theorem choicePass :
    readRef (choiceValues true) (cr 3 (t := .count) rfl) choiceBase = some ⟨1⟩ := by
  have eq := choiceSolved true
  have pass : Rules.HasNode (g := choiceGraph) (cr 3 (t := .count) rfl) (.pass 3)
    (.cons (cr 4 rfl) .nil) := HEq.rfl
  have neg : Rules.HasNode (g := choiceGraph) (cr 4 (t := .bool) rfl) (.op (.source Op.not))
    (.cons (cr 23 rfl) .nil) := HEq.rfl
  rw [Rules.pass_at eq pass]
  let flags := fun j => (readRef (choiceValues true) (cr 4 (t := .bool) rfl) (choiceBase.set 3 j)).map ULift.down
  have first : firstTrue flags = some 1 := (firstTrue_eq_some_iff_samples _ _).mpr
    ⟨by
      unfold flags
      rw [Rules.unary_at eq neg, choiceLatchOne]
      rfl,
    fun j lt => by
      have zero : j = 0 := by omega
      subst j
      unfold flags
      rw [Rules.unary_at eq neg, choiceLatchZero]
      rfl⟩
  change (firstTrue flags).map ULift.up = _
  rw [first]
  rfl

private theorem choiceData : (choiceFixture.observe .not model (choiceInput true) choiceBase).get .head =
    some ⟨false⟩ := by
  change readRef (choiceValues true) (cr 1 (t := .bool) rfl) choiceBase = _
  have eval : Rules.HasNode (g := choiceGraph) (cr 1 (t := .bool) rfl) (.eval 3)
    (.cons (cr 23 rfl) (.cons (cr 3 rfl) .nil)) := HEq.rfl
  rw [Rules.eval_at (choiceSolved true) eval, choicePass]
  change monotonize (fun j => readRef (choiceValues true) (cr 23 (t := .bool) rfl)
    (choiceBase.set 3 j)) 1 = _
  exact (monotonize_eq_some_iff _ _ _).mpr ⟨choiceLatchOne, fun j lt => by
    have zero : j = 0 := by omega
    subst j
    rw [choiceLatchZero]
    rfl⟩

example : (choiceFixture.observe .not model (choiceInput true) choiceBase).get .head = some ⟨false⟩ ∧
    (choiceFixture.observe .not model (choiceInput true) choiceBase).get (.tail .head) = none := by
  refine ⟨choiceData, ?_⟩
  have failed : choiceFixture.source.Fails model (choiceInput true) :=
    .whileBodyFailed rfl (.branchTrue rfl
      (.seq .project (.firstFailed (.whileBodyFailed rfl (.firstFailed (.assignFailed rfl))))))
  cases observed : (choiceFixture.observe .not model (choiceInput true) choiceBase).get (.tail .head) with
  | none => rfl
  | some token =>
    have done : ((choiceFixture.observe .not model (choiceInput true) choiceBase).get (.tail .head)).isSome := by
      rw [observed]
      rfl
    obtain ⟨_, ⟨_, ran, _⟩, _⟩ := choiceFixture.returns_of_completion .not model _ (fun _ => rfl) choiceBase done
    cases failed.deterministic ran

end Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Tests
