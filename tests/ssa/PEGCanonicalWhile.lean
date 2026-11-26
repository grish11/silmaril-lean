module

import Silmaril.SSA.PEG.Simple.Revert.While.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected.Thms
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Basic
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Thms
import Silmaril.SSA.PEG.Simple.Thms
meta import Silmaril.SSA.PEG.Simple.Revert.While.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs

namespace Silmaril.SSA.PEG.Simple.Revert.While.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | nonzero : Op [.count] .bool
  | pred : Op [.count] .count
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .nonzero, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private def form : Form Op .count := ⟨.nonzero, .pred, .not⟩

private def store (n : Nat) : Tuple model.Value [.count] := .cons ⟨n⟩ .nil

private theorem countDown (n : Nat) :
    Exec model form.program.source.body (store n) (some (store 0)) := by
  induction n with
  | zero => exact .whileStop rfl
  | succ n ih =>
    let assigned := Tuple.cons (F := model.Value) (t := Ty.count) ⟨n⟩ (store (n + 1))
    exact .whileStep (next := store n) rfl (.seq (next := assigned) (.assign rfl) .project) ih

private theorem accepted : ∃ cert, extract form.compile = some cert ∧ cert.form = form :=
  form.compile_extract

-- The extracted SIMPLE loop returns at zero iterations and at arbitrary finite exits.
example (n : Nat) : ∃ cert, extract form.compile = some cert ∧
    cert.revert.Returns model (store n) ⟨0⟩ := by
  obtain ⟨cert, checked, recovered⟩ := accepted
  refine ⟨cert, checked, store 0, ?_, ?_⟩
  · change Exec model cert.form.program.source.body (store n) (some (store 0))
    rw [recovered]
    exact countDown n
  · change (store 0).get cert.form.program.retvar = _
    rw [recovered]
    rfl

example (n : Nat) : ∃ cert, extract form.compile = some cert ∧
    form.compile.observe model (form.compile.denote model (store n) cert.demandWellFounded)
      (fun _ => 19) = .cons (some ⟨0⟩) .nil := by
  obtain ⟨cert, checked, recovered⟩ := accepted
  refine ⟨cert, checked, cert.observe_of_returns model (store n) ?_ ?_ _⟩
  · rw [recovered]
    intro b
    rfl
  · change cert.form.program.source.Returns model (store n) ⟨0⟩
    rw [recovered]
    exact ⟨store 0, countDown n, rfl⟩

-- Pass reads the continuation test directly, bypassing negation. Wiring is
-- still well sorted, but this is a different loop exit.
private def wrongExitRaw : RawGraph Op [.count] [.count] 7 1 :=
  { form.compile.toRaw with node := fun i =>
    let row := form.compile.toRaw.node i
    if i = 1 then { row with args := [4] } else row }

private def wrongExit : Graph Op [.count] [.count] 7 1 := wrongExitRaw.check.get (by decide)

example : extract wrongExit = none := by
  cases h : extract wrongExit with
  | none => rfl
  | some cert =>
    have mismatch := congrArg (fun g : RawGraph Op [.count] [.count] 7 1 =>
      (g.node 1).args) cert.table
    change [4] = [2] at mismatch
    contradiction

set_option interpreter.prefer_native false

/-- info: true -/
#guard_msgs in
#eval (extract form.compile).isSome

/-- info: true -/
#guard_msgs in
#eval (extract wrongExit).isNone

end Silmaril.SSA.PEG.Simple.Revert.While.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Pair.Tests

open RVSDG (Tuple)

private abbrev acc : Ty Unit := .data ()

private inductive Op : InstructionSet Unit where
  | positive : Op [.count] .bool
  | pred : Op [.count] .count
  | addOld : Op [.count, acc] acc
  | bad : Op [.count, acc] acc
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Nat
  run
    | .positive, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .addOld, .cons n (.cons a .nil) => some ((show Nat from a) + n.down)
    | .bad, _ => none
    | .not, .cons flag .nil => some ⟨!flag.down⟩

private def input (n a : Nat) : Tuple model.Value [.count, acc] := .cons ⟨n⟩ (.cons a .nil)

private def sum : Form Op .count acc acc := ⟨.positive, .pred, .addOld, .not, .tail .head⟩

private theorem sumTotal : sum.Total model where
  guard x := ⟨x.down != 0, rfl⟩
  leftStep x := ⟨⟨x.down - 1⟩, rfl⟩
  rightStep store := by
    cases store with | cons n tail =>
    cases tail with | cons a tail =>
    cases tail
    exact ⟨(show Nat from a) + n.down, rfl⟩

private def runExtracted (fuel n a : Nat) : Option Nat := do
  let cert ← extract sum.compile
  cert.form.runFuel model fuel (input n a)

set_option interpreter.prefer_native false

-- The additions see 3, 2 and 1, even though the counter is assigned first.
/-- info: some 16 -/
#guard_msgs in
#eval runExtracted 3 3 10

/-- info: some 10 -/
#guard_msgs in
#eval runExtracted 0 0 10

/-- info: none -/
#guard_msgs in
#eval runExtracted 2 3 10

private theorem sumPeg :
    sum.compile.observe model
      (sum.compile.denote model (input 3 10) (sum.program.translate_demandWellFounded sum.negate))
      (fun _ => 17) = .cons (some (16 : Nat)) .nil :=
  sum.program.translate_returns sum.negate model (input 3 10) (fun _ => rfl)
    (sum.runFuel_returns model 3 (input 3 10) (value := (16 : Nat)) rfl) (fun _ => 17)

private def sumCertificate : Certificate sum.compile := ⟨sum, rfl⟩

example : sumCertificate.revert.Returns model (input 3 10) (16 : Nat) :=
  sumCertificate.returns_of_defined model (input 3 10) sumTotal (fun _ => rfl) _ sumPeg

example : ∃ k, sumCertificate.form.runFuel model k (input 3 10) = some (16 : Nat) := by
  obtain ⟨k, returned, _⟩ :=
    sumCertificate.runFuel_of_defined model (input 3 10) sumTotal (fun _ => rfl) _ sumPeg
  exact ⟨k, returned⟩

-- The right update reads the newly computed left value. This wire is well
-- typed but changes a simultaneous update into a sequential dependency.
private def sequentialRaw : RawGraph Op [.count, acc] [acc] 10 1 :=
  { sum.compile.toRaw with node := fun i =>
    let row := sum.compile.toRaw.node i
    if i = 3 then { row with args := [4, 7] } else row }

private def sequential : Graph Op [.count, acc] [acc] 10 1 :=
  sequentialRaw.check.get (by decide)

/-- info: true -/
#guard_msgs in
#eval (extract sequential).isNone

/-- Left is the only observed slot. The partial right update is still
executed by SIMPLE on a continuing iteration. -/
private def discarded : Form Op .count acc .count := ⟨.positive, .pred, .bad, .not, .head⟩

private theorem notTotal : ¬ discarded.Total model := by
  intro total
  obtain ⟨x, impossible⟩ := total.rightStep (input 1 10)
  cases impossible

private def runDiscarded : Option Nat := do
  let cert ← extract discarded.compile
  (cert.form.runFuel model 1 (input 1 10)).map ULift.down

/-- info: (true, none) -/
#guard_msgs in
#eval ((extract discarded.compile).isSome, runDiscarded)

private def tick (n : Nat) : Index 1 := fun _ => n

private theorem setTick (idx : Index 1) (n : Nat) : idx.set 0 n = tick n := by
  funext i
  have h : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Index.set, tick]

private theorem collectOne {t : Ty Unit}
    (sample : (i : Fin [t].length) → Option (model.Value [t][i])) :
    collect [t] sample = (sample 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases sample 0 <;> rfl

-- Only the left carried stream, unary guard and exit test are demanded.
-- The PEG can return despite the failed right update in the SIMPLE body.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem discardedPeg :
    discarded.compile.observe model
      (discarded.compile.denote model (input 1 10)
        (discarded.program.translate_demandWellFounded discarded.negate)) (tick 0) =
      .cons (some ⟨0⟩) .nil := by
  let wf := discarded.program.translate_demandWellFounded discarded.negate
  let values := discarded.compile.denote model (input 1 10) wf
  have eq (v : Fin 10) (idx : Index 1) :
      values (v, idx) = discarded.compile.equation model (input 1 10) values (v, idx) :=
    discarded.compile.denote_solves model (input 1 10) wf (v, idx)
  have initial : values (6, tick 0) = some ⟨1⟩ := by
    rw [eq 6 (tick 0)]
    change values (8, tick 0) = _
    exact eq 8 (tick 0)
  have update : values (4, tick 0) = some ⟨0⟩ := by
    rw [eq 4 (tick 0)]
    change (collect [.count] _).elim none (model.run Op.pred) = _
    rw [collectOne]
    change ((values (6, tick 0)).map (fun x => Tuple.cons x .nil)).elim none (model.run Op.pred) = _
    rw [initial]
    rfl
  have next : values (6, tick 1) = some ⟨0⟩ := by
    rw [eq 6 (tick 1)]
    change values (4, (tick 1).set 0 0) = _
    rw [setTick, update]
  have exit (idx : Index 1) (n : Nat) (value : values (6, idx) = some ⟨n⟩) :
      values (2, idx) = some ⟨!(n != 0)⟩ := by
    have guard : values (5, idx) = some ⟨n != 0⟩ := by
      rw [eq 5 idx]
      change (collect [.count] _).elim none (model.run Op.positive) = _
      rw [collectOne]
      change ((values (6, idx)).map (fun x => Tuple.cons x .nil)).elim none
        (model.run Op.positive) = _
      rw [value]
      rfl
    rw [eq 2 idx]
    change (collect [.bool] _).elim none (model.run Op.not) = _
    rw [collectOne]
    change ((values (5, idx)).map (fun x => Tuple.cons x .nil)).elim none (model.run Op.not) = _
    rw [guard]
    rfl
  let flags := fun k => (values (2, tick k)).map ULift.down
  have stop : flags 1 = some true := by
    unfold flags
    rw [exit (tick 1) 0 next]
    rfl
  have again : flags 0 = some false := by
    unfold flags
    rw [exit (tick 0) 1 initial]
    rfl
  have first : firstTrue flags = some 1 := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨stop, ?_⟩, ?_⟩
    · intro j h
      have zj : j = 0 := by omega
      rw [zj, again]
      rfl
    · intro j h hit
      have zj : j = 0 := by omega
      have trueSample := ((monotonize_eq_some_iff _ _ _).mp hit).1
      rw [zj, again] at trueSample
      cases trueSample
  have pass : values (1, tick 0) = some ⟨1⟩ := by
    rw [eq 1 (tick 0)]
    change (firstTrue (fun k => (values (2, (tick 0).set 0 k)).map ULift.down)).map ULift.up = _
    have aligned : (fun k => (values (2, (tick 0).set 0 k)).map ULift.down) = flags := by
      funext k
      exact congrArg (fun idx => (values (2, idx)).map ULift.down) (setTick (tick 0) k)
    rw [aligned, first]
    rfl
  change Tuple.cons (F := fun t => Option (model.Value t)) (values (0, tick 0)) .nil = _
  congr 1
  rw [eq 0 (tick 0)]
  change (values (1, tick 0)).elim none (fun count =>
    monotonize (fun j => values (6, (tick 0).set 0 j)) count.down) = _
  rw [pass]
  change monotonize (fun j => values (6, (tick 0).set 0 j)) 1 = _
  have aligned : (fun j => values (6, (tick 0).set 0 j)) = (fun j => values (6, tick j)) := by
    funext j
    exact congrArg (fun idx => (show Option (model.Value .count) from values (6, idx)))
      (setTick (tick 0) j)
  rw [aligned]
  apply (monotonize_eq_some_iff _ _ _).mpr
  refine ⟨next, fun j lt => ?_⟩
  have zj : j = 0 := by omega
  rw [zj, initial]
  rfl

private theorem discardedFails : discarded.program.source.Fails model (input 1 10) := by
  let updated : Tuple model.Value [.count, .count, acc] := .cons ⟨0⟩ (input 1 10)
  exact .whileBodyFailed rfl (.seq (next := updated) (.assign rfl) (.firstFailed (.assignFailed rfl)))

example : ¬ discarded.program.source.Returns model (input 1 10) ⟨0⟩ := by
  intro success
  obtain ⟨_, ran, _⟩ := success
  cases Exec.deterministic ran discardedFails

end Silmaril.SSA.PEG.Simple.Revert.While.Pair.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Tests

open RVSDG (Tuple)

private abbrev acc : Ty Unit := .data ()
private abbrev carried : List (Ty Unit) := [.count, acc, acc]

private inductive Op : InstructionSet Unit where
  | twice : Op [.count] .count
  | nonzero : Op [.count] .bool
  | pred : Op [.count] .count
  | sum : Op [acc, acc] acc
  | addCount : Op [.count, acc] acc
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Nat
  run
    | .twice, .cons n .nil => some ⟨2 * n.down⟩
    | .nonzero, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .sum, .cons a (.cons b .nil) => some ((show Nat from a) + (show Nat from b))
    | .addCount, .cons n (.cons a .nil) => some (n.down + (show Nat from a))
    | .not, .cons b .nil => some ⟨!b.down⟩

private def sorts (i : Fin 15) : Ty Unit :=
  match i.val with
  | 1 | 2 | 6 | 12 | 13 => .count
  | 4 | 11 => .bool
  | _ => acc

private inductive ExtraRow where
  | theta
  | parameter
  | cycle

-- Rows are interleaved, the root is row 5, and both accumulator updates use
-- row 0. The supplied-boundary regressions use an extra θ with self-feedback.
private def graph (crosses : Bool) (extra : ExtraRow := .theta) (ambiguous : Bool := false) :
    Graph Op carried [acc] 15 1 where
  forest := ⟨fun _ => none⟩
  sort := sorts
  node := fun i =>
    match i with
    | 0 => .ofLabel (.op .sum)
        (.cons ⟨8, rfl⟩ (.cons (if crosses then ⟨10, rfl⟩ else ⟨3, rfl⟩) .nil))
    | 1 => .ofLabel (.theta 0) (.cons ⟨13, rfl⟩ (.cons ⟨6, rfl⟩ .nil))
    | 2 => .ofLabel (.pass 0) (.cons ⟨11, rfl⟩ .nil)
    | 3 => .ofLabel (.theta 0)
        (.cons (if ambiguous then ⟨9, rfl⟩ else ⟨14, rfl⟩) (.cons ⟨0, rfl⟩ .nil))
    | 4 => .ofLabel (.op .nonzero) (.cons ⟨12, rfl⟩ .nil)
    | 5 => .ofLabel (.eval 0) (.cons ⟨8, rfl⟩ (.cons ⟨2, rfl⟩ .nil))
    | 6 => .ofLabel (.op .pred) (.cons ⟨1, rfl⟩ .nil)
    | 7 => .ofLabel (.op .addCount) (.cons ⟨1, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
    | 8 => .ofLabel (.theta 0) (.cons ⟨9, rfl⟩ (.cons ⟨7, rfl⟩ .nil))
    | 9 => .ofLabel (.param (.tail .head)) .nil
    | 10 =>
      match extra with
      | .theta => .ofLabel (.theta 0) (.cons ⟨14, rfl⟩ (.cons ⟨10, rfl⟩ .nil))
      | .parameter => .ofLabel (.param (.tail .head)) .nil
      | .cycle => .ofLabel (.op .sum) (.cons ⟨10, rfl⟩ (.cons ⟨8, rfl⟩ .nil))
    | 11 => .ofLabel (.op .not) (.cons ⟨4, rfl⟩ .nil)
    | 12 => .ofLabel (.op .twice) (.cons ⟨1, rfl⟩ .nil)
    | 13 => .ofLabel (.param .head) .nil
    | 14 => .ofLabel (.param (.tail (.tail .head))) .nil
  roots := .cons ⟨5, rfl⟩ .nil

private def phase (i : Fin 15) : Nat := if i = 5 then 2 else if i = 2 then 1 else 0

private def localRank (i : Fin 15) : Nat :=
  match i.val with
  | 7 | 11 => 5
  | 0 | 4 => 4
  | 6 | 12 => 3
  | 1 | 3 | 8 | 10 => 2
  | _ => 1

private def descriptor (crosses : Bool) : Descriptor (graph crosses) where
  theta := .cons ⟨1, rfl⟩ (.cons ⟨8, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
  initial := .cons ⟨13, rfl⟩ (.cons ⟨9, rfl⟩ (.cons ⟨14, rfl⟩ .nil))
  next := .cons ⟨6, rfl⟩ (.cons ⟨7, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
  guard := ⟨4, rfl⟩
  negated := ⟨11, rfl⟩
  negate := .not
  pass := ⟨2, rfl⟩
  returnSlot := .tail .head

private def rank : DemandRank 15 1 := [.phase phase, .counter 0, .phase localRank]

private def input (n a b : Nat) : Tuple model.Value carried := .cons ⟨n⟩ (.cons a (.cons b .nil))

private def checked := checkScheduled (graph false) (descriptor false) rank

private def run (fuel n a b : Nat) : Option Nat := do
  let cert ← checked
  cert.runFuel model fuel (input n a b)

set_option interpreter.prefer_native false

-- The updates read the old counter and both old accumulators. At the first
-- step the new pair is (13, 11), and at the second it is (25, 24).
/-- info: (some 25, some 10, none) -/
#guard_msgs in
#eval (run 2 2 10 1, run 0 0 10 1, run 1 2 10 1)

-- Demand ranking alone admits the fourth θ. The checker refuses to read
-- it as a same-iteration update operand because it is outside the region.
/-- info: (true, true, true) -/
#guard_msgs in
#eval (rank.check (graph true), (checkScheduled (graph true) (descriptor true) rank).isNone,
  (check (graph true) (descriptor true) ⟨[12, 4], [6, 0, 7], rank⟩).isNone)

-- An operand must be in scope before its consumer is emitted.
/-- info: true -/
#guard_msgs in
#eval (check (graph false) (descriptor false) ⟨[12, 4], [6, 7, 0], rank⟩).isNone

-- The inferred update order includes the shared sum just once.
/-- info: some [6, 0, 7] -/
#guard_msgs in
#eval sliceOrder (graph false) (descriptor false) (descriptor false).next

-- The graph and its designated output determine the complete certificate.
private def runInferred (fuel n a b : Nat) : Option Nat := do
  let cert ← Automatic.extract (graph false .parameter)
  cert.runFuel model fuel (input n a b)

/-- info: (some 25, some 10, none) -/
#guard_msgs in
#eval (runInferred 2 2 10 1, runInferred 0 0 10 1, runInferred 1 2 10 1)

-- Both accumulator θs initialize from the first accumulator's port.
-- Matching the total θ count alone would miss the ambiguity.
/-- info: (3, 2, true) -/
#guard_msgs in
#eval let bad := graph false .parameter true
  (Automatic.thetaCount bad, (Automatic.candidates bad (.tail .head)).length,
    (Automatic.extract bad).isNone)

-- The same boundary can be read with an unused ordinary self-cycle.
-- The assembled demand rank is checked across the entire graph.
/-- info: (true, false, true) -/
#guard_msgs in
#eval let cyclic := graph false .cycle
  ((Automatic.inferBoundary cyclic).isSome, (Automatic.inferDemandRank cyclic).check cyclic,
    (Automatic.extract cyclic).isNone)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Tests

open RVSDG (Tuple)

private abbrev Outer : List (Ty Unit) := [.count, .count]
private abbrev Inner : List (Ty Unit) := [.count, .count, .count]

private inductive Op : InstructionSet Unit where
  | positive : Op [.count] .bool
  | pred : Op [.count] .count
  | add : Op [.count, .count] .count
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .positive, .cons x .nil => some ⟨x.down != 0⟩
    | .pred, .cons x .nil => some ⟨x.down - 1⟩
    | .add, .cons x (.cons y .nil) => some ⟨x.down + y.down⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

-- Outer store is (counter, accumulator). The child captures these two
-- values and a second copy of the old outer counter for the final commit.
private def form : Form Op Outer Inner .count where
  outerGuard := .op .positive (.cons (.var .head) .nil)
  captures := .cons .head (.cons (.tail .head) (.cons .head .nil))
  innerGuard := .op .positive (.cons (.var .head) .nil)
  innerStep :=
    .seq (.assign (.op .pred (.cons (.var .head) .nil))) <|
    .seq (.assign (.op .add (.cons (.var (.tail .head)) (.cons (.var (.tail (.tail .head))) .nil)))) <|
    .project (.cons (.tail .head) (.cons .head (.cons (.tail (.tail (.tail (.tail .head)))) .nil)))
  commit :=
    .seq (.assign (.op .pred (.cons (.var (.tail (.tail .head))) .nil))) <|
    .project (.cons .head (.cons (.tail (.tail .head)) .nil))
  returnSlot := .tail .head
  negate := .not

private def outerStore (n acc : Nat) : Tuple model.Value Outer := .cons ⟨n⟩ (.cons ⟨acc⟩ .nil)
private def innerStore (n acc saved : Nat) : Tuple model.Value Inner :=
  .cons ⟨n⟩ (.cons ⟨acc⟩ (.cons ⟨saved⟩ .nil))

private def run (outerFuel innerFuel n acc : Nat) : Option Nat := do
  let _ ← check form form.compile
  (form.runFuel model outerFuel innerFuel (outerStore n acc)).map ULift.down

-- The first inner invocation takes three steps, then two, then one.
-- The sum of their contributions is 6 + 3 + 1.
set_option interpreter.prefer_native false in
/-- info: (some 10, some 7, none, none) -/
#guard_msgs in
#eval (run 3 3 3 0, run 0 0 0 7, run 2 3 3 0, run 3 2 3 0)

-- The modified graph remains sorted and has the same number of rows.
-- Its child counter reads the old accumulator instead of the old counter.
private def wrongCapture : Form Op Outer Inner .count :=
  { form with captures := .cons (.tail .head) (.cons (.tail .head) (.cons .head .nil)) }

private def wrongParent : Graph Op Outer [.count] form.size form.size :=
  { form.compile with forest := ⟨fun _ => none⟩ }

set_option interpreter.prefer_native false in
/-- info: (true, true) -/
#guard_msgs in
#eval ((check form wrongCapture.compile).isNone, (check form wrongParent).isNone)

private def childResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => childResult (n + 1 + acc) n

private theorem childExec (n acc saved : Nat) :
    Exec model form.child (innerStore n acc saved) (some (innerStore 0 (childResult acc n) saved)) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih =>
    exact .whileStep (next := innerStore n (n + 1 + acc) saved) rfl
      (form.innerStep.runLoopFree_enableWhile (innerStore (n + 1) acc saved)) (ih _)

private def outerResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => outerResult (childResult acc (n + 1)) n

private theorem outerExec (n acc : Nat) :
    Exec model form.source.body (outerStore n acc) (some (outerStore 0 (outerResult acc n))) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih =>
    refine .whileStep (next := outerStore n (childResult acc (n + 1))) rfl ?_ (ih _)
    exact .seq (next := innerStore (n + 1) acc (n + 1)) .project
      (.seq (childExec (n + 1) acc (n + 1))
        (form.commit.runLoopFree_enableWhile (innerStore 0 (childResult acc (n + 1)) (n + 1))))

private theorem total : form.Total model where
  guard old := ⟨(old.get .head).down != 0, rfl⟩
  child old _ := by
    cases old with | cons n tail =>
    cases tail with | cons acc tail =>
    cases tail
    exact ⟨_, childExec n.down acc.down n.down⟩
  commit {old final} _ := by
    cases final with | cons _ tail =>
    cases tail with | cons _ tail =>
    cases tail with | cons _ tail =>
    cases tail
    exact ⟨_, rfl⟩

private def cert : Certificate form form.compile := ⟨rfl⟩

private theorem returnsTen : form.source.Returns model (outerStore 3 0) ⟨10⟩ :=
  ⟨outerStore 0 (outerResult 0 3), outerExec 3 0, rfl⟩

private theorem observedTen (i : Index form.size) :
    form.compile.observe model
      (form.compile.denote model (outerStore 3 0) cert.demandWellFounded) i =
      .cons (some ⟨10⟩) .nil :=
  (cert.returns_iff_observe model (outerStore 3 0) total (fun _ => rfl) i ⟨10⟩).mp returnsTen

example (i : Index form.size) : ∃ k final,
    WhileTrace model form.outerGuard form.body k (outerStore 3 0) final ∧
      final.get form.returnSlot = ⟨10⟩ :=
  cert.trace_of_defined model (outerStore 3 0) total (fun _ => rfl) i (observedTen i)

private def runDiscovered {n : Nat} (g : Graph Op Outer [.count] n n)
    (outerFuel innerFuel n0 acc : Nat) : Option Nat := do
  let accepted ← Automatic.extract g
  (accepted.form.runFuel model outerFuel innerFuel (outerStore n0 acc)).map ULift.down

-- Same graph as the supplied check, with the form now recovered by the graph-only API.
-- Capturing a different in-scope old value defines a second valid input graph.
/-- info: (some 10, some 5) -/
#guard_msgs in
#eval (runDiscovered form.compile 3 3 3 0, runDiscovered wrongCapture.compile 2 2 2 1)

-- The child initializer bypasses the old outer θ and reads its parameter
-- directly. The modified edge is well sorted, but escapes the capture scope.
private def bypassCapture {n : Nat} (g : Graph Op Outer [.count] n n) :
    Graph Op Outer [.count] n n :=
  { g with node := fun i =>
      let row := g.node i
      match row with
      | ⟨_, .theta loop, args⟩ =>
        if (g.forest.parent loop).isSome then
          match Region.nodeAt g (args.get .head) with
          | ⟨_, .theta _, outerArgs⟩ =>
            .ofLabel (.theta loop) (.cons (outerArgs.get .head) (.cons (args.get (.tail .head)) .nil))
          | _ => row
        else row
      | _ => row }

/-- info: (true, true) -/
#guard_msgs in
#eval ((Automatic.extract (bypassCapture form.compile)).isNone,
  (Automatic.extract wrongParent).isNone)

private def reverseId {width : Nat} (i : Fin width) : Fin width :=
  ⟨width - 1 - i.val, by have := i.isLt; omega⟩

private theorem reverseTwice {width : Nat} (i : Fin width) : reverseId (reverseId i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [reverseId]
  omega

private def reversed (width : Nat) : Fin width ≃ Fin width :=
  ⟨reverseId, reverseId, reverseTwice, reverseTwice⟩

private def moved : Graph Op Outer [.count] form.size form.size :=
  form.compile.reindex (reversed form.size) (reversed form.size)

private def runMoved : Option Nat := do
  let ids ← checkFinEquiv (reverseId (width := form.size)) reverseId
  let accepted ← Reindexed.extract moved ids ids
  (accepted.form.runFuel model 3 3 (outerStore 3 0)).map ULift.down

-- Both the row addresses and loop keys have changed.
/-- info: some 10 -/
#guard_msgs in
#eval runMoved

-- The supplied maps cannot certify a table whose child counter captures
-- a different old slot than the reference graph.
private def wrongWire : Graph Op Outer [.count] form.size form.size :=
  wrongCapture.compile.reindex (reversed form.size) (reversed form.size)

/-- info: true -/
#guard_msgs in
#eval let ids := reversed form.size
  (form.compile.checkReindex wrongWire ids ids).isNone

private def movedCertificate :
    form.compile.ReindexCertificate moved (reversed form.size) (reversed form.size) :=
  ⟨rfl⟩

private theorem movedWF : WellFounded moved.Demand :=
  movedCertificate.demandWellFounded_iff.mpr cert.demandWellFounded

example (i : Index form.size) :
    moved.observe model (moved.denote model (outerStore 3 0) movedWF) i = .cons (some ⟨10⟩) .nil :=
  (movedCertificate.observe_denote model (outerStore 3 0) cert.demandWellFounded movedWF i).trans
    (observedTen _)

-- The outer pass key is permuted independently of its vertex address.
-- The returned accumulator is the only designated root, so the other
-- outer eval must be covered by the discovered bundle anchor.
private def movedIndependently : Graph Op Outer [.count] form.size form.size :=
  form.compile.reindex (reversed form.size)
    (Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩)

private def runInferredNumbering : Option Nat := do
  let accepted ← Reindexed.Automatic.extract movedIndependently
  (accepted.form.runFuel model 3 3 (outerStore 3 0)).map ULift.down

/-- info: some 10 -/
#guard_msgs in
#eval runInferredNumbering

/-- info: true -/
#guard_msgs in
#eval (Reindexed.Automatic.extract (bypassCapture movedIndependently)).isNone

-- The second parameter is isolated when the primitive's two operands
-- share the first parameter. An explicit anchor covers the isolated row.
private def sharedOperands (split : Bool) : Graph Op Outer [.count] 3 0 where
  forest := ⟨Fin.elim0⟩
  sort _ := .count
  node i := match i with
    | 0 => .ofLabel (.op .add) (.cons ⟨1, rfl⟩ (.cons ⟨if split then 2 else 1, rfl⟩ .nil))
    | 1 => .ofLabel (.param .head) .nil
    | 2 => .ofLabel (.param (.tail .head)) .nil
  roots := .cons ⟨0, rfl⟩ .nil

-- Splitting a repeated wire forces one source row to pair with two
-- target rows, even though every operand sort still agrees.
/-- info: (true, true, true) -/
#guard_msgs in
#eval
  let same := sharedOperands false
  let changed := sharedOperands true
  let infer new anchors := Silmaril.SSA.PEG.Reindex.Automatic.infer same new anchors
  ((infer same []).isNone, (infer same [(2, 2)]).isSome, (infer changed [(2, 2)]).isNone)

private def paddedSort {n : Nat} (sort : Fin n → Ty Unit) (i : Fin (n + 1)) : Ty Unit :=
  if h : i.val < n then sort (i.castLT h) else .count

private def padRef {n : Nat} {sort : Fin n → Ty Unit} {t : Ty Unit} (r : Ref sort t) :
    Ref (paddedSort sort) t :=
  ⟨r.id.castSucc, by simpa [paddedSort, r.id.isLt] using r.typed⟩

-- Add a dead primitive that consumes the designated result. Observing
-- the result never demands its consumer. Keep the original loop table.
private def pad {n l : Nat} (g : Graph Op Outer [.count] n l) : Graph Op Outer [.count] (n + 1) l where
  forest := g.forest
  sort := paddedSort g.sort
  node i :=
    if h : i.val < n then
      let row := g.node (i.castLT h)
      (show paddedSort g.sort i = g.sort (i.castLT h) by simp [paddedSort, h]).symm ▸
        Node.ofLabel row.label (row.args.map fun _ r => padRef r)
    else
      (show paddedSort g.sort i = .count by simp [paddedSort, h]).symm ▸
        Node.ofLabel (.op .pred) (.cons (padRef (g.roots.get .head)) .nil)
  roots := g.roots.map fun _ r => padRef r

private def padded := pad movedIndependently

-- Structured compiler images have equally many row and loop keys.
-- The padded graph cannot have both bijections to any such image.
example {k : Nat} :
    ¬ (Nonempty (Fin (form.size + 1) ≃ Fin k) ∧ Nonempty (Fin form.size ≃ Fin k)) :=
  fun ⟨rows, loops⟩ =>
    Nat.succ_ne_self _ ((Fin.equiv_iff_eq.mp rows).trans (Fin.equiv_iff_eq.mp loops).symm)

private def runProjected : Option (Bool × Nat) := do
  let a ← Projected.extract padded
  let value ← a.core.form.runFuel model 3 3 (outerStore 3 0)
  return (a.projection.rows.length == form.size, value.down)

/-- info: some (true, 10) -/
#guard_msgs in
#eval runProjected

-- Retain the child θ but delete its initializer from the proposed
-- projection. The initializer is an outer θ, not the designated eval.
private def rejectsMissingCapture : Option Bool := do
  let cached := Automatic.cacheRows padded
  let header ← Automatic.locate cached
  let exit ← (Automatic.bundleIds cached header.childKey).head?
  let slot ← Automatic.readSlotAt cached header.childKey header.childPass (Ref.ofId cached.sort exit)
  let rows := (List.finRange (form.size + 1)).filter
    (fun i => i != slot.initial.id && i != Fin.last form.size)
  return decide (slot.theta.id ∈ rows) && (padded.checkProjection rows).isNone

/-- info: some true -/
#guard_msgs in
#eval rejectsMissingCapture

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Tests
