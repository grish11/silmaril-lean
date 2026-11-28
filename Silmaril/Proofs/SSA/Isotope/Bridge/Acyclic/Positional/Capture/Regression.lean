module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Tests

open Isotope.Semantics (BoundEnv InstructionModel)
open LambdaSSA.Semantics (Env extend)

set_option backward.isDefEq.respectTransparency false

private inductive Op | enter | test | left | right | join
  deriving DecidableEq

private abbrev N : Ty Unit := .base ()
private abbrev Tagged : Ty Unit := .coprod N N
private abbrev D := Ty.denote (fun _ : Unit => Nat)

local instance : HasTy Op (Ty Unit) where
  src
    | .enter | .test => Tagged
    | .left | .right | .join => .product N N
  trg
    | .enter | .test | .join => Tagged
    | .left | .right => N

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private abbrev ambient : BoundCtx (Ty Unit) 2 := .snoc (.snoc .nil N) Tagged
private abbrev types : Fin 4 → Ty Unit := ![N, N, N, Tagged]

private def entry : Operand Op ambient Tagged := ⟨.op .enter (.bv 0), .op .bv⟩
private def classifier : Operand Op (ambient.snoc Tagged) Tagged := ⟨.op .test (.bv 0), .op .bv⟩
private def left : Operand Op (ambient.snoc N) N :=
  ⟨.op .left (.let₂ (.pair (.bv 2) (.bv 0)) (.pair (.bv 1) (.bv 0))),
    .op (.let₂ (.pair .bv .bv) (.pair .bv .bv))⟩
private def right : Operand Op (ambient.snoc N) N :=
  ⟨.op .right (.pair (.bv 2) (.bv 0)), .op (.pair .bv .bv)⟩
private def join : Operand Op (ambient.snoc N) Tagged :=
  ⟨.op .join (.pair (.bv 2) (.bv 0)), .op (.pair .bv .bv)⟩

/-- Local labels 1 and 2 both jump backward to label 0, and entry label 3
selects the arm. Both arms and the join read the shared bias. -/
private abbrev diamond : Table Op ambient [N, N] 3 where
  types := types
  block := fun i =>
    Fin.cases (motive := fun j => Block Op ambient types [N, N] (types j))
      (.case join (.exit (i := 0) rfl) (.exit (i := 1) rfl))
      (fun j => Fin.cases (motive := fun j => Block Op ambient types [N, N] (types j.succ))
        (.jump left (.local 0))
        (fun j => Fin.cases (motive := fun j => Block Op ambient types [N, N] (types j.succ.succ))
          (.jump right (.local 0))
          (fun j => Fin.cases (motive := fun j => Block Op ambient types [N, N] (types j.succ.succ.succ))
            (.case classifier (.local 1) (.local 2))
            (fun j => j.elim0) j) j) j) i

private theorem checked : diamond.check = true := by cbv

example : (List.finRange 4).map diamond.localTargets = [[], [0], [0], [1, 2]] := rfl

private theorem compile_join {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope ambient γ) :
    diamond.compileAt checked 0 s =
      .case (s.operand join) (.br (i := 0) rfl ⟨.bv 0, .bv⟩) (.br (i := 1) rfl ⟨.bv 0, .bv⟩) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_left {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope ambient γ) :
    diamond.compileAt checked 1 s =
      .join (.br (s.operand left)) (diamond.compileAt checked 0 (.skip s N)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_right {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope ambient γ) :
    diamond.compileAt checked 2 s =
      .join (.br (s.operand right)) (diamond.compileAt checked 0 (.skip s N)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_classifier {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope ambient γ) :
    diamond.compileAt checked 3 s =
      .case (s.operand classifier) (diamond.compileAt checked 1 (.skip s Tagged))
        (diamond.compileAt checked 2 (.skip s Tagged)) := by
  rw [Table.compileAt.eq_def]
  rfl

private def finish (bias packet : Nat) : Sum Nat Nat :=
  let result := 10 * bias + packet
  if packet < 20 then .inl result else .inr result

private def model : InstructionModel D Op (StateM (List Op)) where
  eval
    | .enter => fun x s => (x, s ++ [.enter])
    | .test => fun x s => (x, s ++ [.test])
    | .left => fun x s => (Nat.add x.1 x.2, s ++ [.left])
    | .right => fun x s => (Nat.add (Nat.add x.1 x.2) 20, s ++ [.right])
    | .join => fun x s => (finish x.1 x.2, s ++ [.join])

private def input (bias : Nat) (tag : Sum Nat Nat) : BoundEnv D ambient :=
  BoundEnv.snoc (D := D) (BoundEnv.snoc (A := N) (fun i => Fin.elim0 i) bias) tag

/-- The left path reads 7 in both its arm and its shared successor. -/
example :
    (diamond.toLetCase checked 3 entry).2.denote D model (fun x => nomatch x)
      (input 7 (.inl 3)) [] = (.inl (80 : Nat), [.enter, .test, .left, .join]) := by
  unfold Table.toLetCase Table.toFiniteExit
  rw [compile_classifier .base, compile_left (.skip .base Tagged), compile_right (.skip .base Tagged),
    compile_join (.skip (.skip .base Tagged) N)]
  rfl

/-- The right path returns at the second ordered position, with one shared
successor event and no event from the other arm. -/
example :
    (diamond.toLetCase checked 3 entry).2.denote D model (fun x => nomatch x)
      (input 7 (.inr 3)) [] = (.inr (.inl (100 : Nat)), [.enter, .test, .right, .join]) := by
  unfold Table.toLetCase Table.toFiniteExit
  rw [compile_classifier .base, compile_left (.skip .base Tagged), compile_right (.skip .base Tagged),
    compile_join (.skip (.skip .base Tagged) N)]
  rfl

private def result : Op → Value Nat → Option (Value Nat)
  | .enter, value | .test, value => some value
  | .left, .pair (.atom bias) (.atom packet) => some (.atom (bias + packet))
  | .right, .pair (.atom bias) (.atom packet) => some (.atom (bias + packet + 20))
  | .join, .pair (.atom bias) (.atom packet) =>
    some (match finish bias packet with | .inl a => .inl (.atom a) | .inr b => .inr (.atom b))
  | _, _ => none

private def step (op : Op) (input : Value Nat) (before : List Op) (output : Value Nat)
    (after : List Op) : Prop :=
  result op input = some output ∧ after = before ++ [op]

private def nativeInput (bias : Nat) (tag : Value Nat) : Env Nat :=
  extend (extend (fun _ => .unit) (.atom bias)) tag

/-- The original positional dispatcher follows the same effect order and
returns at outward label zero. -/
example : LambdaSSA.Semantics.Region.Eval step
      (nativeInput 7 (.inl (.atom 3))) (diamond.toSSA 3 entry) [] 0 (.atom 80)
      [.enter, .test, .left, .join] := by
  let env := nativeInput 7 (.inl (.atom 3))
  have entered : LambdaSSA.Semantics.Region.Eval step env (diamond.entry 3 entry) [] 3
      (.inl (.atom 3)) [.enter] :=
    .br (.op .var ⟨rfl, rfl⟩)
  have selected : LambdaSSA.Semantics.Region.Eval step (extend env (.inl (.atom 3)))
      (diamond.block 3).toSSA [.enter] 1 (.atom 3) [.enter, .test] :=
    .case_inl (.op .var ⟨rfl, rfl⟩) (.br .var)
  have arm : LambdaSSA.Semantics.Region.Eval step (extend env (.atom 3))
      (diamond.block 1).toSSA [.enter, .test] 0 (.atom 10) [.enter, .test, .left] :=
    .br (.op (.let₂ (.pair .var .var) (.pair .var .var)) ⟨rfl, rfl⟩)
  have joined : LambdaSSA.Semantics.Region.Eval step (extend env (.atom 10))
      (diamond.block 0).toSSA [.enter, .test, .left] 4 (.atom 80) [.enter, .test, .left, .join] :=
    .case_inl (.op (.pair .var .var) ⟨rfl, rfl⟩) (.br .var)
  exact .cfg entered (.step (by decide) selected
    (.step (by decide) arm (.step (by decide) joined (.exit (by decide)))))

example : LambdaSSA.Semantics.Region.Eval step
      (nativeInput 7 (.inr (.atom 3))) (diamond.toSSA 3 entry) [] 1 (.atom 100)
      [.enter, .test, .right, .join] := by
  let env := nativeInput 7 (.inr (.atom 3))
  have entered : LambdaSSA.Semantics.Region.Eval step env (diamond.entry 3 entry) [] 3
      (.inr (.atom 3)) [.enter] :=
    .br (.op .var ⟨rfl, rfl⟩)
  have selected : LambdaSSA.Semantics.Region.Eval step (extend env (.inr (.atom 3)))
      (diamond.block 3).toSSA [.enter] 2 (.atom 3) [.enter, .test] :=
    .case_inr (.op .var ⟨rfl, rfl⟩) (.br .var)
  have arm : LambdaSSA.Semantics.Region.Eval step (extend env (.atom 3))
      (diamond.block 2).toSSA [.enter, .test] 0 (.atom 30) [.enter, .test, .right] :=
    .br (.op (.pair .var .var) ⟨rfl, rfl⟩)
  have joined : LambdaSSA.Semantics.Region.Eval step (extend env (.atom 30))
      (diamond.block 0).toSSA [.enter, .test, .right] 5 (.atom 100) [.enter, .test, .right, .join] :=
    .case_inr (.op (.pair .var .var) ⟨rfl, rfl⟩) (.br .var)
  exact .cfg entered (.step (by decide) selected
    (.step (by decide) arm (.step (by decide) joined (.exit (by decide)))))

-- The backward-numbered arms share row zero. The emitted LetCase term
-- retains the product destructure in the left request argument.
example :
    Region.Paper.WithBoundEntryEta.Eqv ambient.toList (diamond.toSSA 3 entry)
      (Reverse.tableGrammar diamond checked 3 entry).toTable.toSSA [N, N] ∧
    (Reverse.tableGrammar diamond checked 3 entry).toTable.toLetCase = diamond.toLetCase checked 3 entry :=
  diamond.native_roundTrip checked 3 entry

example :
    ReplayEqv false ambient.toList (diamond.toSSA 3 entry).bindBranchArguments.packExits
      ((Code.ofLetCase (diamond.toLetCase checked 3 entry).2).guardedSSA 0)
      [Region.packedExitType [N, N]] ∧
    ReplayEqv false ambient.toList ((Code.ofLetCase (diamond.toLetCase checked 3 entry).2).guardedSSA 0)
      (Reverse.tableGrammar diamond checked 3 entry).toTable.toSSA.bindBranchArguments.packExits
      [Region.packedExitType [N, N]] ∧
    (Reverse.tableGrammar diamond checked 3 entry).toTable.toLetCase = diamond.toLetCase checked 3 entry :=
  diamond.native_recompile checked 3 entry

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Tests
