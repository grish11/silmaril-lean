module

import Silmaril.SSA.Peggy.SimpleValidation.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms
import Silmaril.SSA.PEG.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Thms
meta import Silmaril.SSA.Peggy.SimpleValidation.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined.Defs
meta import Silmaril.SSA.PEG.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Defs
meta import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Defs

namespace Silmaril.SSA.Peggy.SimpleValidation.Tests

open PEG (Ty)
open PEG.Simple (Expr Stmt)
open Bridge.Egg (Term PrimitiveEq context model)
open Bridge.Figure11 (toAcyclic)
open Optimizer (Rule)
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | add : Op [.count, .count] .count
  | triple : Op [.count] .count
  | bad : Op [] .count
  deriving DecidableEq

private def arithmetic : PEG.Interpretation Op where
  carrier _ := Unit
  run
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .triple, .cons a .nil => some ⟨(a.down + a.down) + a.down⟩
    | .bad, .nil => none

private abbrev params : List (Ty Unit) := [.bool, .count]
private abbrev input (flag : Bool) (n : Nat) : Tuple arithmetic.Value params :=
  .cons ⟨flag⟩ (.cons ⟨n⟩ .nil)

private def plus {vars : List (Ty Unit)} (a b : Expr Op vars .count) : Expr Op vars .count :=
  .op .add (.cons a (.cons b .nil))

private def trueArm : Stmt Op false params [.count] :=
  let x := Expr.var (.tail .head)
  .seq (.assign (plus (plus x x) x))
    (.seq (.assign (plus (.var .head) (.var .head))) (.project (.cons .head .nil)))

/-- The true arm uses its computed triple twice. The false arm fails. -/
private def source : PEG.Simple.Program Op false params .count :=
  ⟨[.count],
    .branch (.var .head) trueArm (.seq (.assign (.op .bad .nil)) (.project (.cons .head .nil))),
    .head⟩

private abbrev pattern : List (Ty Unit) := [.count]

private def addPattern (a b : Term Op pattern .count) : Term Op pattern .count :=
  .app (.prim Op.add) (fun i => match i with | 0 => a | 1 => b)

private def compress : Rule Op .count :=
  let x : Term Op pattern .count := .var 0
  { scope := pattern.length
    context := context pattern
    guards := []
    lhs := addPattern (addPattern x x) x
    rhs := .app (.prim Op.triple) (fun i => match i with | 0 => ⟨0, rfl⟩) }

private def rules : List (Optimizer.Contextual.Schema Op) := [⟨.count, compress⟩]
private abbrev opEq : PrimitiveEq Op := fun _ _ => inferInstance

private def addValues (a b : Option Nat) : Option Nat :=
  (toAcyclic arithmetic).applyPrim Op.add (fun i => match i with | 0 => a | 1 => b)

private def tripleValue (value : Option Nat) : Option Nat :=
  (toAcyclic arithmetic).applyPrim Op.triple (fun i => match i with | 0 => value)

/-- Includes the substitution assigning bottom to x. -/
private theorem compressLaw : compress.core.Holds (model (toAcyclic arithmetic)) := by
  intro ρ _
  let v : Option Nat := ρ (show Fin pattern.length from 0)
  change addValues (addValues v v) v = tripleValue v
  cases v <;> rfl

private theorem rulesSound : ∀ rule ∈ rules.map Optimizer.Contextual.core,
    rule.Holds (model (toAcyclic arithmetic)) := by
  intro rule mem
  have h : rule = compress.core := List.mem_singleton.mp mem
  exact h ▸ compressLaw

private def answer (n : Nat) : Nat :=
  let y := (n + n) + n
  y + y

private theorem sourceReturns (n : Nat) : source.Returns arithmetic (input true n) ⟨answer n⟩ := by
  let afterTriple : Tuple arithmetic.Value (.count :: params) := .cons ⟨(n + n) + n⟩ (input true n)
  let afterSum : Tuple arithmetic.Value (.count :: .count :: params) :=
    .cons ⟨answer n⟩ afterTriple
  refine ⟨.cons ⟨answer n⟩ .nil, ?_, rfl⟩
  exact .branchTrue rfl
    (.seq (next := afterTriple) (.assign rfl)
      (.seq (next := afterSum) (.assign rfl) .project))

example (accepted : Accepted source rules) (n : Nat) :
    accepted.output.runLoopFree arithmetic (input true n) = some ⟨answer n⟩ :=
  accepted.runLoopFree arithmetic rulesSound _ (sourceReturns n)

private def opName {ins : List (Ty Unit)} {out : Ty Unit} : Op ins out → String
  | .add => "add"
  | .triple => "triple"
  | .bad => "bad"

private def assignedOps : {vars outs : List (Ty Unit)} → Stmt Op false vars outs → List String
  | _, _, .assign (.op op _) => [opName op]
  | _, _, .assign (.var _) | _, _, .project _ => []
  | _, _, .seq a b => assignedOps a ++ assignedOps b
  | _, _, .branch _ yes no => assignedOps yes ++ assignedOps no
  | _, _, .while impossible _ _ => nomatch impossible

private def report (depth : Nat) (flag : Bool) :
    Except Rejection (Nat × Nat × List String × Option Nat) := do
  let accepted ← optimize opEq rules depth source
  let before := Optimizer.Contextual.cost ⟨_, source.translate, accepted.ranked⟩
  let after := Optimizer.Contextual.cost accepted.candidate.program
  return (before, after, assignedOps accepted.output.body,
    (accepted.output.runLoopFree arithmetic (input flag 14)).map ULift.down)

set_option interpreter.prefer_native false

/-- info: Except.ok (5, 5, ["add", "add", "add", "bad"], some 84) -/
#guard_msgs in
#eval report 0 true

-- The rule matches inside the selected arm, below the shared sum and its enclosing φ.
/-- info: Except.ok (5, 4, ["triple", "add", "bad"], some 84) -/
#guard_msgs in
#eval report 1 true

/-- info: Except.ok (5, 4, ["triple", "add", "bad"], none) -/
#guard_msgs in
#eval report 1 false

/-- Both arms read the same previously computed value. The current
scheduler would duplicate its writer and rejects this placement. -/
private def sharedArms : PEG.Simple.Program Op false params .count :=
  ⟨[.count], .seq (.assign (.op .triple (.cons (.var (.tail .head)) .nil)))
    (.branch (.var (.tail .head)) (.project (.cons .head .nil)) (.project (.cons .head .nil))),
    .head⟩

private def rejected : Option Rejection :=
  match optimize opEq [] 0 sharedArms with
  | .ok _ => none
  | .error error => some error

/-- info: some (Silmaril.SSA.Peggy.SimpleValidation.Rejection.reversion) -/
#guard_msgs in
#eval rejected

end Silmaril.SSA.Peggy.SimpleValidation.Tests

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Tests

open PEG
open PEG.Simple
open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | zero : Op [] .count
  | one : Op [] .count
  | sub : Op [.count, .count] .count
  | subTwice : Op [.count, .count, .count] .count
  | aboveTwo : Op [.count] .bool
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .one, .nil => some ⟨1⟩
    | .sub, .cons n (.cons k .nil) => some ⟨n.down - k.down⟩
    | .subTwice, .cons n (.cons a (.cons b .nil)) => some ⟨n.down - a.down - b.down⟩
    | .aboveTwo, .cons n .nil => some ⟨decide (n.down > 2)⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private abbrev params : List (Ty Unit) := [.count]
private def store (n : Nat) : Tuple model.Value params := .cons ⟨n⟩ .nil

private def source : WhileProgram Op params .count where
  guard := .op .aboveTwo (.cons (.var .head) .nil)
  body :=
    .seq (.assign (.op .one .nil))
      (.seq (.assign (.op .sub (.cons (.var (.tail .head)) (.cons (.var .head) .nil))))
        (.project (.cons .head .nil)))
  retvar := .head

private def frontend : Graph Op params [.count] 8 1 := source.translate .not

private def sorts (i : Fin 9) : Ty Unit :=
  if h : i.val < 8 then frontend.sort (i.castLT h) else .count

private def liftRef {t : Ty Unit} (ref : Ref frontend.sort t) : Ref sorts t :=
  ⟨ref.id.castSucc, by simpa [sorts, ref.id.isLt] using ref.typed⟩

private inductive Variant where
  | constant
  | changing
  | parameter
  | ordinaryCycle
  deriving DecidableEq

-- Use the compiler output, with the subtraction now reading θ(1, θ)
-- for its decrement. The original live feedback remains in the table.
private def graph (variant : Variant) : Graph Op params [.count] 9 1 where
  forest := frontend.forest
  sort := sorts
  roots := frontend.roots.map fun _ r => liftRef r
  node i :=
    if eq : i = 3 then
      let counter : Ref sorts .count := if variant = .ordinaryCycle then ⟨3, rfl⟩ else ⟨6, rfl⟩
      eq.symm ▸ (Node.ofLabel (.op .sub) (.cons counter (.cons ⟨8, rfl⟩ .nil)) :
        Node Op params (Fin 1) sorts (sorts 3))
    else if old : i.val < 8 then
      let row := frontend.node (i.castLT old)
      (show sorts i = frontend.sort (i.castLT old) by simp [sorts, old]).symm ▸
        Node.ofLabel row.label (row.args.map fun _ r => liftRef r)
    else
      let seed : Ref sorts .count :=
        match variant with
        | .changing => ⟨6, rfl⟩
        | .parameter => ⟨7, rfl⟩
        | _ => ⟨4, rfl⟩
      (show sorts i = .count by simp [sorts, old]).symm ▸
        Node.ofLabel (.theta 0) (.cons seed (.cons ⟨8, rfl⟩ .nil))

private def rows {n : Nat} (_ : Graph Op params [.count] n 1) : Nat := n

private def run : Option (Nat × Nat × Nat × List Nat × List Nat × Nat) := do
  let a ← (optimize (graph .constant)).toOption
  let target := a.rewrite.matched.extract
  let value ← a.reversion.runFuel model 3 (store 5)
  return (a.rewrite.site.val, rows (graph .constant), rows target,
    refNumbers (target.node 3).args, refNumbers (target.node 6).args, value.down)

-- Remove row 8, redirect subtraction from [6, 8] to [6, 4], and
-- retain the live θ with [7, 3]. Three iterations return 2.
#guard refNumbers ((graph .constant).node 3).args == [6, 8]

/-- info: some (8, 9, 8, [6, 4], [7, 3], 2) -/
#guard_msgs in
#eval run

private def rejection (variant : Variant) : Option Rejection :=
  match optimize (graph variant) with
  | .error e => some e
  | .ok _ => none

-- A varying initializer fails matching. A parameter initializer replays
-- but exposes an out-of-scope operand to the SIMPLE schedule.
#guard rejection .ordinaryCycle == some .sourceRank
#guard rejection .changing == some .noCheckedRewrite
#guard rejection .parameter == some .reversion

private theorem sourceReturns : source.source.Returns model (store 5) ⟨2⟩ := by
  have step (n : Nat) : Exec model source.body.enableWhile (store n) (some (store (n - 1))) :=
    source.body.runLoopFree_enableWhile (store n)
  exact ⟨store 2, .whileStep (next := store 4) rfl (step 5)
    (.whileStep (next := store 3) rfl (step 4)
      (.whileStep (next := store 2) rfl (step 3) (.whileStop rfl))), rfl⟩

-- A concrete replay receipt connects the augmented input to the compiler
-- observation. The executable regression above discovers the receipt.
private def matched : Optimizer.Cyclic.Match (graph .constant) (8 : Fin 9) :=
  (Optimizer.Cyclic.matchAt (graph .constant) 8).get (by decide)

private def inputRank : DemandRank 9 1 :=
  [.phase (fun i => 3 - i.val), .counter 0,
    .phase fun i => match i.val with | 4 => 0 | 8 => 1 | k => 10 - k]

private theorem inputWF : WellFounded (graph .constant).Demand :=
  (graph .constant).demandWellFounded_of_check inputRank (by decide)

private def checked : matched.Replay source.rank :=
  (matched.replay source.rank).get (by decide)

private theorem table_eq {a b : RawGraph Op params [.count] 8 1}
    (forest : a.forest = b.forest) (sort : a.sort = b.sort)
    (rows : ∀ i, HEq (a.node i) (b.node i)) (roots : a.roots = b.roots) : a = b := by
  cases a
  cases b
  rw [RawGraph.mk.injEq]
  refine ⟨forest, sort, ?_, roots⟩
  dsimp only at sort rows ⊢
  cases sort
  exact heq_of_eq (funext fun i => eq_of_heq (rows i))

private theorem target_eq : matched.extract = frontend := by
  apply Graph.eq_of_toRaw_eq
  have row (i : Fin 8) :
      matched.extract.sort i = frontend.sort i ∧
        HEq (matched.extract.toRaw.node i) (frontend.toRaw.node i) := by
    have positions : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, HEq.rfl⟩
  exact table_eq rfl (funext fun i => (row i).1) (fun i => (row i).2) rfl

private theorem frontendObserve (g : Graph Op params [.count] 8 1) (h : g = frontend)
    (wf : WellFounded g.Demand) (i : Index 1) :
    g.observe model (g.denote model (store 5) wf) i = .cons (some ⟨2⟩) .nil := by
  subst g
  exact source.translate_returns .not model (store 5) (fun _ => rfl) sourceReturns i

private theorem inputObserve (i : Index 1) : (graph .constant).observe model
    ((graph .constant).denote model (store 5) inputWF) i = .cons (some ⟨2⟩) .nil :=
  (checked.sound inputWF model (store 5) i).trans (frontendObserve _ target_eq _ i)

example (a : Accepted (graph .constant)) (total : a.reversion.Total model)
    (neg : ∀ b : Bool, model.run a.reversion.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index 1) : a.output.Returns model (store 5) ⟨2⟩ :=
  (a.returns_iff_observe model (store 5) total neg i ⟨2⟩).mpr (inputObserve i)

-- Extend the landed decrement fixture so the update reads one twice:
-- once through the removable self-feedback θ, and once directly.
private def sharedSource : Graph Op params [.count] 9 1 :=
  { graph .constant with
    node := fun i =>
      if site : i = 3 then
        site.symm ▸ (Node.ofLabel (.op .subTwice)
          (.cons ⟨6, rfl⟩ (.cons ⟨8, rfl⟩ (.cons ⟨4, rfl⟩ .nil))) :
            Node Op params (Fin 1) sorts (sorts 3))
      else (graph .constant).node i }

private def sharedMatch : Optimizer.Cyclic.Match sharedSource (8 : Fin 9) :=
  (Optimizer.Cyclic.matchAt sharedSource 8).get (by decide)

private def shared : Cost.Candidate sharedSource :=
  let rank := PEG.Simple.Revert.While.Region.Automatic.inferDemandRank sharedMatch.extract
  ⟨8, sharedMatch.extract, sharedMatch.selectionWithRank rank, sharedMatch.rowsWithRank rank⟩

private inductive Layout where
  | original
  | duplicate
  | shortcut
  deriving DecidableEq

private def representative : Layout → Fin 9 → Fin 9
  | .original, i => i
  | .duplicate, i => if i = 8 then 4 else i
  | .shortcut, i => if i = 8 ∨ i = 4 then 7 else i

private theorem sameSort (layout : Layout) (i : Fin 9) :
    sharedSource.sort (representative layout i) = sharedSource.sort i := by
  cases layout with
  | original => rfl
  | duplicate =>
    simp only [representative]
    split
    · rename_i same
      subst i
      rfl
    · rfl
  | shortcut =>
    simp only [representative]
    split
    · rename_i replaced
      rcases replaced with same | same <;> subst i <;> rfl
    · rfl

private def wireRef (layout : Layout) {t : Ty Unit} (r : Ref sharedSource.sort t) :
    Ref (sharedSource.sort ∘ representative layout) t :=
  if redirected : layout = .shortcut ∧ (r.id = 8 ∨ r.id = 4) then
    ⟨6, by
      obtain ⟨rfl, moved⟩ := redirected
      have typed := r.typed
      rcases moved with hit | hit <;> rw [hit] at typed <;> exact typed⟩
  else ⟨r.id, (sameSort layout r.id).trans r.typed⟩

private def wired (layout : Layout) : Cost.Candidate sharedSource :=
  Cost.Candidate.wire sharedSource (representative layout)
    (fun i => (sharedSource.node (representative layout i)).args.map fun _ => wireRef layout)
    (sharedSource.roots.map fun _ => wireRef layout)

private def duplicated := wired .duplicate
private def shortcut := wired .shortcut
private def original := wired .original

-- Both constant operands are replaced by the live counter in the shortcut.
-- It emits and returns 0, but its operand classes fail extraction replay.
#guard [shortcut.primitiveRows, shared.primitiveRows, duplicated.primitiveRows] == [3, 4, 5]
#guard shortcut.selection.check sharedMatch.classes
#guard !EPEG.Selection.checkRows shortcut.rows sharedMatch.classes
#guard (shortcut.checkLegal sharedMatch.classes).isNone
#guard ((PEG.Simple.Revert.While.Region.Automatic.extract shortcut.graph).bind fun cert =>
  (cert.runFuel model 3 (store 7)).map ULift.down) == some 0

-- Keeping the extra θ passes extraction legality but cannot be emitted
-- by the single-loop reverter. The pool must skip it too.
#guard (original.checkLegal sharedMatch.classes).isSome
#guard (original.check sharedMatch.classes).isNone

private def runPool (pool : List (Cost.Candidate sharedSource))
    (cost : Cost.Candidate sharedSource → Nat := Cost.Candidate.primitiveRows) :
    Option (Nat × Nat × Nat) := do
  let a ← Cost.select sharedMatch.classes cost pool
  let order ← PEG.Simple.Revert.While.Region.sliceOrder a.candidate.graph
    a.reversion.descriptor a.reversion.descriptor.next
  let value ← a.reversion.runFuel model 3 (store 7)
  return (a.candidate.primitiveRows, order.length, value.down)

-- Both legal layouts emit and return 1. The shared one binds the
-- constant once per update, and the duplicate layout binds it twice.
#guard runPool [duplicated] == some (5, 3, 1)
#guard runPool [shortcut, original, duplicated, shared] == some (4, 2, 1)
#guard runPool [shared, duplicated, shortcut] == some (4, 2, 1)
#guard (Cost.select (source := sharedSource) sharedMatch.classes Cost.Candidate.primitiveRows []).isNone
#guard (Cost.select sharedMatch.classes Cost.Candidate.primitiveRows [shortcut, original]).isNone
#guard runPool [duplicated, shared] (fun _ => 0) == some (5, 3, 1)
#guard runPool [shared, duplicated] (fun _ => 0) == some (4, 2, 1)

private theorem sharedSourceWF : WellFounded sharedSource.Demand :=
  sharedSource.demandWellFounded_of_check inputRank (by decide)

example (a : Cost.Accepted sharedSource sharedMatch.classes) (total : a.reversion.Total model)
    (neg : ∀ b : Bool, model.run a.reversion.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index 1) :
    a.output.Returns model (store 7) ⟨1⟩ ↔
      sharedSource.observe model (sharedSource.denote model (store 7) sharedSourceWF) i =
        .cons (some ⟨1⟩) .nil :=
  a.returns_iff_observe sharedSourceWF (sharedMatch.classes_valid sharedSourceWF) total neg i ⟨1⟩

private abbrev bundleParams : List (Ty Unit) := [.count, .count]
private abbrev bundleResults : List (Ty Unit) := [.count, .count, .count]

private def bundleSort (i : Fin 12) : Ty Unit :=
  if i = 6 ∨ i = 7 then .bool else .count

private def evalArgs (theta pass : Ref bundleSort .count) :
    Tuple (Ref bundleSort) [.count, .count] :=
  .cons theta (.cons pass .nil)

private def roots (first second third : Ref bundleSort .count) : Tuple (Ref bundleSort) bundleResults :=
  .cons first (.cons second (.cons third .nil))

private def bundleGraph : Graph Op bundleParams bundleResults 12 1 where
  forest := ⟨fun _ => none⟩
  sort := bundleSort
  node i := match i with
    | 0 => .ofLabel (.param .head) .nil
    | 1 => .ofLabel (.param (.tail .head)) .nil
    | 2 => .ofLabel (.theta 0) (evalArgs ⟨0, rfl⟩ ⟨5, rfl⟩)
    | 3 => .ofLabel (.theta 0) (evalArgs ⟨1, rfl⟩ ⟨3, rfl⟩)
    | 4 => .ofLabel (.op .one) .nil
    | 5 => .ofLabel (.op .sub) (evalArgs ⟨2, rfl⟩ ⟨4, rfl⟩)
    | 6 => .ofLabel (.op .aboveTwo) (.cons ⟨2, rfl⟩ .nil)
    | 7 => .ofLabel (.op .not) (.cons ⟨6, rfl⟩ .nil)
    | 8 => .ofLabel (.pass 0) (.cons ⟨7, rfl⟩ .nil)
    | 9 => .ofLabel (.eval 0) (evalArgs ⟨2, rfl⟩ ⟨8, rfl⟩)
    | 10 => .ofLabel (.eval 0) (evalArgs ⟨3, rfl⟩ ⟨8, rfl⟩)
    | 11 => .ofLabel (.pass 0) (.cons ⟨7, rfl⟩ .nil)
    | ⟨k + 12, bound⟩ => False.elim (by omega)
  roots := roots ⟨9, rfl⟩ ⟨10, rfl⟩ ⟨9, rfl⟩

private def bundleWiring (first second : Ref bundleSort .count) (i : Fin 12) :
    Tuple (Ref bundleSort) (bundleGraph.node i).inputs :=
  if atFirst : i = 9 then atFirst.symm ▸ evalArgs ⟨2, rfl⟩ first
  else if atSecond : i = 10 then atSecond.symm ▸ evalArgs ⟨3, rfl⟩ second
  else (bundleGraph.node i).args

private def bundleCandidate (first second : Ref bundleSort .count)
    (outputs : Tuple (Ref bundleSort) bundleResults) : Cost.Candidate bundleGraph :=
  Cost.Candidate.wire bundleGraph id (bundleWiring first second) outputs

private def passRows : EPEG.MatchingNodes bundleGraph 8 11 :=
  ⟨[.bool], .count, .pass 0, .cons ⟨7, rfl⟩ .nil, .cons ⟨7, rfl⟩ .nil, rfl, rfl, HEq.rfl, HEq.rfl⟩

private def bundleClasses : EPEG.Classes 12 := EPEG.Classes.discrete.merge 8 11
private def sharedPass := bundleCandidate ⟨8, rfl⟩ ⟨8, rfl⟩ bundleGraph.roots
private def otherPass := bundleCandidate ⟨11, rfl⟩ ⟨11, rfl⟩ bundleGraph.roots
private def splitPass := bundleCandidate ⟨8, rfl⟩ ⟨11, rfl⟩ bundleGraph.roots
private def swapped := bundleCandidate ⟨8, rfl⟩ ⟨8, rfl⟩ (roots ⟨10, rfl⟩ ⟨9, rfl⟩ ⟨9, rfl⟩)

-- The swap is well typed and independently revertible, but has the wrong
-- provenance at two ports. Split passes are in the same source class
-- and replay successfully, but are distinct addresses in the emitter.
#guard (PEG.Simple.Revert.While.Region.Bundle.extract swapped.graph).isSome
#guard !swapped.selection.check bundleClasses
#guard (swapped.checkLegal bundleClasses).isNone
#guard (splitPass.checkLegal bundleClasses).isSome
#guard (Cost.Bundle.check bundleClasses splitPass).isNone

private def bundleInput : Tuple model.Value bundleParams := .cons ⟨5⟩ (.cons ⟨17⟩ .nil)
private def returnedCounts (out : Tuple model.Value bundleResults) : List Nat :=
  [(out.get .head).down, (out.get (.tail .head)).down, (out.get (.tail (.tail .head))).down]

private def runBundle (pool : List (Cost.Candidate bundleGraph)) (fuel : Nat) :
    Option (Nat × List Nat) := do
  let a ← Cost.Bundle.select bundleClasses Cost.Candidate.primitiveRows pool
  let out ← a.reversion.runFuel model fuel bundleInput
  return (a.reversion.scalar.descriptor.pass.id.val, returnedCounts out)

#guard runBundle [swapped, splitPass, sharedPass, otherPass] 3 == some (8, [2, 17, 2])
#guard runBundle [otherPass, sharedPass] 3 == some (11, [2, 17, 2])
#guard runBundle [sharedPass] 2 == none

private theorem bundleWF : WellFounded bundleGraph.Demand :=
  bundleGraph.demandWellFounded_of_check
    (PEG.Simple.Revert.While.Region.Automatic.inferDemandRank bundleGraph) (by decide)

example (a : Cost.Bundle.Accepted bundleGraph bundleClasses) (idx : Index 1)
    (neg : ∀ b : Bool, model.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ran : Exec model a.output bundleInput (some (.cons ⟨2⟩ (.cons ⟨17⟩ (.cons ⟨2⟩ .nil))))) :
    bundleGraph.observe model (bundleGraph.denote model bundleInput bundleWF) idx =
      .cons (some ⟨2⟩) (.cons (some ⟨17⟩) (.cons (some ⟨2⟩) .nil)) :=
  let valid := passRows.merge_sound (bundleGraph.denote_solves model bundleInput bundleWF)
    EPEG.Classes.discrete_valid (by decide)
  Exists.elim (a.firstExit_of_exec bundleWF valid neg idx ran) (fun _ seen => seen.2.2)

private def zeroRow : EPEG.Saturation.Extension.Row bundleGraph :=
  ⟨[], .count, .op .zero, .nil⟩

private def sampleRow {n : Nat} {g : Graph Op bundleParams bundleResults n 1}
    (stream index : Ref g.sort .count) : EPEG.Saturation.Extension.Row g :=
  ⟨[.count, .count], .count, .eval 0, .cons stream (.cons index .nil)⟩

private def firstSite := sampleRow (g := zeroRow.append) (zeroRow.liftRef ⟨2, rfl⟩) zeroRow.fresh

private def secondSite := sampleRow (g := firstSite.append)
  (firstSite.liftRef (zeroRow.liftRef ⟨3, rfl⟩)) (firstSite.liftRef zeroRow.fresh)

-- A dead eval uses the first zero sample as its index. The emitter still
-- reads the three original shared-pass roots.
private def sampleConsumer := sampleRow (g := secondSite.append)
  (secondSite.liftRef (firstSite.liftRef (zeroRow.liftRef ⟨3, rfl⟩)))
  (secondSite.liftRef firstSite.fresh)

open EPEG.Saturation EPEG.Saturation.Extension in
private def receiptSource : Extension.Output Op bundleParams bundleResults 1 :=
  ⟨16, ⟨sampleConsumer.append, EPEG.Classes.discrete⟩⟩

private def evalArgsWithIndex {n : Nat} {sort : Fin n → Ty Unit} {t : Ty Unit}
    (rhs : Ref sort .count) :
    (row : Node Op bundleParams (Fin 1) sort t) → Tuple (Ref sort) row.inputs
  | ⟨_, .eval _, .cons stream (.cons _ .nil)⟩ => .cons stream (.cons rhs .nil)
  | row => row.args

open EPEG.Saturation.Extension in
private def runAfterReplay (fuel : Nat) :
    Option (Dedup.Worklist.Stop × List Nat × Nat × Bool × List Nat) := do
  let report := (Dedup.Worklist.run Op.zero fuel receiptSource).report
  let receipt ← Cost.Bundle.Worklist.check Op.zero fuel receiptSource report
  let graph := receipt.endpoint.2.graph
  let rhs ← Ref.check graph.sort .count 16
  let candidate := Cost.Candidate.wire graph id
    (fun i => if i.val = 15 then evalArgsWithIndex rhs (graph.node i) else (graph.node i).args)
    graph.roots
  let chosen ← receipt.select Cost.Candidate.primitiveRows [candidate]
  let out ← chosen.reversion.runFuel model 3 bundleInput
  -- The same table with singleton classes cannot justify the redirected index.
  let needsMerge := (Cost.Bundle.check EPEG.Classes.discrete candidate).isNone
  return (receipt.report.stop, receipt.report.sites, receipt.endpoint.1, needsMerge, returnedCounts out)

#guard runAfterReplay 1 == some (.exhausted, [13], 17, true, [2, 17, 2])
#guard runAfterReplay 2 == some (.fixed, [13, 14], 18, true, [2, 17, 2])
#guard (Cost.Bundle.Worklist.check Op.zero 1 receiptSource ⟨[13], .fixed⟩).isNone

private theorem receiptSourceWF : WellFounded receiptSource.2.graph.Demand :=
  sampleConsumer.demandWellFounded
    (secondSite.demandWellFounded (firstSite.demandWellFounded (zeroRow.demandWellFounded bundleWF)))

example {fuel : Nat} (receipt : Cost.Bundle.Worklist.CheckedReceipt Op.zero fuel receiptSource)
    (a : Cost.Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) (idx : Index 1)
    (neg : ∀ b : Bool, model.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ran : a.reversion.runFuel model 3 bundleInput = some (.cons ⟨2⟩ (.cons ⟨17⟩ (.cons ⟨2⟩ .nil)))) :
    receiptSource.2.graph.observe model (receiptSource.2.graph.denote model bundleInput receiptSourceWF) idx =
      .cons (some ⟨2⟩) (.cons (some ⟨17⟩) (.cons (some ⟨2⟩) .nil)) :=
  receipt.observe_of_exec a receiptSourceWF EPEG.Classes.discrete_valid rfl neg idx
    (a.reversion.runFuel_exec 3 ran)

-- Use both occurrences of one in the live decrement, so the candidate
-- can share the binding or give the second occurrence its own row.
private def doubleStep : Graph Op bundleParams bundleResults 12 1 :=
  { bundleGraph with
    node := fun i =>
      if step : i = 5 then
        step.symm ▸ (Node.ofLabel (.op .subTwice) (.cons ⟨2, rfl⟩ (.cons ⟨4, rfl⟩ (.cons ⟨4, rfl⟩ .nil))) :
          Node Op bundleParams (Fin 1) bundleSort (bundleSort 5))
      else bundleGraph.node i }

open EPEG.Saturation.Extension in
private def taggedZero : Row doubleStep := ⟨[], .count, .op .zero, .nil⟩

private def taggedSample := sampleRow (g := taggedZero.append) (taggedZero.liftRef ⟨2, rfl⟩) taggedZero.fresh

open EPEG.Saturation.Extension in
private def taggedScale : Row taggedSample.append :=
  ⟨[.count, .count], .count, .op .sub,
    .cons (taggedSample.liftRef (taggedZero.liftRef ⟨4, rfl⟩)) (.cons taggedSample.fresh .nil)⟩

private def taggedZeroUser := sampleRow (g := taggedScale.append)
  (taggedScale.liftRef (taggedSample.liftRef (taggedZero.liftRef ⟨3, rfl⟩)))
  (taggedScale.liftRef taggedSample.fresh)

private def taggedScaleUser := sampleRow (g := taggedZeroUser.append)
  (taggedZeroUser.liftRef (taggedScale.liftRef (taggedSample.liftRef (taggedZero.liftRef ⟨3, rfl⟩))))
  (taggedZeroUser.liftRef taggedScale.fresh)

open EPEG.Saturation.Extension in
private def taggedSource : Output Op bundleParams bundleResults 1 :=
  ⟨17, ⟨taggedScaleUser.append, EPEG.Classes.discrete⟩⟩

open EPEG.Saturation.Extension in
private def taggedOps : Worklist.Combined.Ops Op := ⟨.zero, .one, .sub⟩

open EPEG.Saturation.Extension in
private def taggedDriver := Worklist.Combined.driver (params := bundleParams)
  (results := bundleResults) (l := 1) taggedOps

-- Remove the old zero sample and the old scaling row from the layout.
-- The duplicate layout adds a second representative for the constant
-- and lets the generator vary the live update's last operand.
private def taggedLayout {n : Nat} (g : Graph Op bundleParams bundleResults n 1) (duplicate : Bool) :
    Option (Cost.Bundle.Worklist.Generate.Skeleton g) := do
  let neutral ← Ref.check g.sort .count 0
  let replacement ← Ref.check g.sort .count (if duplicate then 4 else 0)
  let rep (i : Fin n) := if i.val = 13 then neutral.id else if i.val = 14 then replacement.id else i
  if duplicate then
    let step ← Ref.check g.sort .count 5
    if slot : 2 < (g.node (rep step.id)).inputs.length then
      some ⟨n, rep, some ⟨step.id, ⟨2, slot⟩⟩⟩
    else none
  else some ⟨n, rep, none⟩

private def taggedInput : Tuple model.Value bundleParams := .cons ⟨8⟩ (.cons ⟨17⟩ .nil)

open EPEG.Saturation.Extension Cost.Bundle.Worklist in
private def runGeneratedSelection :
    Option (List Worklist.Combined.Action × Worklist.Stop × List Nat × Nat × (Nat × Nat) × Bool × List Nat) := do
  let report := (taggedDriver.run 2 taggedSource).report
  let receipt ← Cost.Bundle.Worklist.Combined.check taggedOps 2 taggedSource report
  let graph := receipt.endpoint.2.graph
  let duplicate ← taggedLayout graph true
  let shared ← taggedLayout graph false
  let layouts := [duplicate, shared]
  let pool := Generate.pool receipt.endpoint.2.classes layouts
  let liveDuplicate ← pool[1]?
  let slower ← receipt.select Cost.Candidate.primitiveRows [liveDuplicate]
  let chosen ← Generate.select receipt Cost.Candidate.primitiveRows layouts
  let slowOrder ← PEG.Simple.Revert.While.Region.sliceOrder
    (PEG.Simple.Revert.While.Region.Bundle.scalarView slower.candidate.graph)
    slower.reversion.scalar.descriptor slower.reversion.scalar.descriptor.next
  let order ← PEG.Simple.Revert.While.Region.sliceOrder
    (PEG.Simple.Revert.While.Region.Bundle.scalarView chosen.candidate.graph)
    chosen.reversion.scalar.descriptor chosen.reversion.scalar.descriptor.next
  let out ← chosen.reversion.runFuel model 3 taggedInput
  let zeroSite ← Ref.check graph.sort .count 13
  let zeroRhs ← Ref.check graph.sort .count 17
  let onlyZero := EPEG.Classes.discrete.merge zeroSite.id zeroRhs.id
  let missingScale := (Generate.pool onlyZero layouts).isEmpty
  return (receipt.report.sites, receipt.report.stop, pool.map Cost.Candidate.primitiveRows,
    chosen.candidate.primitiveRows, (slowOrder.length, order.length), missingScale, returnedCounts out)

#guard (taggedDriver.run 2 taggedSource).state.1 == 20
#guard runGeneratedSelection == some ([.zeroSample 13, .evalScale 14], .fixed, [7, 7, 6], 6, (3, 2), true, [2, 17, 2])
#guard (Cost.Bundle.Worklist.Combined.check taggedOps 1 taggedSource ⟨[.zeroSample 13], .exhausted⟩).isSome
#guard (Cost.Bundle.Worklist.Combined.check taggedOps 1 taggedSource ⟨[.zeroSample 13], .fixed⟩).isNone

open EPEG.Saturation.Extension in
private def multiSource (joinPasses : Bool) : Output Op bundleParams bundleResults 1 :=
  ⟨12, ⟨bundleGraph, if joinPasses then bundleClasses else EPEG.Classes.discrete⟩⟩

-- Put both output evals after the two candidate pass rows. A choice is
-- made for each eval's pass edge, and both must use the same pass address.
private def multiLayout {n : Nat} (g : Graph Op bundleParams bundleResults n 1) :
    Option (Cost.Bundle.Worklist.Generate.Multi.Layout g) := do
  let firstEval ← Ref.check g.sort .count 9
  let secondEval ← Ref.check g.sort .count 10
  let alternatePass ← Ref.check g.sort .count 11
  let rep (i : Fin n) := if i = firstEval.id then alternatePass.id
    else if i = alternatePass.id then firstEval.id else i
  if first : 1 < (g.node (rep alternatePass.id)).inputs.length then
    if second : 1 < (g.node (rep secondEval.id)).inputs.length then
      some ⟨n, rep, [⟨alternatePass.id, ⟨1, first⟩⟩, ⟨secondEval.id, ⟨1, second⟩⟩]⟩
    else none
  else none

-- The test objective charges the pass edge span at each ordered result port.
private def passSpan {n : Nat} {g : Graph Op bundleParams bundleResults n 1} (c : Cost.Candidate g) : Nat :=
  let span (r : Ref c.graph.sort .count) :=
    match c.graph.node r.id with
    | ⟨_, .eval _, .cons _ (.cons pass .nil)⟩ => r.id.val - pass.id.val + (pass.id.val - r.id.val)
    | _ => 0
  span (c.graph.roots.get .head) + span (c.graph.roots.get (.tail .head)) +
    span (c.graph.roots.get (.tail (.tail .head)))

open EPEG.Saturation.Extension Cost.Bundle.Worklist in
private def runMulti (joinPasses : Bool) : Option (List (Option Nat) × Nat × Nat × List Nat) := do
  let receipt ← Combined.check taggedOps 0 (multiSource joinPasses) ⟨[], .fixed⟩
  let layout ← multiLayout receipt.endpoint.2.graph
  let pool := Generate.Multi.pool receipt.endpoint.2.classes [layout]
  let admitted := pool.map fun c => (Cost.Bundle.check receipt.endpoint.2.classes c).map fun _ => passSpan c
  let chosen ← Generate.Multi.select receipt passSpan [layout]
  let out ← chosen.reversion.runFuel model 3 bundleInput
  return (admitted, passSpan chosen.candidate, chosen.reversion.scalar.descriptor.pass.id.val, returnedCounts out)

-- Either single change splits the passes and fails admission. Changing
-- both makes the nearer pass usable, and the ordered result is unchanged.
#guard runMulti true == some ([some 8, none, none, some 5], 5, 9, [2, 17, 2])
#guard runMulti false == some ([some 8], 8, 8, [2, 17, 2])

example (receipt : Cost.Bundle.Worklist.Combined.CheckedReceipt taggedOps 0 (multiSource true))
    (chosen : Cost.Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) (idx : Index 1)
    (neg : ∀ b : Bool, model.run chosen.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ran : chosen.reversion.runFuel model 3 bundleInput = some (.cons ⟨2⟩ (.cons ⟨17⟩ (.cons ⟨2⟩ .nil)))) :
    bundleGraph.observe model (bundleGraph.denote model bundleInput bundleWF) idx =
      .cons (some ⟨2⟩) (.cons (some ⟨17⟩) (.cons (some ⟨2⟩) .nil)) :=
  let valid := passRows.merge_sound (bundleGraph.denote_solves model bundleInput bundleWF)
    EPEG.Classes.discrete_valid (by decide)
  receipt.observe_of_exec chosen bundleWF valid rfl ⟨⟨1⟩, rfl, fun _ => rfl⟩ neg idx
    (chosen.reversion.runFuel_exec 3 ran)

private theorem doubleStepWF : WellFounded doubleStep.Demand :=
  doubleStep.demandWellFounded_of_check (PEG.Simple.Revert.While.Region.Automatic.inferDemandRank doubleStep)
    (by decide)

private theorem taggedSourceWF : WellFounded taggedSource.2.graph.Demand :=
  taggedScaleUser.demandWellFounded (taggedZeroUser.demandWellFounded
    (taggedScale.demandWellFounded (taggedSample.demandWellFounded (taggedZero.demandWellFounded doubleStepWF))))

example {fuel : Nat} (receipt : Cost.Bundle.Worklist.Combined.CheckedReceipt taggedOps fuel taggedSource)
    (a : Cost.Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) (idx : Index 1)
    (neg : ∀ b : Bool, model.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ran : a.reversion.runFuel model 3 taggedInput = some (.cons ⟨2⟩ (.cons ⟨17⟩ (.cons ⟨2⟩ .nil)))) :
    taggedSource.2.graph.observe model (taggedSource.2.graph.denote model taggedInput taggedSourceWF) idx =
      .cons (some ⟨2⟩) (.cons (some ⟨17⟩) (.cons (some ⟨2⟩) .nil)) :=
  receipt.observe_of_exec a taggedSourceWF EPEG.Classes.discrete_valid rfl ⟨⟨1⟩, rfl, fun _ => rfl⟩ neg idx
    (a.reversion.runFuel_exec 3 ran)

open EPEG.Saturation.Extension in
private def inferenceSource : Output Op bundleParams bundleResults 1 :=
  ⟨14, ⟨taggedSample.append, EPEG.Classes.discrete⟩⟩

open EPEG.Saturation.Extension Cost.Bundle.Worklist.Generate in
private def runInferred : Option (List Nat × List Nat × List (Option (Nat × Nat)) × Nat × List Nat) := do
  let report := (Dedup.Worklist.run Op.zero 1 inferenceSource).report
  let receipt ← Cost.Bundle.Worklist.check Op.zero 1 inferenceSource report
  let layouts := Infer.layouts receipt.endpoint.2.graph
  let pool := Multi.pool receipt.endpoint.2.classes layouts
  let admitted := pool.map fun c => do
    let a ← Cost.Bundle.check receipt.endpoint.2.classes c
    let out ← a.reversion.runFuel model 3 taggedInput
    if returnedCounts out = [2, 17, 2] then
      some (c.primitiveRows, (Infer.scheduledRows a.reversion.scalar.update).length)
    else none
  let chosen ← Infer.select receipt Cost.Candidate.primitiveRows
  let out ← chosen.reversion.runFuel model 3 taggedInput
  return (receipt.report.sites, layouts.map Multi.Layout.size, admitted,
    chosen.candidate.primitiveRows, returnedCounts out)

-- Read the repeated occurrence in the checked live update. The copied
-- layout includes a wiring with both constant computations live.
#guard runInferred == some ([13], [11, 12], [some (4, 2), some (5, 2), some (5, 3)], 4, [2, 17, 2])
#guard (Cost.Bundle.Worklist.Generate.Infer.layouts splitPass.graph).isEmpty

private theorem inferenceSourceWF : WellFounded inferenceSource.2.graph.Demand :=
  taggedSample.demandWellFounded (taggedZero.demandWellFounded doubleStepWF)

example (receipt : Cost.Bundle.Worklist.CheckedReceipt Op.zero 1 inferenceSource)
    (chosen : Cost.Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) (idx : Index 1)
    (neg : ∀ b : Bool, model.run chosen.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ran : chosen.reversion.runFuel model 3 taggedInput = some (.cons ⟨2⟩ (.cons ⟨17⟩ (.cons ⟨2⟩ .nil)))) :
    inferenceSource.2.graph.observe model (inferenceSource.2.graph.denote model taggedInput inferenceSourceWF) idx =
      .cons (some ⟨2⟩) (.cons (some ⟨17⟩) (.cons (some ⟨2⟩) .nil)) :=
  receipt.observe_of_exec chosen inferenceSourceWF EPEG.Classes.discrete_valid rfl neg idx
    (chosen.reversion.runFuel_exec 3 ran)

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Tests

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source.Tests

open PEG PEG.Simple
open PEG.Simple.Revert.While
open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | sub : Op [.count, .count] .count
  | aboveTwo : Op [.count] .bool
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .sub, .cons n (.cons k .nil) => some ⟨n.down - k.down⟩
    | .aboveTwo, .cons n .nil => some ⟨decide (n.down > 2)⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private abbrev slots : List (Ty Unit) := [.count, .count]

private def store (n step : Nat) : Tuple model.Value slots :=
  .cons ⟨n⟩ (.cons ⟨step⟩ .nil)

-- Step is a real input and is used by the live subtraction. The
-- source projection passes it through unchanged when requested.
private def program (keepStep : Bool) : WhileProgram Op slots .count where
  guard := .op .aboveTwo (.cons (.var .head) .nil)
  body :=
    .seq (.assign (.op .sub (.cons (.var .head) (.cons (.var (.tail .head)) .nil))))
      (.project (.cons .head (.cons (if keepStep then .tail (.tail .head) else .head) .nil)))
  retvar := .head

private def run : Option (Nat × List Nat × List Nat × Nat) := do
  let a ← (Source.optimize (program true) .not).toOption
  let rewrite := a.cyclic.rewrite
  let source := (program true).translate .not
  let target := rewrite.matched.extract
  let value ← a.cyclic.reversion.runFuel model 3 (store 8 2)
  return (rewrite.site.val, refNumbers (source.node ⟨3, by decide⟩).args,
    refNumbers (target.node ⟨3, by decide⟩).args, value.down)

-- The compiled step θ is removed. The decrement now reads its
-- parameter at row 7 while the counting recurrence stays live.
/-- info: some (6, [5, 6], [5, 7], 2) -/
#guard_msgs in
#eval run

-- When the selected return is the eliminated slot, eval still
-- samples the parameter at the same loop's first pass.
/-- info: some 3 -/
#guard_msgs in
#eval
  let p : WhileProgram Op slots .count := { program true with retvar := .tail .head }
  ((Source.optimize p .not).toOption.bind fun a =>
    a.cyclic.reversion.runFuel model 2 (store 8 3)).map ULift.down

#guard
  match Source.optimize (program false) .not with
  | .error reason => reason == .noCheckedRewrite
  | .ok _ => false

-- A well-typed next value from the other slot cannot be presented
-- as the eliminated slot's invariant update.
#guard
  match Source.optimize (program true) .not with
  | .error _ => false
  | .ok a =>
    let d := a.cyclic.reversion.descriptor
    let bad := { d with next := .cons (d.next.get .head) (.cons (d.theta.get .head) .nil) }
    (Region.checkScheduledWith a.cyclic.rewrite.matched.extract bad a.cyclic.rewrite.targetRank true).isNone

private theorem sourceReturns : (program true).source.Returns model (store 8 2) ⟨2⟩ := by
  have step (n : Nat) : Exec model (program true).body.enableWhile (store n 2)
      (some (store (n - 2) 2)) :=
    (program true).body.runLoopFree_enableWhile (store n 2)
  exact ⟨store 2 2, .whileStep (next := store 6 2) rfl (step 8)
    (.whileStep (next := store 4 2) rfl (step 6)
      (.whileStep (next := store 2 2) rfl (step 4) (.whileStop rfl))), rfl⟩

private theorem primitiveTotal : {args : List (Ty Unit)} → {t : Ty Unit} →
    (op : Op args t) → (input : Tuple model.Value args) → ∃ out, model.run op input = some out
  | _, _, .sub, .cons _ (.cons _ .nil) => ⟨_, rfl⟩
  | _, _, .aboveTwo, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .not, .cons _ .nil => ⟨_, rfl⟩

private theorem readsTotal {n : Nat} {sort : Fin n → Ty Unit} {vars args : List (Ty Unit)}
    {scope : Tuple (Ref sort) vars} {refs : Tuple (Ref sort) args}
    (reads : Region.Reads scope refs) (input : Tuple model.Value vars) :
    ∃ out, reads.args.eval model input = some out := by
  induction reads with
  | nil => exact ⟨.nil, rfl⟩
  | cons p _ _ ih =>
    obtain ⟨tail, evaluated⟩ := ih
    exact ⟨.cons (input.get p) tail, by simp [Region.Reads.args, Args.eval, Expr.evalLift, evaluated]⟩

private theorem scheduleTotal {n : Nat} {g : Graph Op slots [.count] n 1}
    {outs vars : List (Ty Unit)} {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Region.Schedule g false roots scope) (input : Tuple model.Value vars) :
    ∃ out, schedule.lower.runLoopFree model input = some out := by
  induction schedule with
  | done _ => exact ⟨_, rfl⟩
  | bind _ op _ _ _ reads _ ih =>
    obtain ⟨args, argsEval⟩ := readsTotal reads input
    obtain ⟨value, opEval⟩ := primitiveTotal op args
    obtain ⟨out, bodyEval⟩ := ih (.cons value input)
    exact ⟨out, by simp [Region.Schedule.lower, Stmt.runLoopFree, Expr.eval, Expr.evalLift,
      argsEval, opEval, bodyEval]⟩
  | branch enabled => nomatch enabled

example (a : Source.Accepted (program true) Op.not) : a.output.Returns model (store 8 2) ⟨2⟩ :=
  a.returns model (store 8 2) ⟨scheduleTotal a.cyclic.reversion.guard,
    scheduleTotal a.cyclic.reversion.update⟩ (fun _ => rfl) sourceReturns

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source.Tests
