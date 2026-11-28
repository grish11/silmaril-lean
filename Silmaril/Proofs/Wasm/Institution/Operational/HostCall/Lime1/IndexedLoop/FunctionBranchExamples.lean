module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.FunctionBranchExamples

open Execution.Runtime (Frame MemInst Value)
open Wasm.Lime1.Execution
open Continuation (IfType Label Op)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def rootResults : List NumType := [num32, num64]
private def innerType : Wasm.Lime1.FuncType := ⟨[num32, num32, num64, num32], [num32]⟩
private def innerIf : IfType := .indexed ⟨2⟩ innerType
private def prepare : Site Nat := ⟨⟨2⟩, ⟨[num64], [num64] ++ innerType.params ++ [num32]⟩, 11⟩
private def innerJoin : Site Nat := ⟨⟨3⟩, ⟨[num32, num32, num64], [num32]⟩, 12⟩
private def outerJoin : Site Nat := ⟨⟨4⟩, ⟨[num64, num32], [num32]⟩, 13⟩
private def finalJoin : Site Nat := ⟨⟨5⟩, ⟨[num64, num32], rootResults⟩, 14⟩
private def innerTail : List (Op Nat) := [.call ⟨2⟩ innerJoin]
private def directArm : List (Op Nat) := .drop :: .br ⟨2⟩ :: innerTail
private def conditionalArm : List (Op Nat) := .brIf ⟨2⟩ :: innerTail
private def outerTail : List (Op Nat) := [.call ⟨3⟩ outerJoin]
private def innerControl : List (Op Nat) := .if_ innerIf directArm conditionalArm :: outerTail
private def outerArm : List (Op Nat) := .get ⟨0⟩ :: .call ⟨1⟩ prepare :: innerControl
private def rootTail : List (Op Nat) := [.call ⟨4⟩ finalJoin]
private def outerLabel : Label Nat := ⟨.scalar num32, [i64 42], rootTail, none⟩
private def innerLabel : Label Nat := ⟨innerIf, [i64 55], outerTail, none⟩

private def program : Program Nat where
  module := {
    types := [signature, ⟨[num64], rootResults⟩, innerType]
    funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ (.scalar num32) outerArm outerArm :: rootTail
  saved := 42
  functionIndex := ⟨1⟩
  functionResults := rootResults

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm program.functionType program.module program.function,
      .host producerType 10, .host prepare.type prepare.code, .host innerJoin.type innerJoin.code,
      .host outerJoin.type outerJoin.code, .host finalJoin.type finalJoin.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl, .fixed⟩
private def caller : Frame := ⟨[i32 9], {funcs := [⟨0⟩]}⟩
private abbrev Check := Continuation.Checked base program.module [num64]
private abbrev innerTargets := [innerType.results, [num32], rootResults]
private abbrev outerTargets := [[num32], rootResults]

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have direct : Check innerTargets [num32] innerType.params directArm :=
    .drop (type := num32) (.br (scratch := [num32]) (payload := rootResults) rfl)
  have conditional : Check innerTargets [num32] innerType.params conditionalArm :=
    .brIf (scratch := [num32]) (payload := rootResults) rfl
      (.call (site := innerJoin) (saved := []) rfl rfl .nil)
  have inner : Check outerTargets [num32] ([num64] ++ innerType.params ++ [num32]) innerControl :=
    .if_ (type := innerIf) (saved := [num64]) rfl direct conditional
      (.call (site := outerJoin) (saved := []) rfl rfl .nil)
  have outside : Check outerTargets [num32] [] outerArm :=
    .get (type := num64) (stack := []) rfl (.call (site := prepare) (saved := []) rfl rfl inner)
  have final : Check [rootResults] rootResults [num64, num32] rootTail :=
    .call (site := finalJoin) (saved := []) rfl rfl .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl, .if_ (type := .scalar num32) (saved := [num64]) rfl outside outside final,
    rfl, rfl⟩

private def payload : List Value := [i32 22, i64 77]
private def carried : List Value := i32 99 :: payload

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 1)) (.values [i32 1, i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ args = [i64 7] ∧ ∃ guard arm : BitVec 32,
      outcome = .returned (memory.store (bytes 2)) (.values (i64 55 :: carried ++ [i32 guard, i32 arm]))
  | 12 => store = memory.store (bytes 2) ∧ args = carried ∧
      outcome = .returned (memory.store (bytes 3)) (.values [i32 44])
  | 13 => store = memory.store (bytes 3) ∧ args = [i64 55, i32 44] ∧
      outcome = .returned (memory.store (bytes 4)) (.values [i32 33])
  | 14 => store = memory.store (bytes 4) ∧ args = [i64 42, i32 33] ∧
      outcome = .returned (memory.store (bytes 5)) (.values [i32 66, i64 88])
  | _ => False

private theorem contract : program.Contract memory host := by
  have preparing : prepare.Contract memory host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, guard, arm, eq⟩ := answer
    cases eq
    exact ⟨bytes 2, rfl, rfl, rfl⟩
  have inner : innerJoin.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 3, rfl, rfl, rfl⟩
  have outside : outerJoin.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 4, rfl, rfl, rfl⟩
  have final : finalJoin.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 5, rfl, rfl, rfl⟩
  have arm : Continuation.Contract memory host outerArm :=
    .get (.call preparing (.if_ (.drop .br) (.brIf (.call inner .nil)) (.call outside .nil)))
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 1, rfl, rfl, rfl⟩
  · exact .if_ arm arm (.call final .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) rootResults a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem inOuter : BodyPath ⟨bytes 1, .source [] outerArm, [outerLabel]⟩ := by
  have producer : Path ⟨bytes 0, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨bytes 1, .source [i64 42, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  exact (exit.step (.if_ (saved := [i64 42]) (args := []) (guard := 1) rfl)).step (.block rfl)

private theorem inArm (guard : BitVec 32) (direct : Bool) :
    BodyPath ⟨bytes 2, .source (carried ++ [i32 guard]) (if direct then directArm else conditionalArm),
      [innerLabel, outerLabel]⟩ := by
  have pending : BodyPath ⟨bytes 1, .invoke [] prepare [i64 7] innerControl, [outerLabel]⟩ :=
    (inOuter.step (.get rfl)).step (.resolve (saved := []) (args := [i64 7]) rfl)
  let arm : BitVec 32 := if direct then 1 else 0
  have returned : BodyPath ⟨bytes 2, .source (([i64 55] ++ (carried ++ [i32 guard])) ++ [i32 arm])
      innerControl, [outerLabel]⟩ :=
    pending.step (.returned (vs := i64 55 :: carried ++ [i32 guard, i32 arm]) rfl rfl ⟨rfl, rfl, guard, arm, rfl⟩)
  cases direct
  · exact (returned.step (.if_ (saved := [i64 55]) (args := carried ++ [i32 guard]) (guard := 0) rfl)).step (.block rfl)
  · exact (returned.step (.if_ (saved := [i64 55]) (args := carried ++ [i32 guard]) (guard := 1) rfl)).step (.block rfl)

private theorem atDirect : BodyPath ⟨bytes 2, .branch carried ⟨2⟩ innerTail, [innerLabel, outerLabel]⟩ :=
  (inArm 0 true).step (.drop (stack := carried) (v := i32 0))

private theorem atConditional : BodyPath ⟨bytes 2, .branch carried ⟨2⟩ innerTail, [innerLabel, outerLabel]⟩ :=
  (inArm 1 false).step (.brIf (stack := carried) (guard := 1))

private theorem atFunction (path : BodyPath ⟨bytes 2, .branch carried ⟨2⟩ innerTail, [innerLabel, outerLabel]⟩) :
    BodyPath ⟨bytes 2, .branch ([i64 42, i64 55] ++ carried) ⟨0⟩ rootTail, []⟩ :=
  (path.step (.branchLower (by decide))).step (.branchLower (by decide))

private theorem functionExit
    (path : BodyPath ⟨bytes 2, .branch carried ⟨2⟩ innerTail, [innerLabel, outerLabel]⟩) :
    BodyPath ⟨bytes 2, .frameResult (.values payload), []⟩ :=
  (atFunction path).step (.functionBranch (scratch := [i64 42, i64 55, i32 99]) (payload := payload) rfl rfl)

-- Crossing the two explicit labels exposes a branch to the implicit label
-- with the function's arity, both saved prefixes, and the final skipped call.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 2 (program.active 7)
    [.label 2 [] [value (i64 42), value (i64 55), value (i32 99), value (i32 22), value (i64 77),
      .source (.br ⟨0⟩), .source (.call ⟨4⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, atFunction atDirect, rfl, rfl⟩

-- Label delivery and restoring the caller are separate native steps.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 2 (program.active 7) (values payload)]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, functionExit atDirect, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, values [i32 22, i64 77]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, (functionExit atDirect).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, values [i32 22, i64 77]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, (functionExit atConditional).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, values [i32 66, i64 88]⟩ := by
  have fallthrough : BodyPath ⟨bytes 2, .source carried innerTail, [innerLabel, outerLabel]⟩ :=
    (inArm 0 false).step (.brIf (stack := carried) (guard := 0))
  have innerCall : BodyPath ⟨bytes 2, .invoke [] innerJoin carried [], [innerLabel, outerLabel]⟩ :=
    fallthrough.step (.resolve (saved := []) (args := carried) rfl)
  have inner : BodyPath ⟨bytes 3, .source [i32 44] [], [innerLabel, outerLabel]⟩ :=
    innerCall.step (.returned (vs := [i32 44]) rfl rfl ⟨rfl, rfl, rfl⟩)
  have outerCall : BodyPath ⟨bytes 3, .invoke [] outerJoin [i64 55, i32 44] [], [outerLabel]⟩ :=
    (inner.step .armResult).step (.resolve (saved := []) (args := [i64 55, i32 44]) rfl)
  have outside : BodyPath ⟨bytes 4, .source [i32 33] [], [outerLabel]⟩ :=
    outerCall.step (.returned (vs := [i32 33]) rfl rfl ⟨rfl, rfl, rfl⟩)
  have rootCall : BodyPath ⟨bytes 4, .invoke [] finalJoin [i64 42, i32 33] [], []⟩ :=
    (outside.step .armResult).step (.resolve (saved := []) (args := [i64 42, i32 33]) rfl)
  have returned : BodyPath ⟨bytes 5, .source [i32 66, i64 88] [], []⟩ :=
    rootCall.step (.returned (vs := [i32 66, i64 88]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, (returned.step .labelResult).step .frameDone, rfl, rfl⟩

-- Supplying only the loop's i64 parameter cannot satisfy the function label.
example : ¬ Check innerTargets [num32] [num64] [.br ⟨2⟩] := by
  intro checked
  generalize input : ([num64] : List NumType) = stack at checked
  cases checked with
  | br target =>
    change some rootResults = some _ at target
    cases target
    have short := congrArg List.length input
    simp [rootResults] at short

example : ¬ Check innerTargets [num32] [num64, num32] [.br ⟨2⟩] := by
  intro checked
  generalize input : ([num64, num32] : List NumType) = stack at checked
  cases checked with
  | br target =>
    change some rootResults = some _ at target
    cases target
    have wrongOrder := congrArg List.getLast? input
    simp [rootResults, num32, num64] at wrongOrder

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.FunctionBranchExamples
