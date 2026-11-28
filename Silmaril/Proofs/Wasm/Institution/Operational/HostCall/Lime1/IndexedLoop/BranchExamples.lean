module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.BranchExamples

open Execution.Runtime (Frame MemInst Value)
open Wasm.Lime1.Execution
open Continuation (IfType Label Op)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def outerType : Wasm.Lime1.FuncType := ⟨[], [num64, num32]⟩
private def outerIf : IfType := .indexed ⟨1⟩ outerType
private def innerIf : IfType := .scalar num32
private def prepare : Site Nat := ⟨⟨2⟩, ⟨[num64], [num64, num32]⟩, 11⟩
private def choose : Site Nat := ⟨⟨3⟩, ⟨[num64], [num32, num64, num32, num32]⟩, 12⟩
private def innerJoin : Site Nat := ⟨⟨4⟩, ⟨[num32, num64, num32], [num32]⟩, 13⟩
private def outerJoin : Site Nat := ⟨⟨5⟩, ⟨outerType.results, outerType.results⟩, 14⟩
private def finalJoin : Site Nat := ⟨⟨6⟩, ⟨[num64, num64, num32], [num32]⟩, 15⟩

private def innerTail : List (Op Nat) := [.call ⟨3⟩ innerJoin]
private def branch : List (Op Nat) := .brIf ⟨1⟩ :: innerTail
private def innerArm : List (Op Nat) := .get ⟨0⟩ :: .call ⟨2⟩ choose :: branch
private def outerTail : List (Op Nat) := [.call ⟨4⟩ outerJoin]
private def innerControl : List (Op Nat) := .if_ innerIf innerArm innerArm :: outerTail
private def outerArm : List (Op Nat) := .get ⟨0⟩ :: .call ⟨1⟩ prepare :: innerControl
private def finalTail : List (Op Nat) := [.call ⟨5⟩ finalJoin]
private def outerLabel : Label Nat := ⟨outerIf, [i64 42], finalTail, none⟩
private def innerLabel : Label Nat := ⟨innerIf, [i64 55], outerTail, none⟩

private def program : Program Nat where
  module := {
    types := [signature, outerType]
    funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ outerIf outerArm outerArm :: finalTail
  saved := 42

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm program.functionType program.module program.function, .host producerType 10,
      .host prepare.type prepare.code, .host choose.type choose.code, .host innerJoin.type innerJoin.code,
      .host outerJoin.type outerJoin.code, .host finalJoin.type finalJoin.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl, .fixed⟩
private def caller : Frame := ⟨[i32 9], {funcs := [⟨0⟩]}⟩

private abbrev Check := Continuation.Checked base program.module [num64]
private abbrev outerTargets := [outerType.results, [num32]]
private abbrev innerTargets := [innerIf.signature.results, outerType.results, [num32]]

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have inside : Check innerTargets [num32] [] innerArm :=
    .get (type := num64) (stack := []) rfl
      (.call (site := choose) (saved := []) rfl rfl
        (.brIf (scratch := [num32]) (payload := [num64, num32]) rfl
          (.call (site := innerJoin) (saved := []) rfl rfl .nil)))
  have innerControlChecked : Check outerTargets [num64, num32] [num64, num32] innerControl :=
    .if_ (type := innerIf) (saved := [num64]) rfl inside inside
      (.call (site := outerJoin) (saved := []) rfl rfl .nil)
  have outside : Check outerTargets [num64, num32] [] outerArm :=
    .get (type := num64) (stack := []) rfl (.call (site := prepare) (saved := []) rfl rfl innerControlChecked)
  have final : Check [[num32]] [num32] [num64, num64, num32] finalTail :=
    .call (site := finalJoin) (saved := []) rfl rfl .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl, .if_ (type := outerIf) (saved := [num64]) rfl outside outside final, rfl, rfl⟩

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 1)) (.values [i32 1, i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 2)) (.values [i64 55, i32 1])
  | 12 => store = memory.store (bytes 2) ∧ args = [i64 7] ∧ ∃ guard : BitVec 32,
      outcome = .returned (memory.store (bytes 3)) (.values [i32 99, i64 77, i32 22, i32 guard])
  | 13 => store = memory.store (bytes 3) ∧ args = [i32 99, i64 77, i32 22] ∧
      outcome = .returned (memory.store (bytes 4)) (.values [i32 44])
  | 14 => store = memory.store (bytes 4) ∧ args = [i64 55, i32 44] ∧
      outcome = .returned (memory.store (bytes 5)) (.values [i64 66, i32 33])
  | 15 => (store = memory.store (bytes 3) ∧ args = [i64 42, i64 77, i32 22] ∧
      outcome = .returned (memory.store (bytes 6)) (.values [i32 101])) ∨
      (store = memory.store (bytes 5) ∧ args = [i64 42, i64 66, i32 33] ∧
      outcome = .returned (memory.store (bytes 7)) (.values [i32 102]))
  | _ => False

private theorem contract : program.Contract memory host := by
  have chooseContract : choose.Contract memory host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, guard, eq⟩ := answer
    cases eq
    exact ⟨bytes 3, rfl, rfl, rfl⟩
  have innerJoinContract : innerJoin.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 4, rfl, rfl, rfl⟩
  have outerJoinContract : outerJoin.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 5, rfl, rfl, rfl⟩
  have prepareContract : prepare.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 2, rfl, rfl, rfl⟩
  have finalContract : finalJoin.Contract memory host := by
    intro _ _ _ _ _ _ answer
    rcases answer with ⟨_, _, eq⟩ | ⟨_, _, eq⟩
    · cases eq
      exact ⟨bytes 6, rfl, rfl, rfl⟩
    · cases eq
      exact ⟨bytes 7, rfl, rfl, rfl⟩
  have inside : Continuation.Contract memory host innerArm :=
    .get (.call chooseContract (.brIf (.call innerJoinContract .nil)))
  have outside : Continuation.Contract memory host outerArm :=
    .get (.call prepareContract (.if_ inside inside (.call outerJoinContract .nil)))
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 1, rfl, rfl, rfl⟩
  · exact .if_ outside outside (.call finalContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) program.functionResults a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem atOuter : BodyPath ⟨bytes 1, .source [] outerArm, [outerLabel]⟩ := by
  have producer : Path ⟨bytes 0, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨bytes 1, .source [i64 42, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  exact (exit.step (.if_ (saved := [i64 42]) (args := []) (guard := 1) rfl)).step (.block rfl)

private theorem atBranch (guard : BitVec 32) : BodyPath
    ⟨bytes 3, .source [i32 99, i64 77, i32 22, i32 guard] branch, [innerLabel, outerLabel]⟩ := by
  have preparing : BodyPath ⟨bytes 1, .invoke [] prepare [i64 7] innerControl, [outerLabel]⟩ :=
    (atOuter.step (.get rfl)).step (.resolve (saved := []) (args := [i64 7]) rfl)
  have prepared : BodyPath ⟨bytes 2, .source [i64 55, i32 1] innerControl, [outerLabel]⟩ :=
    preparing.step (.returned (vs := [i64 55, i32 1]) rfl rfl ⟨rfl, rfl, rfl⟩)
  have inner : BodyPath ⟨bytes 2, .source [] innerArm, [innerLabel, outerLabel]⟩ :=
    (prepared.step (.if_ (saved := [i64 55]) (args := []) (guard := 1) rfl)).step (.block rfl)
  have choosing : BodyPath ⟨bytes 2, .invoke [] choose [i64 7] branch, [innerLabel, outerLabel]⟩ :=
    (inner.step (.get rfl)).step (.resolve (saved := []) (args := [i64 7]) rfl)
  exact choosing.step (.returned (vs := [i32 99, i64 77, i32 22, i32 guard]) rfl rfl ⟨rfl, rfl, guard, rfl⟩)

private theorem taken : BodyPath ⟨bytes 3, .branch [i32 99, i64 77, i32 22] ⟨1⟩ innerTail,
    [innerLabel, outerLabel]⟩ :=
  (atBranch 1).step (.brIf (stack := [i32 99, i64 77, i32 22]) (guard := 1))

private theorem lowered : BodyPath ⟨bytes 3, .branch [i64 55, i32 99, i64 77, i32 22] ⟨0⟩ outerTail,
    [outerLabel]⟩ :=
  taken.step (.branchLower (by decide))

private theorem delivered : BodyPath ⟨bytes 3, .source [i64 42, i64 77, i32 22] finalTail, []⟩ :=
  lowered.step (.branchDeliver (scratch := [i64 55, i32 99]) (payload := [i64 77, i32 22]) rfl rfl rfl)

-- Selection consumes only the test. The first transfer skips the inner host,
-- lowers the depth, and exposes the outer host while retaining scratch values.
example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 2 [] [value (i64 55),
      .label 1 [] [value (i32 99), value (i64 77), value (i32 22), .source (.br ⟨1⟩), .source (.call ⟨3⟩)],
      .source (.call ⟨4⟩)], .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, taken, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 2 [] [value (i64 55), value (i32 99), value (i64 77), value (i32 22),
      .source (.br ⟨0⟩), .source (.call ⟨4⟩)], .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, lowered, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), value (i64 77), value (i32 22), .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, delivered, rfl, rfl⟩

private theorem fellThrough : BodyPath ⟨bytes 5, .source [i64 42, i64 66, i32 33] finalTail, []⟩ := by
  have inside : BodyPath ⟨bytes 3, .source [i32 99, i64 77, i32 22] innerTail, [innerLabel, outerLabel]⟩ :=
    (atBranch 0).step (.brIf (stack := [i32 99, i64 77, i32 22]) (guard := 0))
  have first : BodyPath ⟨bytes 3, .invoke [] innerJoin [i32 99, i64 77, i32 22] [], [innerLabel, outerLabel]⟩ :=
    inside.step (.resolve (saved := []) (args := [i32 99, i64 77, i32 22]) rfl)
  have firstResult : BodyPath ⟨bytes 4, .source [i32 44] [], [innerLabel, outerLabel]⟩ :=
    first.step (.returned (vs := [i32 44]) rfl rfl ⟨rfl, rfl, rfl⟩)
  have outside : BodyPath ⟨bytes 4, .source [i64 55, i32 44] outerTail, [outerLabel]⟩ :=
    firstResult.step .armResult
  have second : BodyPath ⟨bytes 4, .invoke [] outerJoin [i64 55, i32 44] [], [outerLabel]⟩ :=
    outside.step (.resolve (saved := []) (args := [i64 55, i32 44]) rfl)
  have secondResult : BodyPath ⟨bytes 5, .source [i64 66, i32 33] [], [outerLabel]⟩ :=
    second.step (.returned (vs := [i64 66, i32 33]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact secondResult.step .armResult

private theorem finish {live next : ByteArray} {wide : BitVec 64} {small out : BitVec 32}
    (path : BodyPath ⟨live, .source [i64 42, i64 wide, i32 small] finalTail, []⟩)
    (nextLive : memory.Live next) (answer : host 15 (memory.store live) [i64 42, i64 wide, i32 small]
      (.returned (memory.store next) (.values [i32 out]))) :
    Steps host launch ⟨memory.store next, caller, values [i32 out]⟩ := by
  have pending : BodyPath ⟨live, .invoke [] finalJoin [i64 42, i64 wide, i32 small] [], []⟩ :=
    path.step (.resolve (saved := []) (args := [i64 42, i64 wide, i32 small]) rfl)
  have returned : BodyPath ⟨next, .source [i32 out] [], []⟩ :=
    pending.step (.returned (vs := [i32 out]) nextLive rfl answer)
  exact (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, (returned.step .labelResult).step .frameDone, nextLive, rfl⟩

example : Steps host launch ⟨memory.store (bytes 6), caller, values [i32 101]⟩ :=
  finish delivered rfl (.inl ⟨rfl, rfl, rfl⟩)

example : Steps host launch ⟨memory.store (bytes 7), caller, values [i32 102]⟩ :=
  finish fellThrough rfl (.inr ⟨rfl, rfl, rfl⟩)

-- Depth three is outside both explicit labels and the implicit function label.
example : ¬ Check innerTargets [num32] [num32, num64, num32, num32] (.brIf ⟨3⟩ :: innerTail) := by
  intro checked
  generalize ([num32, num64, num32, num32] : List NumType) = stack at checked
  cases checked with
  | brIf target _ => cases target

-- Taking the edge requires the target's i64/i32 suffix even if a zero test
-- could continue with the same reversed pair.
example : ¬ Check innerTargets [num32] [num32, num64, num32] [.brIf ⟨1⟩, .drop] := by
  intro checked
  generalize input : ([num32, num64, num32] : List NumType) = stack at checked
  cases checked with
  | brIf target _ =>
    change some [num64, num32] = some _ at target
    cases target
    change [num32, num64] ++ [num32] = (_ ++ [num64, num32]) ++ [num32] at input
    have bad := congrArg List.getLast? (List.append_cancel_right input)
    simp [num32, num64] at bad

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.BranchExamples
