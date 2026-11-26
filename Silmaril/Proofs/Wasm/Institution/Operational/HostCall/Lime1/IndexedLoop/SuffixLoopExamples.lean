module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.SuffixLoopExamples

open Execution.Runtime (Frame MemInst Value)
open Wasm.Lime1.Execution
open Continuation (IfType Label Op)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def loopResults : List NumType := [num64, num32]
private def loopSignature : Wasm.Lime1.FuncType := ⟨[num64], loopResults⟩
private def armSignature : Wasm.Lime1.FuncType := ⟨loopResults ++ [num64, num32], loopResults⟩
private def loopType : IfType := .indexed ⟨1⟩ loopSignature
private def armType : IfType := .indexed ⟨2⟩ armSignature
private def iteration : Site Nat := ⟨⟨2⟩, ⟨[num64], [num64] ++ armSignature.params ++ [num32]⟩, 11⟩
private def complete : Site Nat := ⟨⟨3⟩, ⟨num64 :: loopResults, loopResults⟩, 12⟩
private def follow : Site Nat := ⟨⟨4⟩, ⟨num64 :: loopResults, [num32]⟩, 13⟩
private def arm : List (Op Nat) := [.brIf ⟨1⟩, .drop]
private def bodyTail : List (Op Nat) := [.call ⟨2⟩ complete]
private def afterIteration : List (Op Nat) := .if_ armType arm arm :: bodyTail
private def body : List (Op Nat) := .call ⟨1⟩ iteration :: afterIteration
private def afterLoop : List (Op Nat) := [.call ⟨3⟩ follow]
private def loopCode : List (Op Nat) := .loop loopType body :: afterLoop
private def loopInstr : Wasm.Lime1.Instr := Op.instr (.loop loopType body)
private def loopLabel : Label Nat := ⟨loopType, [i64 42], afterLoop, some body⟩
private def armLabel (saved : BitVec 64) : Label Nat := ⟨armType, [i64 saved], bodyTail, none⟩

private def program : Program Nat where
  module := {
    types := [signature, loopSignature, armSignature]
    funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .drop :: .get ⟨0⟩ :: loopCode
  saved := 42

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm program.functionType program.module program.function,
      .host producerType 10, .host iteration.type iteration.code, .host complete.type complete.code,
      .host follow.type follow.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl, .fixed⟩
private def caller : Frame := ⟨[i32 9], {funcs := [⟨0⟩]}⟩
private abbrev Check := Continuation.Checked base program.module [num64]
private abbrev rootResults := [num32]
private abbrev loopTargets := [[num64], rootResults]

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have armChecked : Check (loopResults :: loopTargets) loopResults armSignature.params arm :=
    .brIf (scratch := loopResults) (payload := [num64]) rfl (.drop (type := num64) .nil)
  have loopChecked : Check loopTargets loopResults [num64] body :=
    .call (site := iteration) (saved := []) rfl rfl
      (.if_ (type := armType) (saved := [num64]) rfl armChecked armChecked
        (.call (site := complete) (saved := []) rfl rfl .nil))
  have rootTail : Check [rootResults] rootResults (num64 :: loopResults) afterLoop :=
    .call (site := follow) (saved := []) rfl rfl .nil
  have loopEntry : Check [rootResults] rootResults [num64, num64] loopCode :=
    .loop (type := loopType) (saved := [num64]) rfl loopChecked rootTail
  have continuation : Check [rootResults] rootResults [num64, num32] program.continuation :=
    .drop (stack := [num64]) (type := num32) (.get (type := num64) rfl loopEntry)
  exact ⟨rfl, rfl, rfl, rfl, rfl, continuation, rfl, rfl⟩

private def armArgs (wide : BitVec 64) (narrow : BitVec 32) (next : BitVec 64) (test : BitVec 32) : List Value :=
  [i64 wide, i32 narrow, i64 next, i32 test]

private def iterationValues (saved wide : BitVec 64) (narrow : BitVec 32) (next : BitVec 64) (test : BitVec 32) :
    List Value :=
  ([i64 saved] ++ armArgs wide narrow next test) ++ [i32 1]

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 1)) (.values [i32 9, i64 88, i32 0])
  | 11 =>
      (store = memory.store (bytes 1) ∧ args = [i64 7] ∧ outcome =
        .returned (memory.store (bytes 2)) (.values (iterationValues 60 400 30 12 1))) ∨
      (store = memory.store (bytes 2) ∧ args = [i64 12] ∧
        (outcome = .returned (memory.store (bytes 3)) (.values (iterationValues 61 401 31 13 0)) ∨
         outcome = .returned (memory.store (bytes 6)) .trap))
  | 12 => store = memory.store (bytes 3) ∧ args = [i64 61, i64 401, i32 31] ∧
      outcome = .returned (memory.store (bytes 4)) (.values [i64 402, i32 32])
  | 13 => store = memory.store (bytes 4) ∧ args = [i64 42, i64 402, i32 32] ∧
      outcome = .returned (memory.store (bytes 5)) (.values [i32 99])
  | _ => False

private theorem contract : program.Contract memory host := by
  have iterationContract : iteration.Contract memory host := by
    intro _ _ _ _ _ _ answer
    rcases answer with ⟨_, _, eq⟩ | ⟨_, _, eq | eq⟩
    · cases eq
      exact ⟨bytes 2, rfl, rfl, rfl⟩
    · cases eq
      exact ⟨bytes 3, rfl, rfl, rfl⟩
    · cases eq
      exact ⟨bytes 6, rfl, rfl, trivial⟩
  have completeContract : complete.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 4, rfl, rfl, rfl⟩
  have followContract : follow.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 5, rfl, rfl, rfl⟩
  have armContract : Continuation.Contract memory host arm := .brIf (.drop .nil)
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 1, rfl, rfl, rfl⟩
  · exact .drop (.get (.loop (.call iterationContract (.if_ armContract armContract (.call completeContract .nil)))
      (.call followContract .nil)))

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) rootResults a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem atIteration {live : ByteArray} {input : BitVec 64}
    (pending : BodyPath ⟨live, .source [i64 42, i64 input] loopCode, []⟩) :
    BodyPath ⟨live, .invoke [] iteration [i64 input] afterIteration, [loopLabel]⟩ :=
  (pending.step (.loop (saved := [i64 42]) (args := [i64 input]) rfl)).step
    (.resolve (saved := []) (args := [i64 input]) rfl)

private theorem first : BodyPath ⟨bytes 1, .invoke [] iteration [i64 7] afterIteration, [loopLabel]⟩ := by
  have producer : Path ⟨bytes 0, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 9 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨bytes 1, .source [i64 42, i32 9] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 9 88 0))).tail
      (.control (.dropInput 9 88))).tail (.control (.loopResult 9))
  exact atIteration ((exit.step (.drop (stack := [i64 42]) (v := i32 9))).step (.get rfl))

private theorem inArm {live : ByteArray} {saved wide next : BitVec 64} {narrow test : BitVec 32}
    (returned : BodyPath ⟨live, .source (iterationValues saved wide narrow next test) afterIteration, [loopLabel]⟩) :
    BodyPath ⟨live, .source (armArgs wide narrow next test) arm, [armLabel saved, loopLabel]⟩ :=
  (returned.step (.if_ (saved := [i64 saved]) (args := armArgs wide narrow next test) (guard := 1) rfl)).step (.block rfl)

private theorem crossed : BodyPath ⟨bytes 2, .branch [i64 60, i64 400, i32 30, i64 12] ⟨0⟩ bodyTail, [loopLabel]⟩ := by
  have returned : BodyPath ⟨bytes 2, .source (iterationValues 60 400 30 12 1) afterIteration, [loopLabel]⟩ :=
    first.step (.returned (vs := iterationValues 60 400 30 12 1) rfl rfl (.inl ⟨rfl, rfl, rfl⟩))
  have branch : BodyPath ⟨bytes 2, .branch [i64 400, i32 30, i64 12] ⟨1⟩ [.drop], [armLabel 60, loopLabel]⟩ :=
    (inArm returned).step (.brIf (stack := [i64 400, i32 30, i64 12]) (guard := 1))
  exact branch.step (.branchLower (by decide))

private theorem restarted : BodyPath ⟨bytes 2, .source [i64 42, i64 12] loopCode, []⟩ :=
  crossed.step (.branchRestart (scratch := [i64 60, i64 400, i32 30]) (args := [i64 12]) rfl rfl rfl)

-- Crossing the conditional leaves the pending branch, loop continuation,
-- and skipped loop tail visible under the live loop label.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 1 [loopInstr]
      [value (i64 60), value (i64 400), value (i32 30), value (i64 12), .source (.br ⟨0⟩), .source (.call ⟨2⟩)],
      .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, crossed, rfl, rfl⟩

-- The loop branch drops the scratch operands and reinstates the source loop.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), value (i64 12), .source loopInstr, .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, restarted, rfl, rfl⟩

private theorem exited : BodyPath ⟨bytes 4, .source [i64 42, i64 402, i32 32] afterLoop, []⟩ := by
  have returned : BodyPath ⟨bytes 3, .source (iterationValues 61 401 31 13 0) afterIteration, [loopLabel]⟩ :=
    (atIteration restarted).step (.returned (vs := iterationValues 61 401 31 13 0) rfl rfl (.inr ⟨rfl, rfl, .inl rfl⟩))
  have fallthrough : BodyPath ⟨bytes 3, .source [i64 401, i32 31, i64 13] [.drop], [armLabel 61, loopLabel]⟩ :=
    (inArm returned).step (.brIf (stack := [i64 401, i32 31, i64 13]) (guard := 0))
  have armResult : BodyPath ⟨bytes 3, .source [i64 401, i32 31] [], [armLabel 61, loopLabel]⟩ :=
    fallthrough.step (.drop (stack := [i64 401, i32 31]) (v := i64 13))
  have atTail : BodyPath ⟨bytes 3, .invoke [] complete [i64 61, i64 401, i32 31] [], [loopLabel]⟩ :=
    (armResult.step .armResult).step (.resolve (saved := []) (args := [i64 61, i64 401, i32 31]) rfl)
  have loopResult : BodyPath ⟨bytes 4, .source [i64 402, i32 32] [], [loopLabel]⟩ :=
    atTail.step (.returned (vs := [i64 402, i32 32]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact loopResult.step .armResult

example : Steps host launch ⟨memory.store (bytes 5), caller, values [i32 99]⟩ := by
  have atTail : BodyPath ⟨bytes 4, .invoke [] follow [i64 42, i64 402, i32 32] [], []⟩ :=
    exited.step (.resolve (saved := []) (args := [i64 42, i64 402, i32 32]) rfl)
  have returned : BodyPath ⟨bytes 5, .source [i32 99] [], []⟩ :=
    atTail.step (.returned (vs := [i32 99]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (returned.step .labelResult).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 6), caller, [.trap]⟩ := by
  have trapped : BodyPath ⟨bytes 6, .trapped [] (Continuation.code afterIteration), [loopLabel]⟩ :=
    (atIteration restarted).step (.trapped rfl (.inr ⟨rfl, rfl, .inr rfl⟩))
  have innerErased : BodyPath ⟨bytes 6, .trapped [] [], [loopLabel]⟩ :=
    trapped.step (.erase (cut := Continuation.code afterIteration) rfl rfl (.inr (by decide)))
  have outerErased : BodyPath ⟨bytes 6, .trapped [] [], []⟩ :=
    (innerErased.step .armTrap).step
      (.erase (removed := [i64 42]) (cut := Continuation.code afterLoop) rfl rfl (.inl (by decide)))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (outerErased.step .labelTrap).step .frameDone, rfl, rfl⟩

-- A normally deliverable pair finishes with i32, while a restart requires i64.
example : ¬ Check loopTargets loopResults loopResults [.br ⟨0⟩] := by
  intro checked
  generalize input : loopResults = stack at checked
  cases checked with
  | br target =>
    change some [num64] = some _ at target
    cases target
    have bad := congrArg List.getLast? input
    simp [loopResults, num32, num64] at bad

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.SuffixLoopExamples
