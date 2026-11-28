module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.BranchTableExamples

open Execution.Runtime (Frame MemInst Value)
open Wasm.Lime1.Execution
open Continuation (IfType Label Op)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def results : List NumType := [num64, num32]
private def armType : IfType := .indexed ⟨2⟩ ⟨[], results⟩
private def choose : Site Nat := ⟨⟨2⟩, ⟨[num64], [num32] ++ results ++ [num32]⟩, 11⟩
private def follow : Site Nat := ⟨⟨3⟩, ⟨num64 :: results, results⟩, 12⟩
private def armTail : List (Op Nat) := [.drop]
private def table : List (Op Nat) := .brTable [⟨0⟩] ⟨1⟩ :: armTail
private def arm : List (Op Nat) := .get ⟨0⟩ :: .call ⟨1⟩ choose :: table
private def rootTail : List (Op Nat) := [.call ⟨2⟩ follow]
private def label : Label Nat := ⟨armType, [i64 42], rootTail, none⟩

private def program : Program Nat where
  module := {
    types := [signature, ⟨[num64], results⟩, ⟨[], results⟩]
    funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ armType arm arm :: rootTail
  saved := 42
  functionIndex := ⟨1⟩
  functionResults := results

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm program.functionType program.module program.function,
      .host producerType 10, .host choose.type choose.code, .host follow.type follow.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl, .fixed⟩
private def caller : Frame := ⟨[i32 9], {funcs := [⟨0⟩]}⟩
private abbrev Check := Continuation.Checked base program.module [num64]

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have tableChecked : Check [results, results] results ([num32] ++ results ++ [num32]) table :=
    .brTable (scratch := [num32]) (payload := results) (by
      intro depth found
      obtain rfl := List.mem_singleton.mp found
      rfl) rfl
  have armChecked : Check [results, results] results [] arm :=
    .get (type := num64) (stack := []) rfl (.call (site := choose) (saved := []) rfl rfl tableChecked)
  have rootChecked : Check [results] results (num64 :: results) rootTail :=
    .call (site := follow) (saved := []) rfl rfl .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl, .if_ (type := armType) (saved := [num64]) rfl armChecked armChecked rootChecked,
    rfl, rfl⟩

private def payload : List Value := [i64 77, i32 22]
private def carried : List Value := i32 99 :: payload

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 1)) (.values [i32 1, i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ args = [i64 7] ∧ ∃ selector : BitVec 32,
      outcome = .returned (memory.store (bytes 2)) (.values (carried ++ [i32 selector]))
  | 12 => store = memory.store (bytes 2) ∧ args = i64 42 :: payload ∧
      outcome = .returned (memory.store (bytes 3)) (.values [i64 88, i32 33])
  | _ => False

private theorem contract : program.Contract memory host := by
  have chooseContract : choose.Contract memory host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, selector, eq⟩ := answer
    cases eq
    exact ⟨bytes 2, rfl, rfl, rfl⟩
  have followContract : follow.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 3, rfl, rfl, rfl⟩
  have armContract : Continuation.Contract memory host arm := .get (.call chooseContract .brTable)
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 1, rfl, rfl, rfl⟩
  · exact .if_ armContract armContract (.call followContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) results a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem atTable (selector : BitVec 32) :
    BodyPath ⟨bytes 2, .source (carried ++ [i32 selector]) table, [label]⟩ := by
  have producer : Path ⟨bytes 0, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨bytes 1, .source [i64 42, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have inside : BodyPath ⟨bytes 1, .source [] arm, [label]⟩ :=
    (exit.step (.if_ (saved := [i64 42]) (args := []) (guard := 1) rfl)).step (.block rfl)
  have choosing : BodyPath ⟨bytes 1, .invoke [] choose [i64 7] table, [label]⟩ :=
    (inside.step (.get rfl)).step (.resolve (saved := []) (args := [i64 7]) rfl)
  exact choosing.step (.returned (vs := carried ++ [i32 selector]) rfl rfl ⟨rfl, rfl, selector, rfl⟩)

private theorem selectTable (selector : BitVec 32) :
    BodyPath ⟨bytes 2, .branch carried (([⟨0⟩] : List LabelIdx)[selector.toNat]?.getD ⟨1⟩) armTail, [label]⟩ :=
  (atTable selector).step (.brTable (stack := carried) (depths := [⟨0⟩]) (fallback := ⟨1⟩))

-- Both selections leave the same scratch and payload until native label transfer.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 2 (program.active 7)
    [.label 2 [] [value (i64 42), .label 2 [] [value (i32 99), value (i64 77), value (i32 22),
      .source (.br ⟨0⟩), .source .drop], .source (.call ⟨2⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, selectTable 0, rfl, rfl⟩

-- The i32 bit pattern for -1 is the unsigned index 2^32 - 1.
example : (-1 : BitVec 32).toNat = 4294967295 := rfl

example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 2 (program.active 7)
    [.label 2 [] [value (i64 42), .label 2 [] [value (i32 99), value (i64 77), value (i32 22),
      .source (.br ⟨1⟩), .source .drop], .source (.call ⟨2⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, selectTable (-1), rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 3), caller, values [i64 88, i32 33]⟩ := by
  have delivered : BodyPath ⟨bytes 2, .source (i64 42 :: payload) rootTail, []⟩ :=
    (selectTable 0).step (.branchDeliver (scratch := [i32 99]) (payload := payload) rfl rfl rfl)
  have invoked : BodyPath ⟨bytes 2, .invoke [] follow (i64 42 :: payload) [], []⟩ :=
    delivered.step (.resolve (saved := []) (args := i64 42 :: payload) rfl)
  have returned : BodyPath ⟨bytes 3, .source [i64 88, i32 33] [], []⟩ :=
    invoked.step (.returned (vs := [i64 88, i32 33]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, (returned.step .labelResult).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, values payload⟩ := by
  have lowered : BodyPath ⟨bytes 2, .branch (i64 42 :: carried) ⟨0⟩ rootTail, []⟩ :=
    (selectTable (-1)).step (.branchLower (by decide))
  have returned : BodyPath ⟨bytes 2, .frameResult (.values payload), []⟩ :=
    lowered.step (.functionBranch (scratch := [i64 42, i32 99]) (payload := payload) rfl rfl)
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, returned.step .frameDone, rfl, rfl⟩

-- Slot zero and the default agree. Even with selector zero, the checker rejects
-- the other entry's reversed signature.
example : ¬ Check [results, [num32, num64], results] results ([num32] ++ results ++ [num32])
    [.brTable [⟨0⟩, ⟨1⟩] ⟨2⟩] := by
  intro checked
  generalize ([num32] ++ results ++ [num32]) = stack at checked
  cases checked with
  | brTable listed defaultTarget =>
    have bad := listed ⟨1⟩ (by decide)
    change some ([num32, num64] : List NumType) = some _ at bad
    change some results = some _ at defaultTarget
    exact (by decide : [num32, num64] ≠ results) (Option.some.inj (bad.trans defaultTarget.symm))

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.BranchTableExamples
