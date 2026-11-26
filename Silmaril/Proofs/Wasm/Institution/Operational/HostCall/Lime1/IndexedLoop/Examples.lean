module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Examples

open Execution.Runtime (Frame MemInst)
open Wasm.Lime1.Execution

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩

private def program : Program Nat where
  module := { types := [signature], funcs := [⟨1⟩, ⟨2⟩], memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  laterIndex := ⟨1⟩
  laterAddress := ⟨2⟩
  laterCode := 11
  saved := 42

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm signature program.module program.function,
      .host producerType 10, .host laterType 11] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl⟩
private def caller : Frame := ⟨[i32 99], { funcs := [⟨0⟩] }⟩

private theorem checked : program.Checked memory caller ⟨0⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 =>
    (store = memory.store (bytes 0) ∧ args = [i64 7] ∧
      (outcome = .returned (memory.store (bytes 1)) (.values [i32 75, i64 12, i32 1]) ∨
       outcome = .diverged)) ∨
    (store = memory.store (bytes 1) ∧ args = [i64 12] ∧
      (outcome = .returned (memory.store (bytes 2)) (.values [i32 23, i64 88, i32 0]) ∨
       outcome = .returned (memory.store (bytes 3)) .trap))
  | 11 => store = memory.store (bytes 2) ∧ args = [i64 42, i32 23] ∧
    outcome = .returned store (.values [i32 5])
  | _ => False

private theorem contract : program.Contract memory host := by
  constructor
  · intro liveBytes args returned outcome _ _ answer
    change host 10 (memory.store liveBytes) args (.returned returned outcome) at answer
    rcases answer with ⟨_, _, eq | diverged⟩ | ⟨_, _, eq | eq⟩
    · cases eq
      exact ⟨bytes 1, rfl, rfl, rfl⟩
    · cases diverged
    · cases eq
      exact ⟨bytes 2, rfl, rfl, rfl⟩
    · cases eq
      exact ⟨bytes 3, rfl, rfl, trivial⟩
  · intro liveBytes args returned outcome _ _ answer
    change host 11 (memory.store liveBytes) args (.returned returned outcome) at answer
    obtain ⟨eq, _, resultEq⟩ := answer
    cases resultEq
    exact ⟨bytes 2, rfl, eq, rfl⟩

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩

private theorem firstInvoke : Path ⟨bytes 0, .producerInvoke 7⟩ :=
  ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
    (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))

private theorem restart : Path ⟨bytes 1, .enterLoop 12⟩ := by
  have returns : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 75 12 1⟩ :=
    .producerReturns rfl (.inl ⟨rfl, rfl, .inl rfl⟩)
  exact ((firstInvoke.tail returns).tail (.control (.test 75 12 1))).tail (.control (.restart 75 12))

private theorem secondInvoke : Path ⟨bytes 1, .producerInvoke 12⟩ :=
  (restart.tail (.control (.openLoop 12))).tail (.control (.resolveProducer 12))

-- Native readback includes the pending loop instruction and the next
-- invocation separately. The active i64 local remains the initial argument.
example : Steps host launch ⟨memory.store (bytes 1), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] (values [i64 42, i64 12] ++ [.source program.loop.instr, .source (.call ⟨1⟩)])]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, restart, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 1), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .label 1 [program.loop.instr]
      [value (i64 12), .invoke ⟨1⟩, .source (.brIf ⟨0⟩), .source .drop], .source (.call ⟨1⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, secondInvoke, rfl, rfl⟩

private theorem reachesLater : Path ⟨bytes 2, .laterInvoke 23⟩ := by
  have returns : Edge program memory host 7 ⟨bytes 1, .producerInvoke 12⟩ ⟨bytes 2, .test 23 88 0⟩ :=
    .producerReturns rfl (.inr ⟨rfl, rfl, .inl rfl⟩)
  exact ((((secondInvoke.tail returns).tail (.control (.test 23 88 0))).tail
    (.control (.dropInput 23 88))).tail (.control (.loopResult 23))).tail (.control (.resolveLater 23))

-- The later host receives the saved i64 below the i32 and sees the latest bytes.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), value (i32 23), .invoke ⟨2⟩]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, reachesLater, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, values [i32 5]⟩ := by
  have returns : Edge program memory host 7 ⟨bytes 2, .laterInvoke 23⟩ ⟨bytes 2, .bodyResult 5⟩ :=
    .laterReturns rfl ⟨rfl, rfl, rfl⟩
  have trace := ((reachesLater.tail returns).tail (.control (.exitResult 5))).tail (.control (.finish (some 5)))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, trace, rfl, rfl⟩

private theorem trapInLoop : Path ⟨bytes 3, .loopTrap Program.afterProducer⟩ :=
  secondInvoke.tail (.producerTraps rfl (.inr ⟨rfl, rfl, .inr rfl⟩))

-- A second possible answer at the same invocation returns a trap with more
-- writes. The loop's native label exit exposes the pending tail before the
-- next trap erasure discards it.
private theorem trapInBody : Path ⟨bytes 3, .bodyTrap [i64 42] program.afterLoop⟩ :=
  (trapInLoop.tail (.control (.eraseLoop (cut := Program.afterProducer) (tail := []) rfl (by decide)))).tail (.control .exitLoop)

example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .trap, .source (.call ⟨1⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, trapInBody, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 3), caller, [.trap]⟩ := by
  have erase : Edge program memory host 7 ⟨bytes 3, .bodyTrap [i64 42] program.afterLoop⟩
      ⟨bytes 3, .bodyTrap [] []⟩ :=
    .control (.eraseBody (removed := [i64 42]) (cut := program.afterLoop) rfl rfl (.inl (by decide)))
  have trace := ((trapInBody.tail erase).tail (.control .exitTrap)).tail (.control (.finish none))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, trace, rfl, rfl⟩

example : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 0, .producerInvoke 7⟩ :=
  .producerDiverges (.inl ⟨rfl, rfl, .inr rfl⟩)

example {dst : Config Nat} : ¬ Step host (program.render memory caller ⟨0⟩ 7 ⟨bytes 0, .producerInvoke 8⟩) dst := by
  intro move
  obtain ⟨_, next, _⟩ := (step_iff checked contract (a := ⟨bytes 0, .producerInvoke 8⟩) rfl).mp move
  cases next with
  | control step => cases step
  | producerReturns _ answer | producerTraps _ answer | producerDiverges answer =>
    rcases answer with ⟨_, eq, _⟩ | ⟨_, eq, _⟩ <;> exact (by decide : _ ≠ _) eq

example : ¬ ({ program with loopIndex := ⟨1⟩ }).Checked memory caller ⟨0⟩ := by
  intro bad
  have impossible : none = some signature := bad.loopIndex
  cases impossible

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Examples
