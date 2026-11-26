module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Examples

open Execution.Runtime (Frame MemInst)
open Wasm.Lime1.Execution

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩

private def middle : Site Nat := ⟨⟨2⟩, ⟨[.int .i32], [.int .i32, .int .i64]⟩, 11⟩
private def last : Site Nat := ⟨⟨3⟩, ⟨[.int .i64, .int .i32, .int .i64], [.int .i32]⟩, 12⟩
private def postMiddle : List (Continuation.Op Nat) := [.drop, .get ⟨0⟩, .call ⟨2⟩ last]

private def program : Program Nat where
  module := { types := [signature], funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩], memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .call ⟨1⟩ middle :: postMiddle
  saved := 42

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm program.functionType program.module program.function,
      .host producerType 10, .host middle.type middle.code, .host last.type last.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl⟩
private def caller : Frame := ⟨[i32 99], { funcs := [⟨0⟩] }⟩

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  have lastChecked : Continuation.Checked base program.module [.int .i64] [signature.results] signature.results
      [.int .i64, .int .i32, .int .i64] [.call ⟨2⟩ last] :=
    .call (base := base) (site := last) (index := ⟨2⟩) (saved := []) rfl rfl .nil
  have middleTail : Continuation.Checked base program.module [.int .i64] [signature.results] signature.results
      [.int .i64, .int .i32, .int .i64] postMiddle :=
    .drop (type := .int .i64) (.get (stack := [.int .i64, .int .i32]) (index := ⟨0⟩)
      (type := .int .i64) rfl lastChecked)
  exact .call (base := base) (site := middle) (index := ⟨1⟩) (saved := [.int .i64]) rfl rfl middleTail

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 =>
    (store = memory.store (bytes 0) ∧ args = [i64 7] ∧
      (outcome = .returned (memory.store (bytes 1)) (.values [i32 75, i64 12, i32 1]) ∨
       outcome = .diverged)) ∨
    (store = memory.store (bytes 1) ∧ args = [i64 12] ∧
      (outcome = .returned (memory.store (bytes 2)) (.values [i32 23, i64 88, i32 0]) ∨
       outcome = .returned (memory.store (bytes 3)) .trap))
  | 11 => store = memory.store (bytes 2) ∧ args = [i32 23] ∧
    (outcome = .returned (memory.store (bytes 4)) (.values [i32 31, i64 77]) ∨
     outcome = .returned (memory.store (bytes 5)) .trap)
  | 12 => store = memory.store (bytes 4) ∧ args = [i64 42, i32 31, i64 7] ∧
    outcome = .returned (memory.store (bytes 6)) (.values [i32 5])
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
  · refine .call ?_ (.drop (.get (.call ?_ .nil)))
    · intro liveBytes args returned outcome _ _ answer
      change host 11 (memory.store liveBytes) args (.returned returned outcome) at answer
      obtain ⟨_, _, eq | eq⟩ := answer
      · cases eq
        exact ⟨bytes 4, rfl, rfl, rfl⟩
      · cases eq
        exact ⟨bytes 5, rfl, rfl, trivial⟩
    · intro liveBytes args returned outcome _ _ answer
      change host 12 (memory.store liveBytes) args (.returned returned outcome) at answer
      obtain ⟨_, _, eq⟩ := answer
      cases eq
      exact ⟨bytes 6, rfl, rfl, rfl⟩

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
    [.label 1 [] (values [i64 42, i64 12] ++ .source program.loop.instr :: program.afterLoop)]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, restart, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 1), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] (value (i64 42) :: .label 1 [program.loop.instr]
      [value (i64 12), .invoke ⟨1⟩, .source (.brIf ⟨0⟩), .source .drop] :: program.afterLoop)]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, secondInvoke, rfl, rfl⟩

private theorem reachesMiddle : Path ⟨bytes 2, .continuation (.invoke [i64 42] middle [i32 23] postMiddle) []⟩ := by
  have returns : Edge program memory host 7 ⟨bytes 1, .producerInvoke 12⟩ ⟨bytes 2, .test 23 88 0⟩ :=
    .producerReturns rfl (.inr ⟨rfl, rfl, .inl rfl⟩)
  exact ((((secondInvoke.tail returns).tail (.control (.test 23 88 0))).tail
    (.control (.dropInput 23 88))).tail (.control (.loopResult 23))).tail (.continuation (.resolve (site := middle) (args := [i32 23]) (saved := [i64 42]) rfl))

-- The first continuation site consumes the loop's i32 while the i64 stays
-- immediately below its callout operands.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), value (i32 23), .invoke ⟨2⟩, .source .drop,
      .source (.localGet ⟨0⟩), .source (.call ⟨2⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, reachesMiddle, rfl, rfl⟩

private theorem reachesLast : Path ⟨bytes 4, .continuation (.invoke [] last [i64 42, i32 31, i64 7] []) []⟩ := by
  have returns : Edge program memory host 7 ⟨bytes 2, .continuation (.invoke [i64 42] middle [i32 23] postMiddle) []⟩
      ⟨bytes 4, .continuation (.source [i64 42, i32 31, i64 77] postMiddle) []⟩ :=
    .continuation (.returned rfl rfl ⟨rfl, rfl, .inl rfl⟩)
  exact (((reachesMiddle.tail returns).tail (.continuation (.drop (stack := [i64 42, i32 31])))).tail
    (.continuation (.get rfl))).tail (.continuation (.resolve (site := last) (args := [i64 42, i32 31, i64 7]) (saved := []) rfl))

-- The second site observes the saved i64, the first site's i32 result, the
-- read of local zero, and the first site's new bytes.
example : Steps host launch ⟨memory.store (bytes 4), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), value (i32 31), value (i64 7), .invoke ⟨3⟩]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, reachesLast, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 6), caller, values [i32 5]⟩ := by
  have returns : Edge program memory host 7 ⟨bytes 4, .continuation (.invoke [] last [i64 42, i32 31, i64 7] []) []⟩
      ⟨bytes 6, .continuation (.source [i32 5] []) []⟩ :=
    .continuation (.returned rfl rfl ⟨rfl, rfl, rfl⟩)
  have trace := ((reachesLast.tail returns).tail (.continuation .labelResult)).tail (.continuation .frameDone)
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, trace, rfl, rfl⟩

private theorem trapInLoop : Path ⟨bytes 3, .loopTrap Program.afterProducer⟩ :=
  secondInvoke.tail (.producerTraps rfl (.inr ⟨rfl, rfl, .inr rfl⟩))

private theorem trapFromLoop : Path ⟨bytes 3, .continuation (.trapped [i64 42] program.afterLoop) []⟩ :=
  (trapInLoop.tail (.control (.eraseLoop (cut := Program.afterProducer) (tail := []) rfl (by decide)))).tail
    (.control .exitLoop)

example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] (value (i64 42) :: .trap :: program.afterLoop)]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, trapFromLoop, rfl, rfl⟩

private theorem trapFromMiddle : Path ⟨bytes 5, .continuation (.trapped [i64 42] (Continuation.code postMiddle)) []⟩ :=
  reachesMiddle.tail (.continuation (.trapped rfl ⟨rfl, rfl, .inr rfl⟩))

example : Steps host launch ⟨memory.store (bytes 5), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .trap, .source .drop, .source (.localGet ⟨0⟩), .source (.call ⟨2⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, trapFromMiddle, rfl, rfl⟩

private theorem unwind {live : ByteArray} {rest : List Admin}
    (trapped : Path ⟨live, .continuation (.trapped [i64 42] rest) []⟩) :
    Path ⟨live, .continuation (.done .trap) []⟩ := by
  have erase : Edge program memory host 7 ⟨live, .continuation (.trapped [i64 42] rest) []⟩
       ⟨live, .continuation (.trapped [] []) []⟩ :=
    .continuation (.erase (removed := [i64 42]) (cut := rest) rfl (List.append_nil _).symm (.inl (by decide)))
  exact ((trapped.tail erase).tail (.continuation .labelTrap)).tail (.continuation .frameDone)

example : Steps host launch ⟨memory.store (bytes 3), caller, [.trap]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, unwind trapFromLoop, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, [.trap]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, unwind trapFromMiddle, rfl, rfl⟩

example : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 0, .producerInvoke 7⟩ :=
  .producerDiverges (.inl ⟨rfl, rfl, .inr rfl⟩)

example {dst : Config Nat} : ¬ Step host (program.render memory caller ⟨0⟩ 7 ⟨bytes 0, .producerInvoke 8⟩) dst := by
  intro move
  obtain ⟨_, next, _⟩ := (step_iff checked contract (a := ⟨bytes 0, .producerInvoke 8⟩) trivial rfl).mp move
  cases next with
  | control step => cases step
  | producerReturns _ answer | producerTraps _ answer | producerDiverges answer =>
    rcases answer with ⟨_, eq, _⟩ | ⟨_, eq, _⟩ <;> exact (by decide : _ ≠ _) eq

example : ¬ ({ program with loopIndex := ⟨1⟩ }).Checked memory caller ⟨0⟩ := by
  intro bad
  have impossible : none = some signature := bad.loopIndex
  cases impossible

example : ¬ Continuation.Checked base program.module [.int .i64] [signature.results] signature.results
    [.int .i64, .int .i32] [.get ⟨1⟩] := by
  intro typed
  generalize ([.int .i64, .int .i32] : List NumType) = stack at typed
  cases typed with
  | get lookup _ => cases lookup

example : ¬ Continuation.Checked base program.module [.int .i64] [signature.results] signature.results
    [.int .i32, .int .i64] [.call ⟨1⟩ middle] := by
  intro typed
  generalize bad : ([.int .i32, .int .i64] : List NumType) = stack at typed
  cases typed with
  | call _ _ _ =>
    have impossible := congrArg List.getLast? bad
    simp [middle] at impossible

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Examples
