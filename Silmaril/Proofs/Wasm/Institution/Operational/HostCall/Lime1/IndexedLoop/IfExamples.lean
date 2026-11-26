module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IfExamples

open Execution.Runtime (Frame MemInst)
open Wasm.Lime1.Execution
open Continuation (Op Label)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def armType : Wasm.Lime1.FuncType := ⟨[num32, num64], [num64, num32, num64]⟩
private def joinType : Wasm.Lime1.FuncType := ⟨[num64, num32], [num32]⟩
private def prepare : Site Nat := ⟨⟨2⟩, ⟨[num64], [num32, num64, num32]⟩, 11⟩
private def inner : Site Nat := ⟨⟨3⟩, armType, 12⟩
private def alternate : Site Nat := ⟨⟨4⟩, signature, 13⟩
private def innerJoin : Site Nat := ⟨⟨5⟩, ⟨[num64, num64, num32, num64], [num32]⟩, 14⟩
private def outerJoin : Site Nat := ⟨⟨6⟩, joinType, 15⟩
private def innerAlternate : Site Nat := ⟨⟨7⟩, armType, 16⟩

private def innerType : Continuation.IfType := .indexed ⟨1⟩ armType
private def innerArm : List (Op Nat) := [.call ⟨2⟩ inner]
private def otherInnerArm : List (Op Nat) := [.call ⟨6⟩ innerAlternate]
private def alternateArm : List (Op Nat) := [.get ⟨0⟩, .call ⟨3⟩ alternate]
private def innerTail : List (Op Nat) := [.call ⟨4⟩ innerJoin]
private def innerBranch : List (Op Nat) := .if_ innerType innerArm otherInnerArm :: innerTail
private def outerArm : List (Op Nat) := .get ⟨0⟩ :: .get ⟨0⟩ :: .call ⟨1⟩ prepare :: innerBranch
private def joinTail : List (Op Nat) := [.call ⟨5⟩ outerJoin]
private def outerLabel : Label Nat := ⟨.scalar num32, [i64 42], joinTail⟩
private def innerLabel : Label Nat := ⟨innerType, [i64 7], innerTail⟩

private def program : Program Nat where
  module := {types := [signature, armType], funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩], memories := [⟨0⟩]}
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ (.scalar num32) outerArm alternateArm :: joinTail
  saved := 42

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm program.functionType program.module program.function, .host producerType 10,
      .host prepare.type prepare.code, .host inner.type inner.code, .host alternate.type alternate.code,
      .host innerJoin.type innerJoin.code, .host outerJoin.type outerJoin.code,
      .host innerAlternate.type innerAlternate.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl⟩
private def caller : Frame := ⟨[i32 99], {funcs := [⟨0⟩]}⟩

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have innerChecked : Continuation.Checked base program.module [num64] [armType.results, [num32], [num32]] armType.results armType.params innerArm :=
    .call (site := inner) (saved := []) rfl rfl .nil
  have otherInnerChecked : Continuation.Checked base program.module [num64] [armType.results, [num32], [num32]] armType.results armType.params otherInnerArm :=
    .call (site := innerAlternate) (saved := []) rfl rfl .nil
  have alternateChecked : Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [] alternateArm :=
    .get (type := num64) (stack := []) rfl (.call (site := alternate) (saved := []) rfl rfl .nil)
  have innerTailChecked : Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [num64, num64, num32, num64] innerTail :=
    .call (site := innerJoin) (saved := []) rfl rfl .nil
  have branch : Continuation.Checked base program.module [num64] [[num32], [num32]] [num32]
      [num64, num32, num64, num32] innerBranch :=
    .if_ (type := innerType) (saved := [num64]) rfl innerChecked otherInnerChecked innerTailChecked
  have outerChecked : Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [] outerArm :=
    .get (type := num64) (stack := []) rfl (.get (type := num64) (stack := [num64]) rfl
      (.call (site := prepare) (saved := [num64]) rfl rfl branch))
  have joinChecked : Continuation.Checked base program.module [num64] [[num32]] [num32] [num64, num32] joinTail :=
    .call (site := outerJoin) (saved := []) rfl rfl .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl, .if_ (type := .scalar num32) (saved := [num64]) rfl outerChecked alternateChecked joinChecked, rfl, rfl⟩

private def guardValue (thenArm : Bool) : BitVec 32 := if thenArm then 1 else 0
private def loopBytes (thenArm : Bool) : ByteArray := bytes (if thenArm then 1 else 2)

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ args = [i64 7] ∧ ∃ flag : Bool,
      outcome = .returned (memory.store (loopBytes flag)) (.values [i32 (guardValue flag), i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ args = [i64 7] ∧ ∃ flag : Bool,
      outcome = .returned (memory.store (bytes 3)) (.values [i32 21, i64 22, i32 (guardValue flag)])
  | 12 => store = memory.store (bytes 3) ∧ args = [i32 21, i64 22] ∧
      (outcome = .returned (memory.store (bytes 4)) (.values [i64 30, i32 31, i64 34]) ∨
       outcome = .returned (memory.store (bytes 5)) .trap)
  | 13 => store = memory.store (bytes 2) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 7)) (.values [i32 47])
  | 14 => ((store = memory.store (bytes 4) ∧ args = [i64 7, i64 30, i32 31, i64 34]) ∨
      (store = memory.store (bytes 10) ∧ args = [i64 7, i64 32, i32 33, i64 35])) ∧
      outcome = .returned (memory.store (bytes 6)) (.values [i32 41])
  | 15 => (store = memory.store (bytes 6) ∧ args = [i64 42, i32 41] ∧
      outcome = .returned (memory.store (bytes 8)) (.values [i32 51])) ∨
      (store = memory.store (bytes 7) ∧ args = [i64 42, i32 47] ∧
      outcome = .returned (memory.store (bytes 9)) (.values [i32 52]))
  | 16 => store = memory.store (bytes 3) ∧ args = [i32 21, i64 22] ∧
      outcome = .returned (memory.store (bytes 10)) (.values [i64 32, i32 33, i64 35])
  | _ => False

private theorem prepareContract : prepare.Contract memory host := by
  intro _ _ _ _ _ _ h
  obtain ⟨_, _, flag, eq⟩ := h
  cases eq
  exact ⟨bytes 3, rfl, rfl, rfl⟩

private theorem innerContract : inner.Contract memory host := by
  intro _ _ _ _ _ _ answer
  rcases answer.2.2 with eq | eq
  · cases eq
    exact ⟨bytes 4, rfl, rfl, rfl⟩
  · cases eq
    exact ⟨bytes 5, rfl, rfl, trivial⟩

private theorem alternateContract : alternate.Contract memory host := by
  intro _ _ _ _ _ _ h
  cases h.2.2
  exact ⟨bytes 7, rfl, rfl, rfl⟩

private theorem innerJoinContract : innerJoin.Contract memory host := by
  intro _ _ _ _ _ _ h
  cases h.2
  exact ⟨bytes 6, rfl, rfl, rfl⟩

private theorem outerJoinContract : outerJoin.Contract memory host := by
  intro _ _ _ _ _ _ answer
  rcases answer with ⟨_, _, eq⟩ | ⟨_, _, eq⟩
  · cases eq
    exact ⟨bytes 8, rfl, rfl, rfl⟩
  · cases eq
    exact ⟨bytes 9, rfl, rfl, rfl⟩

private theorem innerAlternateContract : innerAlternate.Contract memory host := by
  intro _ _ _ _ _ _ h
  cases h.2.2
  exact ⟨bytes 10, rfl, rfl, rfl⟩

private theorem contract : program.Contract memory host := by
  constructor
  · intro _ _ _ _ _ _ answer
    obtain ⟨_, _, flag, eq⟩ := answer
    cases eq
    refine ⟨loopBytes flag, ?_, rfl, rfl⟩
    cases flag <;> rfl
  · exact .if_
      (.get (.get (.call prepareContract (.if_ (.call innerContract .nil)
        (.call innerAlternateContract .nil) (.call innerJoinContract .nil)))))
      (.get (.call alternateContract .nil)) (.call outerJoinContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩

private def wrap (q : Continuation.State Nat) : State Nat := ⟨q.bytes, .continuation q.phase q.labels⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path (wrap q)

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) program.functionResults a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem firstInvoke : Path ⟨bytes 0, .producerInvoke 7⟩ :=
  ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
    (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))

private theorem loopExit (flag : Bool) :
    BodyPath ⟨loopBytes flag, .source [i64 42, i32 (guardValue flag)] program.continuation, []⟩ := by
  have answer : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩
      ⟨loopBytes flag, .test (guardValue flag) 88 0⟩ :=
    .producerReturns (by cases flag <;> rfl) ⟨rfl, rfl, flag, rfl⟩
  exact (((firstInvoke.tail answer).tail (.control (.test (guardValue flag) 88 0))).tail
    (.control (.dropInput (guardValue flag) 88))).tail (.control (.loopResult (guardValue flag)))

private theorem inOuter (flag : Bool) :
    BodyPath ⟨loopBytes flag, .source [] (if flag then outerArm else alternateArm), [outerLabel]⟩ := by
  cases flag
  · exact ((loopExit false).step (.if_ (saved := [i64 42]) (guard := 0) (args := []) rfl)).step .block
  · exact ((loopExit true).step (.if_ (saved := [i64 42]) (guard := 1) (args := []) rfl)).step .block

private theorem reachesInnerBlock (flag : Bool) :
    BodyPath ⟨bytes 3, .block innerLabel [i32 21, i64 22] (if flag then innerArm else otherInnerArm),
      [outerLabel]⟩ := by
  have operands : BodyPath ⟨bytes 1, .source [i64 7, i64 7] (.call ⟨1⟩ prepare :: innerBranch), [outerLabel]⟩ :=
    ((inOuter true).step (.get rfl)).step (.get rfl)
  have pending : BodyPath ⟨bytes 1, .invoke [i64 7] prepare [i64 7] innerBranch, [outerLabel]⟩ :=
    operands.step (.resolve (site := prepare) (args := [i64 7]) (saved := [i64 7]) rfl)
  have next : BodyPath ⟨bytes 3, .source [i64 7, i32 21, i64 22, i32 (guardValue flag)] innerBranch, [outerLabel]⟩ :=
    pending.step (.returned (next := bytes 3) (site := prepare) (vs := [i32 21, i64 22, i32 (guardValue flag)])
      rfl rfl ⟨rfl, rfl, flag, rfl⟩)
  cases flag
  · exact next.step (.if_ (saved := [i64 7]) (args := [i32 21, i64 22]) (guard := 0) rfl)
  · exact next.step (.if_ (saved := [i64 7]) (args := [i32 21, i64 22]) (guard := 1) rfl)

private theorem atInner :
    BodyPath ⟨bytes 3, .invoke [] inner [i32 21, i64 22] [], [innerLabel, outerLabel]⟩ :=
  ((reachesInnerBlock true).step .block).step (.resolve (site := inner) (saved := []) (args := [i32 21, i64 22]) rfl)

-- Guard consumption leaves the ordered parameters in the enclosing stack
-- until the next native step moves them into the arity-three label.
example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .label 1 []
      [value (i64 7), value (i32 21), value (i64 22), .source (.block (.typeIdx ⟨1⟩) [.call ⟨2⟩]),
        .source (.call ⟨4⟩)], .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, reachesInnerBlock true, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .label 1 []
      [value (i64 7), .label 3 [] [value (i32 21), value (i64 22), .invoke ⟨3⟩], .source (.call ⟨4⟩)],
      .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, atInner, rfl, rfl⟩

private theorem joinInner {live : ByteArray} {wide extra : BitVec 64} {narrow : BitVec 32}
    (returned : BodyPath ⟨live, .source [i64 wide, i32 narrow, i64 extra] [], [innerLabel, outerLabel]⟩)
    (answer : host 14 (memory.store live) [i64 7, i64 wide, i32 narrow, i64 extra]
      (.returned (memory.store (bytes 6)) (.values [i32 41]))) :
    BodyPath ⟨bytes 6, .source [i64 42, i32 41] joinTail, []⟩ := by
  have resumed : BodyPath ⟨live, .source [i64 7, i64 wide, i32 narrow, i64 extra] innerTail, [outerLabel]⟩ :=
    returned.step .armResult
  have pending : BodyPath ⟨live, .invoke [] innerJoin [i64 7, i64 wide, i32 narrow, i64 extra] [], [outerLabel]⟩ :=
    resumed.step (.resolve (site := innerJoin) (saved := []) (args := [i64 7, i64 wide, i32 narrow, i64 extra]) rfl)
  have finished : BodyPath ⟨bytes 6, .source [i32 41] [], [outerLabel]⟩ :=
    pending.step (.returned (next := bytes 6) (site := innerJoin) (vs := [i32 41]) rfl rfl answer)
  exact finished.step .armResult

private theorem innerReturned : BodyPath ⟨bytes 4, .source [i64 30, i32 31, i64 34] [],
    [innerLabel, outerLabel]⟩ :=
  atInner.step (.returned (next := bytes 4) (site := inner) (vs := [i64 30, i32 31, i64 34]) rfl rfl
    ⟨rfl, rfl, .inl rfl⟩)

-- Native label completion puts the three results after the inner saved
-- operand and before the next call, without disturbing the outer label base.
example : Steps host launch ⟨memory.store (bytes 4), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .label 1 []
      [value (i64 7), value (i64 30), value (i32 31), value (i64 34), .source (.call ⟨4⟩)],
      .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, innerReturned.step .armResult, rfl, rfl⟩

private theorem throughInner : BodyPath ⟨bytes 6, .source [i64 42, i32 41] joinTail, []⟩ :=
  joinInner innerReturned ⟨.inl ⟨rfl, rfl⟩, rfl⟩

private theorem throughOtherInner : BodyPath ⟨bytes 6, .source [i64 42, i32 41] joinTail, []⟩ := by
  have pending : BodyPath ⟨bytes 3, .invoke [] innerAlternate [i32 21, i64 22] [], [innerLabel, outerLabel]⟩ :=
    ((reachesInnerBlock false).step .block).step
      (.resolve (site := innerAlternate) (saved := []) (args := [i32 21, i64 22]) rfl)
  have returned : BodyPath ⟨bytes 10, .source [i64 32, i32 33, i64 35] [], [innerLabel, outerLabel]⟩ :=
    pending.step (.returned (next := bytes 10) (site := innerAlternate) (vs := [i64 32, i32 33, i64 35]) rfl rfl
      ⟨rfl, rfl, rfl⟩)
  exact joinInner returned ⟨.inr ⟨rfl, rfl⟩, rfl⟩

private theorem throughAlternate : BodyPath ⟨bytes 7, .source [i64 42, i32 47] joinTail, []⟩ := by
  have pending : BodyPath ⟨bytes 2, .invoke [] alternate [i64 7] [], [outerLabel]⟩ :=
    ((inOuter false).step (.get rfl)).step (.resolve (site := alternate) (saved := []) (args := [i64 7]) rfl)
  have returned : BodyPath ⟨bytes 7, .source [i32 47] [], [outerLabel]⟩ :=
    pending.step (.returned (next := bytes 7) (site := alternate) (vs := [i32 47]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact returned.step .armResult

private theorem finish {live next : ByteArray} {input out : BitVec 32}
    (path : BodyPath ⟨live, .source [i64 42, i32 input] joinTail, []⟩)
    (liveNext : memory.Live next)
    (answer : host 15 (memory.store live) [i64 42, i32 input]
      (.returned (memory.store next) (.values [i32 out]))) :
    BodyPath ⟨next, .done (.values [i32 out]), []⟩ := by
  have pending : BodyPath ⟨live, .invoke [] outerJoin [i64 42, i32 input] [], []⟩ :=
    path.step (.resolve (site := outerJoin) (saved := []) (args := [i64 42, i32 input]) rfl)
  have returned : BodyPath ⟨next, .source [i32 out] [], []⟩ :=
    pending.step (.returned liveNext rfl answer)
  exact (returned.step .labelResult).step .frameDone

example : Steps host launch ⟨memory.store (bytes 8), caller, values [i32 51]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, finish (next := bytes 8) (out := 51) throughInner rfl (.inl ⟨rfl, rfl, rfl⟩), rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 8), caller, values [i32 51]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, finish (next := bytes 8) (out := 51) throughOtherInner rfl (.inl ⟨rfl, rfl, rfl⟩), rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 9), caller, values [i32 52]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, finish (next := bytes 9) (out := 52) throughAlternate rfl (.inr ⟨rfl, rfl, rfl⟩), rfl, rfl⟩

private theorem trapInOuter : BodyPath ⟨bytes 5, .trapped [i64 7] (Continuation.code innerTail), [outerLabel]⟩ := by
  have trapped : BodyPath ⟨bytes 5, .trapped [] [], [innerLabel, outerLabel]⟩ :=
    atInner.step (.trapped (next := bytes 5) (site := inner) rfl ⟨rfl, rfl, .inr rfl⟩)
  exact trapped.step .armTrap

private theorem trapAtJoin : BodyPath ⟨bytes 5, .trapped [i64 42] (Continuation.code joinTail), []⟩ := by
  have erased : BodyPath ⟨bytes 5, .trapped [] [], [outerLabel]⟩ :=
    trapInOuter.step (.erase (removed := [i64 7]) (cut := Continuation.code innerTail) rfl rfl (.inl (by decide)))
  exact erased.step .armTrap

example : Steps host launch ⟨memory.store (bytes 5), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 7), .trap, .source (.call ⟨4⟩)], .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, trapInOuter, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .trap, .source (.call ⟨5⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, trapAtJoin, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, [.trap]⟩ := by
  have erased : BodyPath ⟨bytes 5, .trapped [] [], []⟩ :=
    trapAtJoin.step (.erase (removed := [i64 42]) (cut := Continuation.code joinTail) rfl rfl (.inl (by decide)))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (erased.step .labelTrap).step .frameDone, rfl, rfl⟩

-- An in-range type index must resolve to the full declared signature.
example : ¬ Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [num64, num32, num64, num32]
    (.if_ (.indexed ⟨0⟩ armType) innerArm otherInnerArm :: innerTail) := by
  intro checked
  generalize ([num64, num32, num64, num32] : List NumType) = stack at checked
  cases checked with
  | if_ resolved _ _ _ =>
    change some signature = some armType at resolved
    exact (by decide : signature ≠ armType) (Option.some.inj resolved)

-- The complete parameter suffix is checked before selecting an arm.
example : ¬ Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [num64, num32] innerBranch := by
  intro checked
  generalize supplied : ([num64, num32] : List NumType) = stack at checked
  cases checked with
  | if_ _ _ _ _ =>
    have tooShort := congrArg List.length supplied
    simp [innerType, armType, Continuation.IfType.signature] at tooShort

example : ¬ Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [num64, num32, num32] innerBranch := by
  intro checked
  generalize supplied : ([num64, num32, num32] : List NumType) = stack at checked
  cases checked with
  | if_ _ _ _ _ =>
    change [num64, num32] ++ [num32] = _ ++ [num32] at supplied
    have beforeGuard := List.append_cancel_right supplied
    have last := congrArg List.getLast? beforeGuard
    simp [innerType, armType, Continuation.IfType.signature, num32, num64] at last

-- The untaken arm would leave the input order in place, which differs from
-- the declared result order.
example : ¬ Continuation.Checked base program.module [num64] [[num32], [num32]] [num32] [num64, num32, num64, num32]
    (.if_ innerType innerArm [] :: innerTail) := by
  intro checked
  generalize ([num64, num32, num64, num32] : List NumType) = stack at checked
  cases checked with
  | if_ _ _ other _ =>
    generalize input : innerType.signature.params = stack at other
    cases other
    contradiction

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IfExamples
