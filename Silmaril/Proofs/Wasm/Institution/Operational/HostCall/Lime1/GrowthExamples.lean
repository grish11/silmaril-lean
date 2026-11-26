module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.GrowthExamples

open Execution
open Execution.Runtime (Frame FuncInst MemInst ModuleInst TableInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked
open IndexedLoop (Program Edge call_run_iff producerType i32 i64)

-- Keep the concrete page behind its size proof so kernel conversion does
-- not expand the entire buffer while comparing checked configurations.
private opaque initialPage : { page : ByteArray // page.size = Memory.pageSize } :=
  ⟨⟨Array.replicate Memory.pageSize 0x5a⟩, by
    change (Array.replicate Memory.pageSize (0x5a : UInt8)).size = _
    simp⟩
private def firstPage : ByteArray := initialPage.val
private def initial : MemInst := ⟨firstPage, some 2⟩
private def written : ByteArray := (Memory.store firstPage 0 (count := 4) (0x04030201 : BitVec 32)).getD firstPage
private def grown : ByteArray := written ++ ⟨Array.replicate Memory.pageSize 0⟩

private theorem firstSize : firstPage.size = Memory.pageSize := initialPage.property

private theorem initialAllowed : MemoryGrow.SizeAllows initial 0 := by
  simp [MemoryGrow.SizeAllows, initial, firstSize, Memory.size, Memory.pageSize, Memory.maxPages]

private theorem writeEdge : MemoryWrite.EdgeAt firstPage 0 (.store 0 0x04030201) (.written written) := by
  apply MemoryWrite.fact_at (.write _ _ _ ?_)
  change Memory.store firstPage 0 (count := 4) (0x04030201 : BitVec 32) = some written
  cases found : Memory.store firstPage 0 (count := 4) (0x04030201 : BitVec 32) with
  | some data =>
    apply congrArg some
    unfold written
    exact congrArg (fun out : Option ByteArray => out.getD firstPage) found.symm
  | none =>
    have bounds := (MemoryWrite.store_none_iff_at (mem := firstPage) (offset := 0)
      (address := 0) (word := 0x04030201)).mp found
    rw [firstSize] at bounds
    exact (by decide : ¬ Memory.pageSize < (0 : BitVec 32).toNat + 0 + 4) bounds |>.elim

private theorem writtenSize : written.size = Memory.pageSize :=
  (show written.size = firstPage.size from MemoryWrite.closed_at writeEdge).trans firstSize

private theorem writtenPages : Memory.size written = 1 := by
  simp [Memory.size, writtenSize, Memory.pageSize]

private def signature : Wasm.Lime1.FuncType := ⟨[.int .i32], [.int .i64, .int .i32, .int .i32]⟩
private def calleeModule : ModuleInst := { types := [signature], memories := [⟨1⟩] }

private def fn : Graph.Memory32.Function where
  declaration := ⟨calleeModule, ⟨0⟩, signature.params, [], signature.results⟩
  rank := 0
  initial := [i64 6, i32 0, i32 0x04030201]
  code := [.store 0, .ranked (.numeric (.get ⟨0⟩)), .grow, .size]

private def target : MemoryTarget := ⟨⟨0⟩, fn⟩
private def table : TableInst := ⟨[some ⟨0⟩], none⟩
private def indirect : IndirectSite := ⟨⟨table, ⟨1⟩, signature⟩, ⟨[]⟩, [some fn]⟩
private def prepare : Site Nat := ⟨⟨4⟩, ⟨[.int .i64, .int .i32], [.int .i32, .int .i32, .int .i32]⟩, 9⟩
private def observe : Site Nat := ⟨⟨1⟩, ⟨[.int .i32] ++ signature.results, [.int .i32]⟩, 7⟩
private def saved : List Value := [i32 23]
private def lookupArgs : List Value := (saved ++ [i32 1]) ++ [i32 0]
private def afterLookup : List (Continuation.Op Nat) := [.call ⟨2⟩ observe]
private def lookupOps : List (Continuation.Op Nat) := .callIndirect indirect :: afterLookup

private def program : Program Nat where
  module := {
    types := [IndexedLoop.signature, signature]
    funcs := [⟨3⟩, ⟨4⟩, ⟨1⟩]
    tables := [⟨0⟩]
    memories := [⟨1⟩] }
  rootAddress := ⟨2⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨3⟩
  producerCode := 8
  continuation := .call ⟨1⟩ prepare :: lookupOps
  saved := 99

private def caller : Frame := ⟨[i64 111], { funcs := [⟨2⟩] }⟩
private def base : Store Nat :=
  { memories := [⟨⟨#[0xcc]⟩, none⟩, initial], tables := [table],
    funcs := [.wasm signature calleeModule target.code, .host observe.type 7,
      .wasm program.functionType program.module program.function, .host producerType 8, .host prepare.type 9] }

private def mem : Memory32 base := ⟨⟨1⟩, initial, rfl, .growing initialAllowed⟩
private def fixed : Memory32 base := ⟨⟨1⟩, initial, rfl, .fixed⟩

private theorem growEdge : MemoryGrow.Edge (mem.current written) (.request 1) (.grown grown) := by
  have allowed : MemoryGrow.SizeAllows (mem.current written) 1 := by
    simp [MemoryGrow.SizeAllows, mem, Memory32.current, initial, writtenSize, writtenPages, Memory.pageSize, Memory.maxPages]
  apply MemoryGrow.fact (.grow 1 grown ?_)
  exact (MemoryGrow.grow_eq_some_iff (m := mem.current written)).mpr ⟨allowed, by
    unfold grown
    rfl⟩

private theorem grownPages : Memory.size grown = 2 := by
  have count := MemoryGrow.grown_pages (m := mem.current written) growEdge
  change Memory.size grown = Memory.size written + 1 at count
  rw [writtenPages] at count
  exact count

private theorem writtenLive : mem.Live written :=
  mem.live_same_size mem.initial_live (writtenSize.trans firstSize.symm)

private theorem grownLive : mem.Live grown := mem.live_grow rfl writtenLive growEdge

-- A fixed profile rejects the same typed body as soon as it contains grow.
example : ¬ target.Checked fixed := by
  intro h
  have bad := h.supported
  contradiction

-- The bytes previously written at address zero survive. Growth adds a
-- separate zero-filled page, with the already-written array as its prefix.
example : Memory.load written 0 4 = some 0x04030201 :=
  MemoryWrite.read_after_write_at writeEdge
example : grown = written ++ ⟨Array.replicate Memory.pageSize 0⟩ :=
  MemoryGrow.grown_bytes (m := mem.current written) growEdge

-- Two extra pages would exceed the declared maximum of two.
example {extra : ByteArray} :
    ¬ MemoryGrow.Edge (mem.current written) (.request 2) (.grown extra) := by
  intro step
  cases MemoryGrow.invert step with
  | grow _ _ sized =>
    have bound := (MemoryGrow.grow_eq_some_iff (m := mem.current written) |>.mp sized).1.2.2
    change (some 2 : Option Nat).isNone ∨ Memory.size written + 2 ≤ 2 at bound
    rw [writtenPages] at bound
    simp at bound

private def host : HostSemantics Nat := fun code store operands outcome =>
  match code with
  | 8 => store = mem.store firstPage ∧ operands = [i64 7] ∧
      outcome = .returned (mem.store firstPage) (.values [i32 1, i64 88, i32 0])
  | 9 => store = mem.store firstPage ∧ operands = [i64 99, i32 1] ∧
      outcome = .returned (mem.store firstPage) (.values lookupArgs)
  | 7 => (store = mem.store grown ∧ operands = [i32 23, i64 6, i32 1, i32 2] ∧
      outcome = .returned (mem.store grown) (.values [i32 21])) ∨
      (store = mem.store written ∧ operands = [i32 23, i64 6, i32 (-1), i32 1] ∧
        outcome = .returned (mem.store written) (.values [i32 11]))
  | _ => False

private theorem linked : indirect.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro address registered found
    simp [indirect, Graph.Program.lookup] at found
  · intro address member
    simp [indirect, table] at member
    subst address
    exact ⟨.wasm signature calleeModule target.code, rfl,
      fun _ => .inr ⟨fn, rfl, show target.Allocated base from rfl⟩⟩

private theorem checked : program.Checked mem caller ⟨0⟩ := by
  have suffix : Continuation.Checked base program.module [.int .i64] [[.int .i32]] [.int .i32]
      ([.int .i32] ++ signature.results) afterLookup :=
    .call (site := observe) (saved := []) rfl (show observe.Allocated base from rfl) .nil
  have lookup : Continuation.Checked base program.module [.int .i64] [[.int .i32]] [.int .i32]
      (([.int .i32] ++ signature.params) ++ [.int .i32]) lookupOps :=
    .callIndirect (saved := [.int .i32]) linked suffix
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    .call (site := prepare) (saved := []) rfl (show prepare.Allocated base from rfl) lookup, rfl, rfl⟩

private theorem contract : program.Contract mem host := by
  have prepared : prepare.Contract mem host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨firstPage, mem.initial_live, rfl, rfl⟩
  have observed : observe.Contract mem host := by
    intro _ _ _ _ _ _ answer
    rcases answer with answer | answer
    · cases answer.2.2
      exact ⟨grown, grownLive, rfl, rfl⟩
    · cases answer.2.2
      exact ⟨written, writtenLive, rfl, rfl⟩
  have atSite : indirect.Contract mem host := by
    constructor
    · intro address code member allocated
      simp [indirect, table] at member
      subst address
      cases (show some (.wasm signature calleeModule target.code : FuncInst Wasm.Lime1.Func Nat)
        = some (.host signature code) from allocated)
    · intro callee found
      rcases callee with ⟨⟨address⟩, registered⟩
      cases address with
      | zero =>
        change some fn = some registered at found
        cases found
        exact ⟨rfl, rfl, rfl, rfl⟩
      | succ => simp [IndirectSite.memoryLookup, indirect] at found
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨firstPage, mem.initial_live, rfl, rfl⟩
  · exact .call prepared (.callIndirect atSite (.call observed .nil))

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program mem host 7) ⟨firstPage, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge mem host (program.active 7) [.int .i32] a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem BodyPath.calleeStep {bytes next : ByteArray} {a b : MemoryCallee.Phase}
    (path : BodyPath ⟨bytes, .memory saved target a afterLookup, []⟩)
    (move : MemoryCallee.Edge mem target bytes a next b) :
    BodyPath ⟨next, .afterMemory saved target afterLookup b, []⟩ :=
  path.step (.memory move)

private theorem atGrow :
    BodyPath ⟨written, .memory saved target (.body [i32 1] [i64 6, i32 1] [.grow, .size]) afterLookup, []⟩ := by
  have producer : Path ⟨firstPage, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program mem host 7 ⟨firstPage, .producerInvoke 7⟩ ⟨firstPage, .test 1 88 0⟩ :=
    .producerReturns mem.initial_live ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨firstPage, .source [i64 99, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have preparing : BodyPath ⟨firstPage, .invoke [] prepare [i64 99, i32 1] lookupOps, []⟩ :=
    exit.step (.resolve (saved := []) (args := [i64 99, i32 1]) rfl)
  have lookup : BodyPath ⟨firstPage, .source lookupArgs lookupOps, []⟩ :=
    preparing.step (.returned (vs := lookupArgs) mem.initial_live rfl ⟨rfl, rfl, rfl⟩)
  have invoke : BodyPath ⟨firstPage, .memory saved target (.invoke [i32 1]) afterLookup, []⟩ :=
    lookup.step (.callIndirect (saved := saved) (args := [i32 1]) rfl
      (.memory (callee := target) rfl rfl (show target.Allocated base from rfl) rfl))
  have entered : BodyPath ⟨firstPage, .memory saved target (.body [i32 1] fn.initial fn.code) afterLookup, []⟩ :=
    invoke.calleeStep .enter
  have stored : BodyPath ⟨written, .memory saved target
      (.body [i32 1] [i64 6] [.ranked (.numeric (.get ⟨0⟩)), .grow, .size]) afterLookup, []⟩ :=
    entered.calleeStep (.store (args := [i32 1]) (saved := [i64 6]) writeEdge)
  exact stored.calleeStep (.get (v := i32 1) rfl)

private theorem atSizeSuccess : BodyPath ⟨grown, .memory saved target
    (.body [i32 1] [i64 6, i32 1] [.size]) afterLookup, []⟩ := by
  have old : MemoryCallee.pages written = i32 1 := by simp [MemoryCallee.pages, writtenPages]
  simpa only [Continuation.Phase.afterMemory, List.singleton_append, old] using
    atGrow.calleeStep (.grow (args := [i32 1]) (saved := [i64 6]) rfl growEdge)

private theorem atSizeFailure : BodyPath ⟨written, .memory saved target
    (.body [i32 1] [i64 6, i32 (-1)] [.size]) afterLookup, []⟩ :=
  atGrow.calleeStep (.growFail (args := [i32 1]) (saved := [i64 6]))

-- Both outcomes reach the next native source instruction from ordinary entry.
example : Steps host launch (program.render mem caller ⟨0⟩ 7 ⟨grown, .continuation
    (.memory saved target (.body [i32 1] [i64 6, i32 1] [.size]) afterLookup) []⟩) :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, atSizeSuccess, grownLive, rfl⟩

example : Steps host launch (program.render mem caller ⟨0⟩ 7 ⟨written, .continuation
    (.memory saved target (.body [i32 1] [i64 6, i32 (-1)] [.size]) afterLookup) []⟩) :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, atSizeFailure, writtenLive, rfl⟩

private theorem finish {bytes : ByteArray} {old result : BitVec 32}
    (path : BodyPath ⟨bytes, .memory saved target (.body [i32 1] [i64 6, i32 old] [.size]) afterLookup, []⟩)
    (live : mem.Live bytes)
    (answer : host 7 (mem.store bytes) (saved ++ [i64 6, i32 old, MemoryCallee.pages bytes])
      (.returned (mem.store bytes) (.values [i32 result]))) :
    Steps host launch ⟨mem.store bytes, caller, values [i32 result]⟩ := by
  let out := [i64 6, i32 old, MemoryCallee.pages bytes]
  have sized : BodyPath ⟨bytes, .memory saved target (.body [i32 1] out []) afterLookup, []⟩ :=
    path.calleeStep .size
  have exit : BodyPath ⟨bytes, .memory saved target (.exit [i32 1] (.values out)) afterLookup, []⟩ :=
    sized.calleeStep .labelDone
  have returned : BodyPath ⟨bytes, .source (saved ++ out) afterLookup, []⟩ :=
    exit.calleeStep .frameDone
  have observed : BodyPath ⟨bytes, .invoke [] observe (saved ++ out) [], []⟩ :=
    returned.step (.resolve (saved := []) (args := saved ++ out) rfl)
  have done : BodyPath ⟨bytes, .source [i32 result] [], []⟩ :=
    observed.step (.returned (vs := [i32 result]) live rfl answer)
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (done.step .labelResult).step .frameDone, live, rfl⟩

-- The following host checks the actual bytes, old/reported result and new
-- page count. The same request also admits an in-limit resource failure.
example : Steps host launch ⟨mem.store grown, caller, values [i32 21]⟩ := by
  apply finish atSizeSuccess grownLive
  have new : MemoryCallee.pages grown = i32 2 := by simp [MemoryCallee.pages, grownPages]
  rw [new]
  exact .inl ⟨rfl, rfl, rfl⟩

example : Steps host launch ⟨mem.store written, caller, values [i32 11]⟩ := by
  apply finish atSizeFailure writtenLive
  have old : MemoryCallee.pages written = i32 1 := by simp [MemoryCallee.pages, writtenPages]
  rw [old]
  exact .inr ⟨rfl, rfl, rfl⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.GrowthExamples
