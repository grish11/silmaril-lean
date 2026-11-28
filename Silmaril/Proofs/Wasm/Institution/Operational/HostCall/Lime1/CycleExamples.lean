module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.CycleExamples

open Execution.Runtime (Frame FuncAddr FuncInst ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Ranked
open IndexedLoop (Edge Program State call_run_iff producerType)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64

private def empty : ByteArray := ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
private def written : ByteArray := ⟨#[0, 1, 2, 3, 4, 0, 0, 0, 0, 0]⟩
private abbrev word : BitVec 32 := 0x04030201
private def signature : Wasm.Lime1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def moduleAt : ModuleInst :=
  { types := [signature], funcs := [⟨1⟩], tables := [⟨0⟩], memories := [⟨0⟩] }
private def declaration : Declaration := ⟨moduleAt, ⟨0⟩, signature.params, [], signature.results⟩
private def callB : CallTarget := ⟨⟨0⟩, ⟨1⟩, declaration⟩
private def getSelector : Graph.Memory32.Op := .ranked (.numeric (.get ⟨0⟩))
private def choose : Graph.Memory32.Op := .callIndirect ⟨0⟩ ⟨signature.params, signature.results⟩

-- A writes before calling B. B uses the live selector to call A again or
-- to choose a returning leaf. All three functions have the same signature.
private def aFn : Graph.Memory32.Function :=
  ⟨declaration, 0, [i32 0, i32 word], [.store 1, getSelector, .ranked (.call callB)]⟩
private def bFn : Graph.Memory32.Function :=
  ⟨declaration, 0, [], [getSelector, getSelector, choose]⟩
private def leafFn : Graph.Memory32.Function := ⟨declaration, 0, [i32 42], []⟩

private def a : MemoryTarget := ⟨⟨0⟩, aFn⟩
private def b : MemoryTarget := ⟨⟨1⟩, bFn⟩
private def leaf : MemoryTarget := ⟨⟨2⟩, leafFn⟩
private def armType : Option NumType := some (.int .i32)
private def callArm : List Graph.Memory32.Op := [getSelector, .ranked (.call callB)]
private def baseArm : List Graph.Memory32.Op := [getSelector]
private def guardTail : List Graph.Memory32.Op := [.store 1, .load 1]
private def guardSaved : List Value := [i32 4, i32 0]
private def guardFn : Graph.Memory32.Function :=
  ⟨declaration, 0, guardSaved ++ [i32 0, i32 word],
    .store 5 :: getSelector :: .if_ armType callArm baseArm :: guardTail⟩
-- Both arms must leave the scalar result, including the skipped arm.
example : ¬ guardFn.WellTyped guardFn.initial
    (.store 5 :: getSelector :: .if_ armType callArm [] :: guardTail) := by
  unfold Graph.Memory32.Function.WellTyped
  decide

private def guarded : MemoryTarget := ⟨⟨6⟩, guardFn⟩

private def branchDecl : Declaration := ⟨moduleAt, ⟨0⟩, signature.params, [.int .i32], signature.results⟩
private def getZero : Graph.Memory32.Op := .ranked (.numeric (.get ⟨1⟩))
private def branchPrefix : List Graph.Memory32.Op := [getZero, getZero, .load 5, getSelector]
private def branchSuffix : List Graph.Memory32.Op := [.store 1, getZero, .load 1]
private def branchArm : List Graph.Memory32.Op :=
  branchPrefix ++ .ranked (.brIf ⟨0⟩ [.int .i32]) :: branchSuffix
private def branchTail : List Graph.Memory32.Op := [.store 1, getZero, .load 5]
private def branchFn : Graph.Memory32.Function :=
  ⟨branchDecl, 0, [i32 4, i32 1, i32 0, i32 word],
    [.store 5, .if_ armType branchArm [getZero]] ++ branchTail⟩
private def branching : MemoryTarget := ⟨⟨7⟩, branchFn⟩

-- A function body starts with a single label.
example : MemoryTarget.supportedOp false (.ranked (.brIf ⟨1⟩ [.int .i32])) = false := rfl

example : MemoryTarget.supportedOp false (.if_ armType
    (branchPrefix ++ .ranked (.brIf ⟨2⟩ [.int .i32]) :: branchSuffix) [getZero]) = false := by decide

-- Even an untaken branch must declare the active label's result signature.
example : ¬ branchFn.WellTyped branchFn.initial
    ([.store 5, .if_ armType
      (branchPrefix ++ .ranked (.brIf ⟨0⟩ [.int .i64]) :: branchSuffix) [getZero]] ++ branchTail) := by
  unfold Graph.Memory32.Function.WellTyped
  decide

private def outerSuffix : List Graph.Memory32.Op := [getZero, .load 5, .store 0, getZero, .load 5]

private def outerArm (depth : LabelIdx) (result : List NumType) : List Graph.Memory32.Op :=
  [getSelector, getZero, .if_ none [] (branchPrefix ++ [.ranked (.brIf depth result), .store 1])] ++ outerSuffix

private def outerFn : Graph.Memory32.Function :=
  { branchFn with code := [.store 5, .if_ armType (outerArm ⟨1⟩ [.int .i32]) [getZero]] ++ branchTail }

private def outerBranching : MemoryTarget := ⟨⟨8⟩, outerFn⟩

-- Depth three is beyond both explicit arms and the implicit function label.
example : MemoryTarget.supportedOp false (.if_ armType (outerArm ⟨3⟩ [.int .i32]) [getZero]) = false := by decide

-- The crossed label is void, but the target requires one i32.
example : ¬ outerFn.WellTyped outerFn.initial
    ([.store 5, .if_ armType (outerArm ⟨1⟩ []) [getZero]] ++ branchTail) := by
  unfold Graph.Memory32.Function.WellTyped
  decide

private def table : Execution.Runtime.TableInst := ⟨[some a.address, some leaf.address, some guarded.address, some branching.address, some outerBranching.address], none⟩

private def site : IndirectSite where
  toSite := ⟨table, ⟨1⟩, signature⟩
  graph := ⟨[]⟩
  memoryFunctions := [some aFn, some bFn, some leafFn, none, none, none, some guardFn, some branchFn, some outerFn]
  memoryCalls := .recursive

private def prepare : Site Nat :=
  ⟨⟨5⟩, ⟨[.int .i64, .int .i32], [.int .i64, .int .i32, .int .i32]⟩, 1⟩
private def saved : List Value := [i64 77]
private def dispatch : List (Continuation.Op Nat) := [.callIndirect site]

private def program : Program Nat where
  module := {
    types := [IndexedLoop.signature, signature, ⟨[.int .i64], [.int .i64, .int .i32]⟩]
    funcs := [⟨4⟩, ⟨5⟩]
    tables := [⟨0⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨3⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨4⟩
  producerCode := 0
  continuation := .call ⟨1⟩ prepare :: dispatch
  saved := 99
  functionIndex := ⟨2⟩
  functionResults := [.int .i64, .int .i32]

private def caller : Frame := ⟨[], { funcs := [⟨3⟩] }⟩
private def base : Store Nat :=
  { memories := [⟨empty, some 1⟩], tables := [table], funcs :=
    [.wasm signature moduleAt a.code, .wasm signature moduleAt b.code, .wasm signature moduleAt leaf.code,
      .wasm program.functionType program.module program.function, .host producerType 0, .host prepare.type 1, .wasm signature moduleAt guarded.code,
      .wasm signature moduleAt branching.code, .wasm signature moduleAt outerBranching.code] }
private def mem : Memory32 base := ⟨⟨0⟩, ⟨empty, some 1⟩, rfl, .fixed⟩
private def host : HostSemantics Nat := fun code store operands outcome =>
  match code with
  | 0 => store = base ∧ operands = [i64 7] ∧
      outcome = .returned base (.values [i32 1, i64 88, i32 0])
  | 1 => store = base ∧ operands = [i64 99, i32 1] ∧ ∃ arg selector : BitVec 32,
      outcome = .returned base (.values (saved ++ [i32 arg, i32 selector]))
  | _ => False

private theorem tableEntries {address : FuncAddr} (member : some address ∈ site.table.refs) :
    address = a.address ∨ address = leaf.address ∨ address = guarded.address ∨ address = branching.address ∨ address = outerBranching.address := by
  simpa [site, table] using member

private theorem registered {callee : MemoryTarget} (found : site.memoryLookup callee.address = some callee.fn) :
    callee = a ∨ callee = b ∨ callee = leaf ∨ callee = guarded ∨ callee = branching ∨ callee = outerBranching := by
  rcases callee with ⟨⟨address⟩, fn⟩
  rcases address with _ | _ | _ | _ | _ | _ | _ | _ | _ | address <;>
    simp_all [IndirectSite.memoryLookup, site, a, b, leaf, guarded, branching, outerBranching]

private theorem outerLinked : site.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro address fn found
    simp [site, Graph.Program.lookup] at found
  · intro address member
    rcases tableEntries member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.wasm signature moduleAt a.code, rfl, fun _ => .inr ⟨aFn, rfl, rfl⟩⟩
    · exact ⟨.wasm signature moduleAt leaf.code, rfl, fun _ => .inr ⟨leafFn, rfl, rfl⟩⟩
    · exact ⟨.wasm signature moduleAt guarded.code, rfl, fun _ => .inr ⟨guardFn, rfl, rfl⟩⟩
    · exact ⟨.wasm signature moduleAt branching.code, rfl, fun _ => .inr ⟨branchFn, rfl, rfl⟩⟩
    · exact ⟨.wasm signature moduleAt outerBranching.code, rfl, fun _ => .inr ⟨outerFn, rfl, rfl⟩⟩

private theorem directLink : site.MemoryDirect (base := base) a callB b := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem guardLink : site.MemoryDirect (base := base) guarded callB b := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem innerLinked : site.MemoryIndirect mem host b ⟨0⟩ ⟨signature.params, signature.results⟩ := by
  refine ⟨rfl, rfl, fun address member => ?_⟩
  rcases tableEntries member with rfl | rfl | rfl | rfl | rfl
  · exact ⟨.wasm signature moduleAt a.code, rfl, fun _ => ⟨aFn, rfl, rfl, trivial⟩⟩
  · exact ⟨.wasm signature moduleAt leaf.code, rfl, fun _ => ⟨leafFn, rfl, rfl, trivial⟩⟩
  · exact ⟨.wasm signature moduleAt guarded.code, rfl, fun _ => ⟨guardFn, rfl, rfl, trivial⟩⟩
  · exact ⟨.wasm signature moduleAt branching.code, rfl, fun _ => ⟨branchFn, rfl, rfl, trivial⟩⟩
  · exact ⟨.wasm signature moduleAt outerBranching.code, rfl, fun _ => ⟨outerFn, rfl, rfl, trivial⟩⟩

private theorem graphLinked : site.MemoryLinked mem host := by
  constructor
  · intro callee found
    rcases registered found with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · intro parent found target used
    rcases registered found with rfl | rfl | rfl | rfl | rfl | rfl
    · have same : target = callB := by
        simpa [a, aFn, getSelector, Graph.Memory32.Function.targets, Graph.Memory32.Op.targets,
          Graph.Op.targets] using used
      subst target
      exact .inl ⟨b, directLink, trivial⟩
    · simp [b, bFn, getSelector, choose, Graph.Memory32.Function.targets, Graph.Memory32.Op.targets,
        Graph.Op.targets] at used
    · simp [leaf, leafFn, Graph.Memory32.Function.targets] at used
    · have same : target = callB := by
        simpa [guarded, guardFn, getSelector, callArm, baseArm, guardTail, Graph.Memory32.Function.targets,
          Graph.Memory32.Op.targets, Graph.Memory32.codeTargets, Graph.Op.targets] using used
      subst target
      exact .inl ⟨b, guardLink, trivial⟩
    · simp [branching, branchFn, branchArm, branchPrefix, branchSuffix, branchTail, getZero, getSelector,
        Graph.Memory32.Function.targets, Graph.Memory32.Op.targets, Graph.Memory32.codeTargets, Graph.Op.targets] at used
    · simp [outerBranching, outerFn, outerArm, outerSuffix, branchPrefix, branchTail, getZero, getSelector,
        Graph.Memory32.Function.targets, Graph.Memory32.Op.targets, Graph.Memory32.codeTargets, Graph.Op.targets] at used
  · intro parent found index ty used
    rcases registered found with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [a, aFn, getSelector, MemoryTarget.sourceOps, MemoryTarget.descendants] at used
    · have same : Graph.Memory32.Op.callIndirect index ty = choose := by
        simpa [b, bFn, getSelector, choose, MemoryTarget.sourceOps, MemoryTarget.descendants] using used
      change Graph.Memory32.Op.callIndirect index ty =
        .callIndirect ⟨0⟩ ⟨signature.params, signature.results⟩ at same
      obtain ⟨rfl, rfl⟩ := Graph.Memory32.Op.callIndirect.inj same
      exact innerLinked
    · simp [leaf, leafFn, MemoryTarget.sourceOps] at used
    · simp [guarded, guardFn, callArm, baseArm, guardTail, getSelector,
        MemoryTarget.sourceOps, MemoryTarget.descendants] at used
    · simp [branching, branchFn, branchArm, branchPrefix, branchSuffix, branchTail, getZero, getSelector,
        MemoryTarget.sourceOps, MemoryTarget.descendants] at used
    · simp [outerBranching, outerFn, outerArm, outerSuffix, branchPrefix, branchTail, getZero, getSelector,
        MemoryTarget.sourceOps, MemoryTarget.descendants] at used

-- The same graph cannot supply the strict admission policy. A's direct site
-- is well linked but its allocated target has the same rank.
example : ¬ site.MemoryLinked mem host .ranked := by
  intro linked
  have used : callB ∈ a.fn.targets := by decide
  rcases linked.direct a rfl callB used with ⟨child, link, rank⟩ | ⟨code, link⟩
  · exact Nat.not_lt_zero _ rank
  · have eq := link.allocated
    change some (.wasm signature moduleAt b.code : FuncInst Wasm.Lime1.Func Nat) =
      some (.host signature code) at eq
    cases eq

private theorem programChecked : program.Checked mem caller ⟨0⟩ := by
  have suffix : Continuation.Checked base program.module [.int .i64] [[.int .i64, .int .i32]]
      [.int .i64, .int .i32] [.int .i64, .int .i32, .int .i32] dispatch :=
    .callIndirect (saved := [.int .i64]) outerLinked .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    .call (site := prepare) (saved := []) rfl (show prepare.Allocated base from rfl) suffix, rfl, rfl⟩

private theorem programContract : program.Contract mem host := by
  have prepared : prepare.Contract mem host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, _, _, eq⟩ := answer
    cases eq
    exact ⟨empty, rfl, rfl, rfl⟩
  have dispatchContract : site.Contract mem host := by
    refine ⟨?_, graphLinked⟩
    intro address code member allocated
    rcases tableEntries member with rfl | rfl | rfl | rfl | rfl
    · cases (show some (.wasm signature moduleAt a.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
    · cases (show some (.wasm signature moduleAt leaf.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
    · cases (show some (.wasm signature moduleAt guarded.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
    · cases (show some (.wasm signature moduleAt branching.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
    · cases (show some (.wasm signature moduleAt outerBranching.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨empty, rfl, rfl, rfl⟩
  · exact .call prepared (.callIndirect dispatchContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program mem host 7) ⟨empty, .source⟩
private abbrev BodyPath (bytes : ByteArray) (phase : Continuation.Phase Nat) :=
  Path ⟨bytes, .continuation phase []⟩

private theorem atDispatch (arg selector : BitVec 32) :
    BodyPath empty (.source ((saved ++ [i32 arg]) ++ [i32 selector]) dispatch) := by
  have producer : Path ⟨empty, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have answered : Edge program mem host 7 ⟨empty, .producerInvoke 7⟩ ⟨empty, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath empty (.source [i64 99, i32 1] program.continuation) :=
    (((producer.tail answered).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have preparing : BodyPath empty (.invoke [] prepare [i64 99, i32 1] dispatch) :=
    exit.tail (.continuation (.resolve (saved := []) (args := [i64 99, i32 1]) rfl))
  exact preparing.tail (.continuation (.returned (vs := saved ++ [i32 arg, i32 selector]) rfl rfl
      ⟨rfl, rfl, arg, selector, rfl⟩))

private theorem atInvoke (selector : BitVec 32) : BodyPath empty (.memory saved site a (.invoke [i32 selector]) []) :=
  (atDispatch selector 0).tail (.continuation (.callIndirect (saved := saved) (args := [i32 selector]) rfl
    (.memory (callee := a) rfl rfl (show a.Allocated base from rfl) rfl)))

private abbrev Position := ByteArray × MemoryCallee.Phase Nat
private def calleeStep (src dst : Position) : Prop :=
  MemoryCallee.Edge mem host site a src.1 src.2 dst.1 dst.2
private abbrev CalleeRun := Relation.ReflTransGen calleeStep

private theorem CalleeRun.advance {src : Position} {bytes nextBytes : ByteArray} {p q : MemoryCallee.Phase Nat}
    (run : CalleeRun src (bytes, p)) (move : MemoryCallee.Edge mem host site a bytes p nextBytes q) :
    CalleeRun src (nextBytes, q) :=
  run.tail move

private def inRoot (q : Position) : State Nat :=
  ⟨q.1, .continuation (.afterMemory saved site a [] q.2) []⟩

private theorem rootStep {src dst : Position} (move : calleeStep src dst) :
    Edge program mem host 7 (inRoot src) (inRoot dst) := by
  rcases src with ⟨bytes, phase⟩
  cases phase <;> try exact .continuation (.memory move)
  case done => cases move

private theorem rootRun {src dst : Position} (start : Path (inRoot src)) (run : CalleeRun src dst) :
    Path (inRoot dst) := by
  induction run with
  | refl => exact start
  | tail _ move ih => exact ih.tail (rootStep move)

private def inB (selector : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .child [i32 selector] [] b phase []

private theorem toChoice (selector : BitVec 32) {before : ByteArray}
    (write : MemoryWrite.EdgeAt before 1 (.store 0 word) (.written written)) :
    CalleeRun (before, .invoke [i32 selector])
      (written, inB selector (.body [i32 selector] [i32 selector, i32 selector] [choose])) := by
  have entered : CalleeRun (before, .invoke [i32 selector]) (before, .body [i32 selector] aFn.initial aFn.code) :=
    Relation.ReflTransGen.single (.enter (callee := a))
  have stored : CalleeRun (before, .invoke [i32 selector])
      (written, .body [i32 selector] [] [getSelector, .ranked (.call callB)]) :=
    entered.advance (.store (saved := []) write)
  have operand : CalleeRun (before, .invoke [i32 selector])
      (written, .body [i32 selector] [i32 selector] [.ranked (.call callB)]) :=
    stored.advance (.get (v := i32 selector) rfl)
  have invoked : CalleeRun (before, .invoke [i32 selector]) (written, inB selector (.invoke [i32 selector])) :=
    operand.advance (.call (saved := []) (operands := [i32 selector]) directLink rfl)
  have inside : CalleeRun (before, .invoke [i32 selector])
      (written, inB selector (.body [i32 selector] [] bFn.code)) :=
    invoked.advance (.child .enter)
  have first : CalleeRun (before, .invoke [i32 selector])
      (written, inB selector (.body [i32 selector] [i32 selector] [getSelector, choose])) :=
    inside.advance (.child (.get (v := i32 selector) rfl))
  exact first.advance (.child (.get (v := i32 selector) rfl))

private theorem firstWrite : MemoryWrite.EdgeAt empty 1 (.store 0 word) (.written written) :=
  MemoryWrite.fact_at (.write 0 word written (by decide))

private def inLeaf (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  inB 1 (.child [i32 1] [] leaf phase [])

-- Selector 1 chooses the base case and resumes both suspended frames with
-- their original operands and the write made before the call.
example : Steps host launch ⟨mem.store written, caller, values [i64 77, i32 42]⟩ := by
  have invoked : CalleeRun (empty, .invoke [i32 1]) (written, inLeaf (.invoke [i32 1])) :=
    (toChoice 1 firstWrite).advance
      (.child (.callIndirect (saved := []) (operands := [i32 1]) (child := leaf) (.memory rfl rfl (show leaf.Allocated base from rfl) rfl) rfl))
  have entered : CalleeRun (empty, .invoke [i32 1]) (written, inLeaf (.body [i32 1] [i32 42] [])) :=
    invoked.advance (.child (.child .enter))
  have leafLabel : CalleeRun (empty, .invoke [i32 1]) (written, inLeaf (.exit [i32 1] (.values [i32 42]))) :=
    entered.advance (.child (.child .labelDone))
  have resumedB : CalleeRun (empty, .invoke [i32 1])
      (written, inB 1 (.body [i32 1] [i32 42] [])) :=
    leafLabel.advance (.child (.child .frameDone))
  have bLabel : CalleeRun (empty, .invoke [i32 1]) (written, inB 1 (.exit [i32 1] (.values [i32 42]))) :=
    resumedB.advance (.child .labelDone)
  have resumedA : CalleeRun (empty, .invoke [i32 1]) (written, .body [i32 1] [i32 42] []) :=
    bLabel.advance (.child .frameDone)
  have aLabel : CalleeRun (empty, .invoke [i32 1]) (written, .exit [i32 1] (.values [i32 42])) :=
    resumedA.advance .labelDone
  have restored : BodyPath written (.source [i64 77, i32 42] []) :=
    rootRun (src := (empty, .invoke [i32 1])) (atInvoke 1) (aLabel.advance .frameDone)
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (restored.tail (.continuation .labelResult)).tail (.continuation .frameDone), rfl, rfl⟩

private def insideCycle (q : Position) : Position :=
  (q.1, MemoryCallee.afterChild [i32 0] [] b [] (MemoryCallee.afterChild [i32 0] [] a [] q.2))

private theorem cycleStep {src dst : Position} (move : calleeStep src dst) :
    calleeStep (insideCycle src) (insideCycle dst) := by
  rcases src with ⟨bytes, phase⟩
  rcases dst with ⟨nextBytes, next⟩
  cases phase <;> try exact .child (.child move)
  case done => cases move

private theorem underCycle {src dst : Position} (run : CalleeRun src dst) :
    CalleeRun (insideCycle src) (insideCycle dst) := by
  induction run with
  | refl => exact .refl
  | tail _ move ih => exact ih.tail (cycleStep move)

private theorem oneCycle {before : ByteArray}
    (write : MemoryWrite.EdgeAt before 1 (.store 0 word) (.written written)) :
    CalleeRun (before, .invoke [i32 0]) (insideCycle (written, .invoke [i32 0])) :=
  (toChoice 0 write).advance
    (.child (.callIndirect (saved := []) (operands := [i32 0]) (child := a) (.memory rfl rfl (show a.Allocated base from rfl) rfl) rfl))

private def pendingAgain : Nat → Position
  | 0 => (written, .invoke [i32 0])
  | n + 1 => insideCycle (pendingAgain n)

private theorem repeatCycle (n : Nat) : CalleeRun (written, .invoke [i32 0]) (pendingAgain n) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    exact (oneCycle (MemoryWrite.fact_at (.write 0 word written (by decide)))).trans (underCycle ih)

-- Selector 0 revisits A. For each finite depth, the exact native endpoint
-- has another pending A invocation, suspended A/B frames and the live write.
example (n : Nat) : Steps host launch (program.render mem caller ⟨0⟩ 7 (inRoot (pendingAgain (n + 1)))) := by
  have reached := rootRun (src := (empty, .invoke [i32 0])) (atInvoke 0) ((oneCycle firstWrite).trans (underCycle (repeatCycle n)))
  have bytes (k : Nat) : (pendingAgain k).1 = written := by
    induction k with
    | zero => rfl
    | succ k ih => exact ih
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, reached, by change mem.Live (pendingAgain (n + 1)).1; rw [bytes]; rfl, rfl⟩

private def beforeGuard : ByteArray := ⟨#[0, 0, 0, 0, 0, 1, 2, 3, 4, 0]⟩
private def returnedGuard : ByteArray := ⟨#[0, 42, 0, 0, 0, 1, 2, 3, 4, 0]⟩

private abbrev GuardPath (bytes : ByteArray) (phase : MemoryCallee.Phase Nat) :=
  BodyPath bytes (.memory saved site guarded phase [])

private theorem GuardPath.step {bytes nextBytes : ByteArray} {p q : MemoryCallee.Phase Nat}
    (path : GuardPath bytes p) (move : MemoryCallee.Edge mem host site guarded bytes p nextBytes q) :
    BodyPath nextBytes (.afterMemory saved site guarded [] q) :=
  path.tail (.continuation (.memory move))

private theorem atBlock (guard : BitVec 32) :
    GuardPath beforeGuard (.ifBlock [i32 guard] guardSaved armType
      (MemoryCallee.selectArm guard callArm baseArm) guardTail) := by
  have invocation : GuardPath empty (.invoke [i32 guard]) :=
    (atDispatch guard 2).tail (.continuation (.callIndirect (saved := saved) (args := [i32 guard]) rfl
      (.memory (callee := guarded) rfl rfl (show guarded.Allocated base from rfl) rfl)))
  have entered : GuardPath empty (.body [i32 guard] guardFn.initial guardFn.code) :=
    invocation.step .enter
  have stored : GuardPath beforeGuard (.body [i32 guard] guardSaved
      [getSelector, .if_ armType callArm baseArm, .store 1, .load 1]) :=
    entered.step (.store (saved := guardSaved) (MemoryWrite.fact_at (.write 0 word beforeGuard (by decide))))
  have tested : GuardPath beforeGuard (.body [i32 guard] (guardSaved ++ [i32 guard])
      (.if_ armType callArm baseArm :: guardTail)) := stored.step (.get (v := i32 guard) rfl)
  exact tested.step .ifSelect

private def inGuard (guard : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .arm [i32 guard] guardSaved armType phase guardTail

private theorem guardOpen (guard : BitVec 32) :
    GuardPath beforeGuard (inGuard guard (.body [i32 guard] [] (MemoryCallee.selectArm guard callArm baseArm))) :=
  (atBlock guard).step .ifEnter

-- The native prefix ends after selection and still contains a source block.
example : Steps host launch ⟨mem.store beforeGuard, caller, program.functionCode 7
    (values saved ++ MemoryWrite.limeActivationCode 1 (declaration.frame [i32 0]) [] []
      (values guardSaved ++ [.source (.block (MemoryCallee.blockType armType) (MemoryCallee.expr baseArm))] ++
        MemoryCallee.code guardTail))⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, atBlock 0, rfl, rfl⟩

private theorem finishGuard {bits : BitVec 32} {bytes : ByteArray} {guard : BitVec 32}
    (resumed : GuardPath beforeGuard (.body [i32 guard] (guardSaved ++ [i32 bits]) guardTail))
    (write : MemoryWrite.EdgeAt beforeGuard 1 (.store 0 bits) (.written bytes))
    (read : MemoryQuery.EdgeAt bytes 1 (.load 4) (.value word)) (live : mem.Live bytes) :
    Steps host launch ⟨mem.store bytes, caller, values [i64 77, i32 word]⟩ := by
  have stored : GuardPath bytes (.body [i32 guard] [i32 4] [.load 1]) :=
    resumed.step (.store (saved := [i32 4]) write)
  have loaded : GuardPath bytes (.body [i32 guard] [i32 word] []) :=
    stored.step (.load (saved := []) read)
  have label : GuardPath bytes (.exit [i32 guard] (.values [i32 word])) := loaded.step .labelDone
  have restored : BodyPath bytes (.source [i64 77, i32 word] []) := label.step .frameDone
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (restored.tail (.continuation .labelResult)).tail (.continuation .frameDone), live, rfl⟩

-- The zero arm runs no call. Its scalar result reaches the shared suffix.
example : Steps host launch ⟨mem.store beforeGuard, caller, values [i64 77, i32 word]⟩ := by
  have opened : GuardPath beforeGuard (inGuard 0 (.body [i32 0] [] baseArm)) := guardOpen 0
  have read : GuardPath beforeGuard (inGuard 0 (.body [i32 0] [i32 0] [])) :=
    opened.step (.armStep rfl (.get (v := i32 0) rfl))
  exact finishGuard (read.step (.armStep rfl .labelDone))
    (MemoryWrite.fact_at (.write 0 0 beforeGuard (by decide)))
    (MemoryQuery.fact_at (.load 4 word (by decide))) rfl

private def inGuardB (guard : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  inGuard guard (.child [i32 guard] [] b phase [])

private theorem atGuardChoice (guard : BitVec 32) (nonzero : guard ≠ 0) :
    GuardPath beforeGuard (inGuardB guard (.body [i32 guard] [i32 guard, i32 guard] [choose])) := by
  have opened : GuardPath beforeGuard (inGuard guard (.body [i32 guard] [] callArm)) := by
    have chosen : MemoryCallee.selectArm guard callArm baseArm = callArm := ite_eq_right nonzero
    simpa only [chosen] using guardOpen guard
  have read : GuardPath beforeGuard (inGuard guard (.body [i32 guard] [i32 guard] [.ranked (.call callB)])) :=
    opened.step (.armStep rfl (.get (v := i32 guard) rfl))
  have invoked : GuardPath beforeGuard (inGuardB guard (.invoke [i32 guard])) :=
    read.step (.armStep rfl (.call (saved := []) (operands := [i32 guard]) guardLink rfl))
  have entered : GuardPath beforeGuard (inGuardB guard (.body [i32 guard] [] bFn.code)) :=
    invoked.step (.armStep rfl (.child .enter))
  have first : GuardPath beforeGuard (inGuardB guard (.body [i32 guard] [i32 guard] [getSelector, choose])) :=
    entered.step (.armStep rfl (.child (.get (v := i32 guard) rfl)))
  exact first.step (.armStep rfl (.child (.get (v := i32 guard) rfl)))

private def inGuardLeaf (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  inGuardB 1 (.child [i32 1] [] leaf phase [])

-- The nonzero arm makes the call and returns through its explicit label.
example : Steps host launch ⟨mem.store returnedGuard, caller, values [i64 77, i32 word]⟩ := by
  have invocation : GuardPath beforeGuard (inGuardLeaf (.invoke [i32 1])) :=
    (atGuardChoice 1 (by decide)).step (.armStep rfl (.child
      (.callIndirect (saved := []) (operands := [i32 1]) (child := leaf)
        (.memory rfl rfl (show leaf.Allocated base from rfl) rfl) rfl)))
  have entered : GuardPath beforeGuard (inGuardLeaf (.body [i32 1] [i32 42] [])) :=
    invocation.step (.armStep rfl (.child (.child .enter)))
  have leafLabel : GuardPath beforeGuard (inGuardLeaf (.exit [i32 1] (.values [i32 42]))) :=
    entered.step (.armStep rfl (.child (.child .labelDone)))
  have bBody : GuardPath beforeGuard (inGuardB 1 (.body [i32 1] [i32 42] [])) :=
    leafLabel.step (.armStep rfl (.child (.child .frameDone)))
  have bLabel : GuardPath beforeGuard (inGuardB 1 (.exit [i32 1] (.values [i32 42]))) :=
    bBody.step (.armStep rfl (.child .labelDone))
  have armBody : GuardPath beforeGuard (inGuard 1 (.body [i32 1] [i32 42] [])) :=
    bLabel.step (.armStep rfl (.child .frameDone))
  exact finishGuard (armBody.step (.armStep rfl .labelDone))
    (MemoryWrite.fact_at (.write 0 42 returnedGuard (by decide)))
    (MemoryQuery.fact_at (.load 4 word (by decide))) rfl

-- A trap in the selected callee skips the join and keeps the write before the if.
example : Steps host launch ⟨mem.store beforeGuard, caller, [.trap]⟩ := by
  have trapped : GuardPath beforeGuard (inGuardB (-1) (.trapped [i32 (-1)] [i32 (-1)] [])) :=
    (atGuardChoice (-1) (by decide)).step (.armStep rfl (.child
      (.indirectTrap (stack := [i32 (-1)]) (index := ⟨0⟩)
        (signature := ⟨signature.params, signature.results⟩) (selector := -1) (.bounds rfl))))
  have erased : GuardPath beforeGuard (inGuardB (-1) (.trapped [i32 (-1)] [] [])) :=
    trapped.step (.armStep rfl (.child (.erase (removed := [i32 (-1)]) (cut := []) rfl rfl (.inl (by simp)))))
  have bLabel : GuardPath beforeGuard (inGuardB (-1) (.exit [i32 (-1)] .trap)) :=
    erased.step (.armStep rfl (.child .labelTrap))
  have armTrap : GuardPath beforeGuard (inGuard (-1) (.trapped [i32 (-1)] [] [])) :=
    bLabel.step (.armStep rfl (.child .frameDone))
  have trappedGuard : GuardPath beforeGuard (.trapped [i32 (-1)] guardSaved (MemoryCallee.code guardTail)) :=
    armTrap.step (.armStep rfl .labelTrap)
  have cleaned : GuardPath beforeGuard (.trapped [i32 (-1)] [] []) :=
    trappedGuard.step (.erase (removed := guardSaved) (cut := MemoryCallee.code guardTail)
      rfl rfl (.inl (by simp [guardSaved])))
  have guardLabel : GuardPath beforeGuard (.exit [i32 (-1)] .trap) :=
    cleaned.step .labelTrap
  have outer : BodyPath beforeGuard (.trapped saved []) := guardLabel.step .frameDone
  have discarded : BodyPath beforeGuard (.trapped [] []) :=
    outer.tail (.continuation (.erase (removed := saved) (cut := []) rfl rfl (.inl (by simp [saved]))))
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (discarded.tail (.continuation .labelTrap)).tail (.continuation .frameDone), rfl, rfl⟩

private abbrev BranchPath (bytes : ByteArray) (phase : MemoryCallee.Phase Nat) (target : MemoryTarget := branching) :=
  BodyPath bytes (.memory saved site target phase [])

private theorem BranchPath.step {target : MemoryTarget} {bytes nextBytes : ByteArray} {p q : MemoryCallee.Phase Nat}
    (path : BranchPath bytes p target) (move : MemoryCallee.Edge mem host site target bytes p nextBytes q) :
    BodyPath nextBytes (.afterMemory saved site target [] q) :=
  path.tail (.continuation (.memory move))

private def inBranchArm (guard : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .arm [i32 guard] [i32 4] armType phase branchTail

private theorem atBranch (guard : BitVec 32) :
    BranchPath beforeGuard (inBranchArm guard (.body [i32 guard] [i32 0, i32 word, i32 guard]
      (.ranked (.brIf ⟨0⟩ [.int .i32]) :: branchSuffix))) := by
  have invocation : BranchPath empty (.invoke [i32 guard]) :=
    (atDispatch guard 3).tail (.continuation (.callIndirect (saved := saved) (args := [i32 guard]) rfl
      (.memory (callee := branching) rfl rfl (show branching.Allocated base from rfl) rfl)))
  have entered : BranchPath empty (.body [i32 guard] branchFn.initial branchFn.code) := invocation.step .enter
  have stored : BranchPath beforeGuard (.body [i32 guard] [i32 4, i32 1]
      (.if_ armType branchArm [getZero] :: branchTail)) :=
    entered.step (.store (saved := [i32 4, i32 1]) (MemoryWrite.fact_at (.write 0 word beforeGuard (by decide))))
  have selected : BranchPath beforeGuard (.ifBlock [i32 guard] [i32 4] armType
      (MemoryCallee.selectArm 1 branchArm [getZero]) branchTail) :=
    stored.step (.ifSelect (saved := [i32 4]) (type := armType) (left := branchArm)
      (right := [getZero]) (rest := branchTail) (guard := 1))
  have chosen : MemoryCallee.selectArm 1 branchArm [getZero] = branchArm := rfl
  have opened : BranchPath beforeGuard (inBranchArm guard (.body [i32 guard] [] branchArm)) :=
    (show BranchPath beforeGuard (.ifBlock [i32 guard] [i32 4] armType branchArm branchTail) from
      chosen ▸ selected).step .ifEnter
  have scratch : BranchPath beforeGuard (inBranchArm guard (.body [i32 guard] [i32 0]
      ([getZero, .load 5, getSelector, .ranked (.brIf ⟨0⟩ [.int .i32])] ++ branchSuffix))) :=
    opened.step (.armStep rfl (.get (v := i32 0) rfl))
  have address : BranchPath beforeGuard (inBranchArm guard (.body [i32 guard] [i32 0, i32 0]
      ([.load 5, getSelector, .ranked (.brIf ⟨0⟩ [.int .i32])] ++ branchSuffix))) :=
    scratch.step (.armStep rfl (.get (v := i32 0) rfl))
  have loaded : BranchPath beforeGuard (inBranchArm guard (.body [i32 guard] [i32 0, i32 word]
      ([getSelector, .ranked (.brIf ⟨0⟩ [.int .i32])] ++ branchSuffix))) :=
    address.step (.armStep rfl (.load (saved := [i32 0]) (MemoryQuery.fact_at (.load 0 word (by decide)))))
  exact loaded.step (.armStep rfl (.get (v := i32 guard) rfl))

private theorem finishBranch {guard : BitVec 32} {bytes : ByteArray} {target : MemoryTarget}
    (decl : target.fn.declaration = branchDecl)
    (start : BranchPath bytes (.body [i32 guard] [i32 4, i32 word] branchTail) target)
    (write : MemoryWrite.EdgeAt bytes 1 (.store 4 word) (.written bytes))
    (read : MemoryQuery.EdgeAt bytes 5 (.load 0) (.value word)) (live : mem.Live bytes) :
    Steps host launch ⟨mem.store bytes, caller, values [i64 77, i32 word]⟩ := by
  have stored : BranchPath bytes (.body [i32 guard] [] [getZero, .load 5]) target := start.step (.store (saved := []) write)
  have address : BranchPath bytes (.body [i32 guard] [i32 0] [.load 5]) target := stored.step (.get (v := i32 0) (by rw [decl]; rfl))
  have loaded : BranchPath bytes (.body [i32 guard] [i32 word] []) target := address.step (.load (saved := []) read)
  have label : BranchPath bytes (.exit [i32 guard] (.values [i32 word])) target := loaded.step .labelDone
  have restored : BodyPath bytes (.source [i64 77, i32 word] []) := label.step .frameDone
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (restored.tail (.continuation .labelResult)).tail (.continuation .frameDone), live, rfl⟩

private theorem pendingBranch :
    BranchPath beforeGuard (inBranchArm 1 (.branch [i32 1] [i32 0, i32 word] ⟨0⟩ [.int .i32] branchSuffix)) :=
  (atBranch 1).step (.armStep rfl (.brIf (stack := [i32 0, i32 word]) (rest := branchSuffix) (result := [.int .i32]) (guard := 1)))

-- This prefix still contains the native br and the active scratch operand.
example : Steps host launch ⟨mem.store beforeGuard, caller, program.functionCode 7
    (values saved ++ MemoryWrite.limeActivationCode 1 (branchDecl.frame [i32 1]) [] []
      (values [i32 4] ++ [.label 1 [] (values [i32 0, i32 word] ++
        .source (.br ⟨0⟩) :: MemoryCallee.code branchSuffix)] ++ MemoryCallee.code branchTail))⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, pendingBranch, rfl, rfl⟩

-- Taken: only the payload reaches the saved address. The arm store is skipped.
example : Steps host launch ⟨mem.store beforeGuard, caller, values [i64 77, i32 word]⟩ :=
  finishBranch (guard := 1) rfl (pendingBranch.step
    (.armStep rfl (.branchDone (scratch := [i32 0]) (payload := [i32 word]) rfl)))
    (MemoryWrite.fact_at (.write 4 word beforeGuard (by decide)))
    (MemoryQuery.fact_at (.load 0 word (by decide))) rfl

private def afterFallthrough : ByteArray := ⟨#[0, 1, 2, 3, 4, 1, 2, 3, 4, 0]⟩

-- Untaken: the arm store uses the scratch address and the payload, then
-- the normal label delivers the reloaded result through the same join.
example : Steps host launch ⟨mem.store afterFallthrough, caller, values [i64 77, i32 word]⟩ := by
  have fell : BranchPath beforeGuard (inBranchArm 0 (.body [i32 0] [i32 0, i32 word] branchSuffix)) :=
    (atBranch 0).step (.armStep rfl (.brIf (stack := [i32 0, i32 word]) (rest := branchSuffix) (result := [.int .i32]) (guard := 0)))
  have stored : BranchPath afterFallthrough (inBranchArm 0 (.body [i32 0] [] [getZero, .load 1])) :=
    fell.step (.armStep rfl (.store (saved := []) (MemoryWrite.fact_at (.write 0 word afterFallthrough (by decide)))))
  have address : BranchPath afterFallthrough (inBranchArm 0 (.body [i32 0] [i32 0] [.load 1])) :=
    stored.step (.armStep rfl (.get (v := i32 0) rfl))
  have loaded : BranchPath afterFallthrough (inBranchArm 0 (.body [i32 0] [i32 word] [])) :=
    address.step (.armStep rfl (.load (saved := []) (MemoryQuery.fact_at (.load 0 word (by decide)))))
  exact finishBranch (guard := 0) rfl (loaded.step (.armStep rfl .labelDone))
    (MemoryWrite.fact_at (.write 4 word afterFallthrough (by decide)))
    (MemoryQuery.fact_at (.load 0 word (by decide))) rfl

private abbrev OuterPath (bytes : ByteArray) (phase : MemoryCallee.Phase Nat) :=
  BranchPath bytes phase outerBranching

private def inOuter (guard : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .arm [i32 guard] [i32 4] armType phase branchTail

private def inInner (guard : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  inOuter guard (.arm [i32 guard] [i32 guard] none phase outerSuffix)

private def innerBranch : Graph.Memory32.Op := .ranked (.brIf ⟨1⟩ [.int .i32])
private def innerArm : List Graph.Memory32.Op := branchPrefix ++ [innerBranch, .store 1]

private theorem atOuterBranch (guard : BitVec 32) :
    OuterPath beforeGuard (inInner guard (.body [i32 guard] [i32 0, i32 word, i32 guard] [innerBranch, .store 1])) := by
  have invocation : OuterPath empty (.invoke [i32 guard]) :=
    (atDispatch guard 4).tail (.continuation (.callIndirect (saved := saved) (args := [i32 guard]) rfl
      (.memory (callee := outerBranching) rfl rfl (show outerBranching.Allocated base from rfl) rfl)))
  have entered : OuterPath empty (.body [i32 guard] outerFn.initial outerFn.code) := invocation.step .enter
  have stored : OuterPath beforeGuard (.body [i32 guard] [i32 4, i32 1]
      (.if_ armType (outerArm ⟨1⟩ [.int .i32]) [getZero] :: branchTail)) :=
    entered.step (.store (saved := [i32 4, i32 1]) (MemoryWrite.fact_at (.write 0 word beforeGuard (by decide))))
  have block : OuterPath beforeGuard (.ifBlock [i32 guard] [i32 4] armType (outerArm ⟨1⟩ [.int .i32]) branchTail) :=
    stored.step (.ifSelect (saved := [i32 4]) (type := armType) (left := outerArm ⟨1⟩ [.int .i32])
      (right := [getZero]) (rest := branchTail) (guard := 1))
  have outer : OuterPath beforeGuard (inOuter guard (.body [i32 guard] [] (outerArm ⟨1⟩ [.int .i32]))) :=
    block.step .ifEnter
  have withSaved : OuterPath beforeGuard (inOuter guard
      (.body [i32 guard] [i32 guard] (getZero :: .if_ none [] innerArm :: outerSuffix))) :=
    outer.step (.armStep rfl (.get (v := i32 guard) rfl))
  have test : OuterPath beforeGuard (inOuter guard
      (.body [i32 guard] [i32 guard, i32 0] (.if_ none [] innerArm :: outerSuffix))) :=
    withSaved.step (.armStep rfl (.get (v := i32 0) rfl))
  have innerBlock : OuterPath beforeGuard (inOuter guard (.ifBlock [i32 guard] [i32 guard] none innerArm outerSuffix)) :=
    test.step (.armStep rfl (.ifSelect (saved := [i32 guard]) (type := none) (left := [])
      (right := innerArm) (rest := outerSuffix) (guard := 0)))
  have opened : OuterPath beforeGuard (inInner guard (.body [i32 guard] [] innerArm)) :=
    innerBlock.step (.armStep rfl .ifEnter)
  have scratch : OuterPath beforeGuard
      (inInner guard (.body [i32 guard] [i32 0] [getZero, .load 5, getSelector, innerBranch, .store 1])) :=
    opened.step (.armStep rfl (.armStep rfl (.get (v := i32 0) rfl)))
  have address : OuterPath beforeGuard
      (inInner guard (.body [i32 guard] [i32 0, i32 0] [.load 5, getSelector, innerBranch, .store 1])) :=
    scratch.step (.armStep rfl (.armStep rfl (.get (v := i32 0) rfl)))
  have loaded : OuterPath beforeGuard
      (inInner guard (.body [i32 guard] [i32 0, i32 word] [getSelector, innerBranch, .store 1])) :=
    address.step (.armStep rfl (.armStep rfl
      (.load (saved := [i32 0]) (MemoryQuery.fact_at (.load 0 word (by decide))))))
  exact loaded.step (.armStep rfl (.armStep rfl (.get (v := i32 guard) rfl)))

private theorem pendingDepthOne :
    OuterPath beforeGuard (inInner 1 (.branch [i32 1] [i32 0, i32 word] ⟨1⟩ [.int .i32] [.store 1])) :=
  (atOuterBranch 1).step (.armStep rfl (.armStep rfl
    (.brIf (stack := [i32 0, i32 word]) (depth := ⟨1⟩) (result := [.int .i32]) (rest := [.store 1]) (guard := 1))))

-- After the guard step the native branch is still inside the void label.
example : Steps host launch ⟨mem.store beforeGuard, caller, program.functionCode 7
    (values saved ++ MemoryWrite.limeActivationCode 1 (branchDecl.frame [i32 1]) [] []
      (values [i32 4] ++ [.label 1 [] (values [i32 1] ++ [.label 0 []
        (values [i32 0, i32 word] ++ .source (.br ⟨1⟩) :: MemoryCallee.code [.store 1])] ++
        MemoryCallee.code outerSuffix)] ++ MemoryCallee.code branchTail))⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, pendingDepthOne, rfl, rfl⟩

private theorem pendingOuter :
    OuterPath beforeGuard (inOuter 1 (.branch [i32 1] [i32 1, i32 0, i32 word] ⟨0⟩ [.int .i32] outerSuffix)) :=
  pendingDepthOne.step (.armStep rfl (.armStep rfl (.branchLower (by decide))))

-- The next native step drops the inner suffix and leaves the outer operands
-- and code in place. Delivery and outer cleanup still have to step.
example : Steps host launch ⟨mem.store beforeGuard, caller, program.functionCode 7
    (values saved ++ MemoryWrite.limeActivationCode 1 (branchDecl.frame [i32 1]) [] []
      (values [i32 4] ++ [.label 1 [] (values [i32 1, i32 0, i32 word] ++
        .source (.br ⟨0⟩) :: MemoryCallee.code outerSuffix)] ++ MemoryCallee.code branchTail))⟩ :=
  (call_run_iff (arg := 7) programChecked programContract).mpr ⟨_, pendingOuter, rfl, rfl⟩

-- Only the i32 payload reaches the outer join. Both skipped stores would
-- change the final bytes, while the joined store uses the saved address.
example : Steps host launch ⟨mem.store beforeGuard, caller, values [i64 77, i32 word]⟩ :=
  finishBranch (target := outerBranching) (guard := 1) rfl (pendingOuter.step
    (.armStep rfl (.branchDone (scratch := [i32 1, i32 0]) (payload := [i32 word]) rfl)))
    (MemoryWrite.fact_at (.write 4 word beforeGuard (by decide)))
    (MemoryQuery.fact_at (.load 0 word (by decide))) rfl

private def afterOuterFallthrough : ByteArray := ⟨#[1, 2, 3, 4, 4, 1, 2, 3, 4, 0]⟩

example : Steps host launch ⟨mem.store afterOuterFallthrough, caller, values [i64 77, i32 word]⟩ := by
  have fallthrough : OuterPath beforeGuard (inInner 0 (.body [i32 0] [i32 0, i32 word] [.store 1])) :=
    (atOuterBranch 0).step (.armStep rfl (.armStep rfl
      (.brIf (stack := [i32 0, i32 word]) (depth := ⟨1⟩) (result := [.int .i32]) (rest := [.store 1]) (guard := 0))))
  have inner : OuterPath afterFallthrough (inInner 0 (.body [i32 0] [] [])) :=
    fallthrough.step (.armStep rfl (.armStep rfl (.store (saved := [])
      (MemoryWrite.fact_at (.write 0 word afterFallthrough (by decide))))))
  have resumed : OuterPath afterFallthrough (inOuter 0 (.body [i32 0] [i32 0] outerSuffix)) :=
    inner.step (.armStep rfl (.armStep rfl .labelDone))
  have address : OuterPath afterFallthrough
      (inOuter 0 (.body [i32 0] [i32 0, i32 0] [.load 5, .store 0, getZero, .load 5])) :=
    resumed.step (.armStep rfl (.get (v := i32 0) rfl))
  have payload : OuterPath afterFallthrough
      (inOuter 0 (.body [i32 0] [i32 0, i32 word] [.store 0, getZero, .load 5])) :=
    address.step (.armStep rfl (.load (saved := [i32 0]) (MemoryQuery.fact_at (.load 0 word (by decide)))))
  have stored : OuterPath afterOuterFallthrough (inOuter 0 (.body [i32 0] [] [getZero, .load 5])) :=
    payload.step (.armStep rfl (.store (saved := [])
      (MemoryWrite.fact_at (.write 0 word afterOuterFallthrough (by decide)))))
  have address : OuterPath afterOuterFallthrough (inOuter 0 (.body [i32 0] [i32 0] [.load 5])) :=
    stored.step (.armStep rfl (.get (v := i32 0) rfl))
  have loaded : OuterPath afterOuterFallthrough (inOuter 0 (.body [i32 0] [i32 word] [])) :=
    address.step (.armStep rfl (.load (saved := []) (MemoryQuery.fact_at (.load 0 word (by decide)))))
  exact finishBranch (target := outerBranching) (guard := 0) rfl (loaded.step (.armStep rfl .labelDone))
    (MemoryWrite.fact_at (.write 4 word afterOuterFallthrough (by decide)))
    (MemoryQuery.fact_at (.load 0 word (by decide))) rfl

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.CycleExamples
