module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Entry.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr HostOutcome MemAddr MemInst ModuleInst Value)
open Computed
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64

private def slot : MemAddr := ⟨0⟩
private def rootAddr : FuncAddr := ⟨1⟩
private def childAddr : FuncAddr := ⟨2⟩
private def hostType : Wasm.V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩
private def site : HostCall.V1.Site Nat := ⟨⟨0⟩, ⟨0⟩, hostType, 17⟩
private def numericType : Wasm.V1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def child : Function :=
  ⟨⟨{ memories := [slot], types := [numericType] }, ⟨0⟩, numericType.params, [], numericType.results⟩, 0, [],
    [.ranked (.numeric (.get ⟨0⟩))]⟩
private def childTarget : CallTarget := ⟨⟨1⟩, childAddr, child.declaration⟩
private def mod : ModuleInst := { funcs := [site.address, childAddr], memories := [slot], types := [hostType] }
private def fn : Function :=
  ⟨⟨mod, ⟨0⟩, hostType.params, [.int .i32], hostType.results⟩, 1, [i32 0],
    [.ranked (.set ⟨2⟩), .load 1, .ranked (.call childTarget)]⟩

private def operands (traps : Bool) : List Prefix.Op :=
  [.get ⟨0⟩, .get ⟨1⟩] ++ (if traps then [.get ⟨2⟩, .bin .i32 (.div .unsigned)] else [])

private def entry (traps : Bool) : HostEntry Nat := ⟨⟨0⟩, rootAddr, fn, operands traps, site⟩
private def graph : Program := ⟨[none, none, some child], none⟩
private def args : List Value := [i64 81, i32 9]
private def caller : Frame := ⟨[i32 42], { funcs := [rootAddr] }⟩
private def initial : MemInst := ⟨⟨#[0xa5, 0x12, 0x22, 0x32, 0x42, 0x5a]⟩, none⟩
private def written : ByteArray := ⟨#[0xa5, 0x44, 0x33, 0x22, 0x11, 0x5a]⟩
private def base (traps : Bool) : Store Nat :=
  { funcs := [.host hostType 17, .wasm fn.declaration.type mod (entry traps).v1Func,
      .wasm child.declaration.type child.declaration.module child.v1Func], memories := [initial] }
private def live (traps : Bool) := storeWithBytes (base traps) slot initial initial.data
private def changed (traps : Bool) := storeWithBytes (base traps) slot initial written

private theorem sourceChecked (traps : Bool) :
    (entry traps).Checked .fixed graph slot .ranked (base traps) caller args where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by cases traps <;> decide
  slot := rfl
  linkedHost := rfl
  allocatedHost := rfl
  scalarHost := by cases traps <;> decide
  typedBody := by cases traps <;> rfl
  supportedTail := rfl
  linkedTail := by
    intro target used
    have only : target ∈ [childTarget] := used
    obtain rfl := List.mem_singleton.mp only
    exact ⟨child, rfl, rfl, rfl, by show 0 < 1; decide⟩

private theorem layout (traps : Bool) : Layout graph (base traps) slot initial where
  memory := rfl
  functions := by
    intro address callee found
    rcases address with ⟨_ | _ | _ | _⟩ <;> simp [graph, Program.lookup] at found
    subst callee
    rfl

private inductive Outcome (traps : Bool) : HostOutcome Wasm.V1.Func Nat → Prop where
  | values : Outcome traps (.returned (changed traps) (.values [i32 7]))
  | trap : Outcome traps (.returned (changed traps) .trap)
  | diverges : Outcome traps .diverged

private def host (traps : Bool) : HostSemantics Nat :=
  fun tag s given answer => tag = 17 ∧ s = live traps ∧ given = args ∧ Outcome traps answer

private theorem hostContract (traps : Bool) :
    (entry traps).Contract (host traps) .fixed slot initial (live traps) := by
  rintro _ _ _ r ⟨_, _, _, returned⟩
  have storeEffect : HostStoreEffect .fixed slot initial (live traps) (changed traps) :=
    ⟨initial.data, written, rfl, rfl, rfl⟩
  cases returned
  · exact ⟨rfl, storeEffect⟩
  · exact ⟨trivial, storeEffect⟩

private abbrev PhaseEdge (traps : Bool) :=
  (entry traps).Edge (host traps) .fixed graph slot (base traps) initial initial.data caller args

private abbrev PhaseRuns (traps : Bool) :=
  (entry traps).Runs (host traps) .fixed graph slot (base traps) initial initial.data caller args

private abbrev cfg (traps : Bool) := (entry traps).render (base traps) slot initial initial.data caller args

private def source (traps : Bool) : Config Nat :=
  ⟨live traps, caller, values [i64 81, i32 9] ++ [.source (.call ⟨0⟩)]⟩

private theorem corresponds (traps : Bool) {dst : Config Nat} :
    Steps (host traps) (source traps) dst ↔
      ∃ next, PhaseRuns traps .call next ∧
        (entry traps).Ready .fixed graph slot .ranked initial args next ∧ dst = cfg traps next :=
  HostEntry.v1_call_run_iff rfl (sourceChecked traps) (layout traps) trivial rfl (hostContract traps)

private theorem native (traps : Bool) {phase : HostEntry.Phase} (run : PhaseRuns traps .call phase) :
    Steps (host traps) (source traps) (cfg traps phase) := by
  apply (corresponds traps).mpr
  refine ⟨phase, run, ?_, rfl⟩
  induction run with
  | refl => trivial
  | tail _ edge ih => exact edge.ready rfl (sourceChecked traps) (layout traps) rfl (hostContract traps) ih

private def saved : List Value := [i32 0]

private theorem readsParams (traps : Bool) : PhaseRuns traps .call
    (.computing (saved ++ args) (if traps then [.get ⟨2⟩, .bin .i32 (.div .unsigned)] else [])) := by
  have entered : PhaseRuns traps .call (.computing fn.initial (operands traps)) :=
    (Relation.ReflTransGen.single .resolve).tail .enter
  cases traps
  · exact (entered.tail (.numeric (.get rfl))).tail (.numeric (.get rfl))
  · exact (entered.tail (.numeric (.get rfl))).tail (.numeric (.get rfl))

private theorem pending : PhaseRuns false .call (.pending saved args) :=
  (readsParams false).tail (.hostResolve rfl)

-- Entry carries the typed mixed-width values through the two native
-- resolver steps and the function's own parameter reads.
example : Steps (host false) (source false)
    ⟨live false, caller, [.frame 1 (fn.declaration.frame args)
      [.label 1 [] (values (saved ++ args) ++ .invoke site.address :: (entry false).tail)]]⟩ :=
  native false pending

example :=
  (corresponds false).mp (native false (pending.tail (.diverged ⟨rfl, rfl, rfl, .diverges⟩)))

private def active := fn.declaration.frame args
private def recorded : Frame := { active with locals := args ++ [i32 7] }
private def tail := (entry false).tail

private def framed (s : Store Nat) (f : Frame) (body : List Admin) : Config Nat :=
  ⟨s, caller, [.frame 1 f [.label 1 [] body]]⟩

private theorem delivered {r : Execution.Runtime.Result} (answer : Outcome false (.returned (changed false) r)) :
    Step (host false) (cfg false (.pending saved args)) (framed (changed false) active (values saved ++ result r ++ tail)) :=
  .frame (.label (.context
    (.invokeHost (live false) (changed false) active site.address hostType 17 args r
      rfl rfl ⟨rfl, rfl, rfl, answer⟩) saved tail) 1 []) 1 caller

private def observed : Config Nat := ⟨changed false, caller, values [i32 0x11223344]⟩

private theorem nativeSuccess : Steps (host false) (source false) observed := by
  let store := changed false
  let word := i32 0x11223344
  let load : Admin := .source ((Op.load 1).v1)
  let call : Admin := .source (.call childTarget.index)
  have recordedLocal : Step (host false) (framed store active (values saved ++ result (.values [i32 7]) ++ tail))
      (framed store recorded (values saved ++ [load, call])) :=
    .frame (.label (.context (.localSet _ active ⟨2⟩ (i32 7) (i32 0) rfl) saved [load, call]) 1 []) 1 caller
  have read : Step (host false) (framed store recorded (values saved ++ [load, call]))
      (framed store recorded (values [word] ++ [call])) := by
    apply Step.frame (Step.label ?_ 1 []) 1 caller
    exact (MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1)
      (address := 0) (saved := []) (tail := [call])
      (show frameMemory store recorded = some (slot, { initial with data := written }) from rfl)).mpr
        ⟨.value 0x11223344, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  have resolveChild : Step (host false) (framed store recorded (values [word] ++ [call]))
      (framed store recorded (values [word] ++ [.invoke childAddr])) :=
    .frame (.label (.context (.call _ _ childTarget.index childAddr rfl) [word] []) 1 []) 1 caller
  have invokeChild := Step.invokeWasm (host := host false) store recorded childAddr child.declaration.type
    child.declaration.module child.v1Func [word] rfl rfl (by decide)
  let callee := child.declaration.frame [word]
  have gets := Step.localGet (host := host false) store callee ⟨0⟩ word rfl
  exact (((((native false pending).tail (delivered .values)).tail recordedLocal).tail read).tail resolveChild
    |>.tail (.frame (.label invokeChild 1 []) 1 caller)
    |>.tail (.frame (.label (.frame (.label gets 1 []) 1 recorded) 1 []) 1 caller)
    |>.tail (.frame (.label (.frame (.pure _ _ (.labelDone 1 [] [word])) 1 recorded) 1 []) 1 caller)
    |>.tail (.frame (.label (.pure _ _ (.frameDone 1 callee [word] rfl)) 1 []) 1 caller)
    |>.tail (.frame (.pure _ _ (.labelDone 1 [] [word])) 1 caller))
    |>.tail (.pure _ _ (.frameDone 1 recorded [word] rfl))

example : ∃ phase, PhaseRuns false .call phase ∧
    (entry false).Ready .fixed graph slot .ranked initial args phase ∧ observed = cfg false phase :=
  (corresponds false).mp nativeSuccess

private def trapped : Config Nat := ⟨changed false, caller, [.trap]⟩

private theorem nativeTrap : Steps (host false) (source false) trapped := by
  have discard : Step (host false) (framed (changed false) active (values saved ++ result .trap ++ tail))
      (framed (changed false) active [.trap]) :=
    .frame (.label (.pure _ _ (.trapValues (i32 0) [] tail)) 1 []) 1 caller
  exact ((((native false pending).tail (delivered .trap)).tail discard)
      |>.tail (.frame (.pure _ _ (.labelTrap 1 [])) 1 caller))
    |>.tail (.pure _ _ (.frameTrap 1 active))

example : ∃ phase, PhaseRuns false .call phase ∧
    (entry false).Ready .fixed graph slot .ranked initial args phase ∧ trapped = cfg false phase :=
  (corresponds false).mp nativeTrap

-- The prefix trap comes from a default-initialized local and leaves the live
-- bytes unchanged. The two administrative unwinds follow the tail discard.
example : Steps (host true) (source true) ⟨live true, caller, [.trap]⟩ := by
  let scratch := saved ++ [i64 81]
  let rest := .source (.call site.index) :: (entry true).tail
  have before : PhaseRuns true .call (.computing (scratch ++ [i32 9, i32 0]) [.bin .i32 (.div .unsigned)]) :=
    (readsParams true).tail (.numeric (.get rfl))
  have fails : PhaseEdge true (.computing (scratch ++ [i32 9, i32 0]) [.bin .i32 (.div .unsigned)])
      (.trapped scratch rest) :=
    .prefixTrap (.trap (Numerics.intBinOp_div_zero .i32 .unsigned 9))
  have discard : PhaseEdge true (.trapped scratch rest) (.trapped [] []) :=
    .discard (.cut [] scratch rest [] (Or.inl (by decide)))
  exact native true ((((before.tail fails).tail discard).tail .closeTrap).tail
    (.graph (.pure (.frameTrap 1 active))))

-- The same reached pending site has a divergence step only when declared.
example {dst : Config Nat} : ¬ Step CallFrame.v1NoHost (cfg false (.pending saved args)) dst := by
  intro move
  have checked : site.Checked (live false) active args := ⟨rfl, rfl, rfl, by decide⟩
  rcases (v1_host_pending_step_iff (k := (entry false).context args) (outer := caller)
    (saved := saved) (tail := tail) checked).mp move with ⟨_, _, impossible, _⟩ | ⟨impossible, _⟩
  · exact impossible
  · exact impossible

-- Native arity alone would accept the permuted root operands. The source
-- entry guard requires the declaration's ordered types.
example : ¬ (entry false).Checked .fixed graph slot .ranked (base false) caller [i32 9, i64 81] := by
  intro wrong
  have different : [NumType.int .i32, .int .i64] ≠ hostType.params := by decide
  exact different wrong.parameters

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
