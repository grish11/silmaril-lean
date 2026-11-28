module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.SequenceExamples

open Execution.Runtime (Frame FuncAddr HostOutcome MemAddr MemInst ModuleInst Value)
open Computed
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private def slot : MemAddr := ⟨0⟩
private def rootAddr : FuncAddr := ⟨2⟩
private def hostType : Wasm.V1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def first : HostCall.V1.Site Nat := ⟨⟨0⟩, ⟨0⟩, hostType, 11⟩
private def second : HostCall.V1.Site Nat := ⟨⟨1⟩, ⟨1⟩, hostType, 19⟩
private def mod : ModuleInst := { funcs := [first.address, second.address], memories := [slot], types := [hostType] }
private def fn : Function :=
  ⟨⟨mod, ⟨0⟩, hostType.params, [.int .i32], hostType.results⟩, 0, [i32 0],
    [.ranked (.set ⟨1⟩), .load 1]⟩
private def segment : HostSegment Nat := ⟨[], second⟩
private def seq : Sequence Nat := ⟨⟨⟨0⟩, rootAddr, fn, [.get ⟨0⟩], first⟩, [segment]⟩
private def graph : Program := ⟨[], none⟩
private def rootArgs : List Value := [i32 5]
private def saved : List Value := [i32 0]
private def caller : Frame := ⟨[i32 42], { funcs := [rootAddr] }⟩
private def initial : MemInst := ⟨⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩, none⟩
private def base : Store Nat :=
  { funcs := [.host hostType 11, .host hostType 19, .wasm fn.declaration.type mod seq.v1Func],
    memories := [initial] }

private def live (bytes : ByteArray) := storeWithBytes base slot initial bytes
private def firstBytes : Bool → ByteArray
  | false => ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
  | true => ⟨#[0xaa, 0x88, 0x77, 0x66, 0x55, 0xbb]⟩
private def firstValue (choice : Bool) : Value := i32 (if choice then 8 else 7)
private def secondValue : Value := i32 100
private def word (choice : Bool) : BitVec 32 := if choice then 0x55667788 else 0x11223344

private inductive FirstOutcome : HostOutcome Wasm.V1.Func Nat → Prop
  | value (choice : Bool) : FirstOutcome (.returned (live (firstBytes choice)) (.values [firstValue choice]))
  | trap : FirstOutcome (.returned (live (firstBytes true)) .trap)

private def host : HostSemantics Nat :=
  fun id store input outcome =>
    (id = first.target ∧ store = live initial.data ∧ input = rootArgs ∧ FirstOutcome outcome) ∨
    ∃ choice : Bool, id = second.target ∧ store = live (firstBytes choice) ∧ input = [firstValue choice] ∧
      (outcome = .returned store (.values [secondValue]) ∨ outcome = .diverged)

private theorem isSite {site : HostCall.V1.Site Nat} (member : site ∈ seq.sites) : site = first ∨ site = second := by
  change site ∈ [first, second] at member
  simpa using member

private theorem checked : seq.Checked .fixed graph slot .ranked base caller rootArgs where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro site used
    rcases isSite used with rfl | rfl <;> exact ⟨rfl, rfl, by decide⟩
  typedBody := rfl
  supportedTail := rfl
  linkedTail := by intro _ h; cases h

private theorem layout : Layout graph base slot initial where
  memory := rfl
  functions := by intro _ _ h; simp [graph, Program.lookup] at h

private theorem contract : seq.Contract host .fixed slot initial base := by
  intro site used bytes _ input _ after result behavior
  have signature : site.signature = hostType := by rcases isSite used with rfl | rfl <;> rfl
  rcases behavior with ⟨_, store, _, behavior⟩ | ⟨choice, _, store, _, outcome | impossible⟩
  · rw [store]
    cases behavior with
    | value choice =>
      refine ⟨?_, initial.data, firstBytes choice, rfl, ?_, ?_⟩
      · rw [signature]
        rfl
      · cases choice <;> rfl
      · cases choice <;> rfl
    | trap => exact ⟨trivial, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases outcome
    rw [store, signature]
    cases choice
    · exact ⟨rfl, firstBytes false, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, firstBytes true, firstBytes true, rfl, rfl, rfl⟩
  · cases impossible

private abbrev Phase := Sequence.Phase Nat
private abbrev Ready := seq.Ready .fixed graph slot .ranked initial
private abbrev Runs := seq.Runs host .fixed graph slot base initial initial.data caller rootArgs
private abbrev cfg := seq.render base slot initial initial.data caller rootArgs

private def source : Config Nat := ⟨live initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩
private def firstPending : Phase := .pending initial.data saved rootArgs first [segment]
private def secondPending (choice : Bool) : Phase :=
  .pending (firstBytes choice) saved [firstValue choice] second []

private theorem correspondence {dst : Config Nat} :
    Steps host source dst ↔ ∃ phase, Runs .call phase ∧ Ready phase ∧ dst = cfg phase :=
  Sequence.v1_call_run_iff rfl checked layout trivial rfl contract

private theorem readyOnRun {phase : Phase} (run : Runs .call phase) : Ready phase := by
  induction run with
  | refl => trivial
  | tail _ move ih => exact move.ready rfl checked layout rfl contract ih

private theorem native {phase : Phase} (run : Runs .call phase) : Steps host source (cfg phase) :=
  correspondence.mpr ⟨phase, run, readyOnRun run, rfl⟩

private theorem firstRun : Runs .call firstPending :=
  (((Relation.ReflTransGen.single .resolve).tail .enter).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private theorem secondRun (choice : Bool) : Runs .call (secondPending choice) := by
  have delivered : Runs .call (seq.delivered caller rootArgs (firstBytes choice) saved [segment]
      (.values [firstValue choice])) :=
    firstRun.tail (.returned (.inl ⟨rfl, rfl, rfl, .value choice⟩) rfl)
  exact delivered.tail (.hostResolve rfl)

private def active : Frame := fn.declaration.frame rootArgs
private def recorded : Frame := { active with locals := rootArgs ++ [secondValue] }
private def framed (s : Store Nat) (f : Frame) (body : List Admin) : Config Nat :=
  ⟨s, caller, [.frame 1 f [.label 1 [] body]]⟩

-- Both outcomes from one first invocation feed the ordered value and the
-- actual returned store into the second native invocation.
example (choice : Bool) : Steps host source
    (framed (live (firstBytes choice)) active (values (saved ++ [firstValue choice]) ++ [.invoke second.address] ++ seq.root.tail)) :=
  native (secondRun choice)

private theorem nativeSuccess (choice : Bool) :
    Steps host source ⟨live (firstBytes choice), caller, values [i32 (word choice)]⟩ := by
  let store := live (firstBytes choice)
  let load : Admin := .source ((Op.load 1).v1)
  have delivered : Step host (cfg (secondPending choice))
      (framed store active (values saved ++ values [secondValue] ++ seq.root.tail)) :=
    .frame (.label (.context
      (.invokeHost store store active second.address hostType 19 [firstValue choice] (.values [secondValue])
        rfl rfl (.inr ⟨choice, rfl, rfl, rfl, .inl rfl⟩)) saved seq.root.tail) 1 []) 1 caller
  have recordedLocal : Step host (framed store active (values saved ++ values [secondValue] ++ seq.root.tail))
      (framed store recorded (values saved ++ [load])) :=
    .frame (.label (.context (.localSet store active ⟨1⟩ secondValue (i32 0) rfl) saved [load]) 1 []) 1 caller
  have read : Step host (framed store recorded (values saved ++ [load]))
      (framed store recorded (values [i32 (word choice)])) := by
    apply Step.frame (Step.label ?_ 1 []) 1 caller
    refine (MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1) (address := 0) (saved := [])
      (tail := []) (show frameMemory store recorded = some (slot, { initial with data := firstBytes choice }) from rfl)).mpr
      ⟨.value (word choice), ?_, rfl⟩
    cases choice <;> exact MemoryQuery.fact_at (.load _ _ (by decide))
  exact ((((native (secondRun choice)).tail delivered).tail recordedLocal).tail read
    |>.tail (.frame (.pure _ _ (.labelDone 1 [] [i32 (word choice)])) 1 caller))
    |>.tail (.pure _ _ (.frameDone 1 recorded [i32 (word choice)] rfl))

example (choice : Bool) :=
  correspondence.mp (nativeSuccess choice)

-- Declared divergence at the second invocation leaves the new store and the
-- pending invocation exactly in place.
example (choice : Bool) : Steps host source (cfg (secondPending choice)) :=
  native ((secondRun choice).tail (.diverged (.inr ⟨choice, rfl, rfl, rfl, .inr rfl⟩)))

private def afterTrap : Phase := .trapped (firstBytes true) saved (seq.continuation [segment])

private theorem trapDelivery : Runs .call afterTrap := by
  have returned : host first.target (live initial.data) rootArgs (.returned (live (firstBytes true)) .trap) :=
    .inl ⟨rfl, rfl, rfl, .trap⟩
  exact firstRun.tail (.returned returned rfl)

example : Steps host source (framed (live (firstBytes true)) active
    (values saved ++ .trap :: .source (.call second.index) :: seq.root.tail)) :=
  native trapDelivery

-- The next site's instruction is discarded on unwind. The trapping host's
-- returned bytes are still the live memory after the frame is discarded.
example : Steps host source ⟨live (firstBytes true), caller, [.trap]⟩ := by
  have discarded : Runs .call (.trapped (firstBytes true) [] []) :=
    trapDelivery.tail (.discard (.cut [] saved (seq.continuation [segment]) [] (Or.inl (by decide))))
  exact native ((discarded.tail .closeTrap).tail (.graph (.pure (.frameTrap 1 active))))

-- With an embedding that supplies no outcome, the same pending
-- configuration takes no successor at all.
example (choice : Bool) {dst : Config Nat} : ¬ Step CallFrame.v1NoHost (cfg (secondPending choice)) dst := by
  intro move
  have blocked : seq.Contract CallFrame.v1NoHost .fixed slot initial base :=
    fun _ _ _ _ _ _ _ _ outcome => outcome.elim
  obtain ⟨phase, transition, _, _⟩ :=
    (Sequence.v1_step_iff rfl checked layout trivial rfl blocked (readyOnRun (secondRun choice))).mp move
  cases transition with
  | returned outcome _ => exact outcome
  | diverged outcome => exact outcome

-- Static checking uses the first declared result type to admit the second
-- site, even if the embedding never returns normally at the first one.
example : Sequence.check fn (Prefix.stackTypes fn.initial)
    [seq.first, { segment with site := { second with signature := ⟨[.int .i64], [.int .i32]⟩ } }] = false := rfl


namespace EnclosingTail

private def savedPrefix : List Value := [Value.int .i64 42]
private def nextType : Wasm.V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩
private def nextSite : HostCall.V1.Site Nat := { second with signature := nextType }
private def entryFn : Function := { fn with initial := savedPrefix, code := [] }
private def entry : Sequence Nat := ⟨⟨⟨0⟩, rootAddr, entryFn, [.get ⟨0⟩], first⟩, []⟩
private def scalar : Option NumType := some (.int .i32)
private def tailRegion : Source Nat := .hosts ⟨[], nextSite⟩ []
private def arm : Source Nat := .ifThen scalar ⟨0⟩ .root (.hosts ⟨[.get ⟨0⟩], first⟩ []) (.plain [])
private def body : Source Nat := .blockThen scalar arm tailRegion
private def allocationFor (region : Source Nat) : Store Nat :=
  { funcs := [.host hostType 11, .host nextType 19, .wasm entryFn.declaration.type mod (entry.v1FuncFor region)],
    memories := [initial] }
private def storedFor (region : Source Nat) (bytes : ByteArray) := storeWithBytes (allocationFor region) slot initial bytes
private abbrev allocation := allocationFor body
private abbrev stored := storedFor body
private def innerLabel : OpenLabel Nat := .block [] scalar (.plain [])
private def outerLabel : OpenLabel Nat := .block savedPrefix scalar tailRegion
private def labels := [innerLabel, outerLabel]

private def behaviorFor (region : Source Nat) : HostSemantics Nat := fun id store operands answer =>
  (id = first.target ∧ store = storedFor region initial.data ∧ operands = rootArgs ∧
    ((∃ choice : Bool, answer = .returned (storedFor region (firstBytes choice)) (.values [firstValue choice])) ∨
      answer = .returned (storedFor region (firstBytes true)) .trap)) ∨
  ∃ choice : Bool, id = nextSite.target ∧ store = storedFor region (firstBytes choice) ∧
    operands = savedPrefix ++ [firstValue choice] ∧
    (answer = .returned store (.values [i32 (word choice)]) ∨ answer = .diverged)

private abbrev behavior := behaviorFor body

private theorem siteOf {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites body) :
    site = first ∨ site = nextSite := by
  change site ∈ [first, first, nextSite] at used
  simpa using used

private theorem admittedFor (region : Source Nat)
    (sites : ∀ site ∈ entry.sourceSites region, site = first ∨ site = nextSite)
    (typed : entry.checkSource (Prefix.stackTypes entryFn.initial) entryFn.declaration.results entryFn.entryLabels region = true)
    (guard : Source.Allowed .fixed graph slot .ranked entryFn region) :
    entry.Checked .fixed graph slot .ranked (allocationFor region) caller rootArgs region where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro site used
    rcases sites site used with rfl | rfl <;> exact ⟨rfl, rfl, by decide⟩
  typedBody := typed
  guardedBody := guard
  supportedTail := rfl
  linkedTail := by intro _ used; cases used

private theorem admitted : entry.Checked .fixed graph slot .ranked allocation caller rootArgs body :=
  admittedFor body (fun _ => siteOf) rfl (by
    refine ⟨trivial, ?_, trivial, trivial⟩
    intro _ member
    cases member)

private theorem layoutFor (region : Source Nat) : Layout graph (allocationFor region) slot initial where
  memory := rfl
  functions := by intro _ _ found; simp [graph, Program.lookup] at found

private abbrev storeLayout := layoutFor body

private theorem embeddingFor (region : Source Nat)
    (sites : ∀ site ∈ entry.sourceSites region, site = first ∨ site = nextSite) :
    entry.Contract (behaviorFor region) .fixed slot initial (allocationFor region) region := by
  intro site used bytes _ operands _ after result outcome
  have signature : site.signature.results = [.int .i32] := by rcases sites site used with rfl | rfl <;> rfl
  rcases outcome with ⟨_, store, _, ⟨choice, equal⟩ | trap⟩ | ⟨choice, _, store, _, equal | impossible⟩
  · cases equal
    rw [store, signature]
    cases choice
    · exact ⟨rfl, initial.data, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases trap
    rw [store]
    exact ⟨trivial, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases equal
    rw [store, signature]
    cases choice
    · exact ⟨rfl, firstBytes false, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, firstBytes true, firstBytes true, rfl, rfl, rfl⟩
  · cases impossible

private theorem embedding : entry.Contract behavior .fixed slot initial allocation body :=
  embeddingFor body (fun _ => siteOf)

private abbrev TailRuns := entry.Runs behavior .fixed graph slot allocation initial initial.data caller rootArgs
private abbrev renderPhase := entry.render allocation slot initial initial.data caller rootArgs
private def launch : Config Nat := ⟨stored initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩
private def inside := entryFn.declaration.frame rootArgs

private theorem tailReady {phase : Phase} (run : TailRuns (.call body) phase) :
    entry.Ready .fixed graph slot .ranked initial phase body := by
  induction run with
  | refl => rfl
  | tail _ move ih => exact move.ready rfl admitted storeLayout rfl embedding ih

private theorem nativeTail {phase : Phase} (run : TailRuns (.call body) phase) :
    Steps behavior launch (renderPhase phase) :=
  (Sequence.v1_call_run_iff rfl admitted storeLayout trivial rfl embedding).mpr ⟨phase, run, tailReady run, rfl⟩

private theorem entersArm :
    TailRuns (.call body) (.pending initial.data [] rootArgs first [] labels) := by
  have opens : TailRuns (.call body) (.if_ initial.data [] scalar ⟨0⟩ .root
      (.hosts ⟨[.get ⟨0⟩], first⟩ []) (.plain []) [outerLabel]) :=
    ((Relation.ReflTransGen.single .resolve).tail .enter).tail .openBlock
  have selects : TailRuns (.call body) (.block initial.data [] scalar .root (.plain []) [outerLabel]) :=
    (opens.tail (.readCondition rfl)).tail .select
  exact ((selects.tail .openBlock).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private def nextPending (choice : Bool) : Phase :=
  .pending (firstBytes choice) [] (savedPrefix ++ [firstValue choice]) nextSite []

private theorem reachesTail (choice : Bool) : TailRuns (.call body) (nextPending choice) := by
  have returned : behavior first.target (stored initial.data) rootArgs
      (.returned (stored (firstBytes choice)) (.values [firstValue choice])) :=
    .inl ⟨rfl, rfl, rfl, .inl ⟨choice, rfl⟩⟩
  have inner : TailRuns (.call body) (.completed (firstBytes choice) [firstValue choice] innerLabel [outerLabel]) :=
    entersArm.tail (.returned returned rfl)
  have outer : TailRuns (.call body) (.completed (firstBytes choice) [firstValue choice] outerLabel []) :=
    inner.tail (.closeLabel rfl)
  exact (outer.tail (.closeLabel rfl)).tail
    (.hostResolve (saved := []) (actual := savedPrefix ++ [firstValue choice]) (site := nextSite) rfl)

-- Both the mixed-width saved prefix and the arm result are consumed by
-- the distinct host in the enclosing continuation, using the returned bytes.
example (choice : Bool) : Steps behavior launch
    ⟨stored (firstBytes choice), caller, [.frame 1 inside
      [.label 1 [] (values (savedPrefix ++ [firstValue choice]) ++ [.invoke nextSite.address])]]⟩ :=
  nativeTail (reachesTail choice)

example (choice : Bool) : Steps behavior launch ⟨stored (firstBytes choice), caller, values [i32 (word choice)]⟩ := by
  have returned : behavior nextSite.target (stored (firstBytes choice)) (savedPrefix ++ [firstValue choice])
      (.returned (stored (firstBytes choice)) (.values [i32 (word choice)])) :=
    .inr ⟨choice, rfl, rfl, rfl, .inl rfl⟩
  have deliver := (reachesTail choice).tail (.returned returned rfl)
  exact nativeTail ((deliver.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word choice)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 inside [i32 (word choice)] rfl))))

-- Divergence at the resumed host still steps to the same pending call.
example (choice : Bool) : Step behavior (renderPhase (nextPending choice)) (renderPhase (nextPending choice)) := by
  exact .frame (.label (.invokeHostDiverges _ _ nextSite.address nextType nextSite.target
    (savedPrefix ++ [firstValue choice]) rfl rfl (.inr ⟨choice, rfl, rfl, rfl, .inr rfl⟩)) 1 []) 1 caller

-- In an embedding with no outcome, this pending invocation has no native step.
example (choice : Bool) {dst : Config Nat} : ¬ Step CallFrame.v1NoHost (renderPhase (nextPending choice)) dst := by
  intro move
  have blocked : entry.Contract CallFrame.v1NoHost .fixed slot initial allocation body :=
    fun _ _ _ _ _ _ _ _ outcome => outcome.elim
  obtain ⟨_, transition, _, _⟩ :=
    (Sequence.v1_step_iff rfl admitted storeLayout trivial rfl blocked (tailReady (reachesTail choice))).mp move
  cases transition with
  | returned outcome _ => exact outcome
  | diverged outcome => exact outcome

private def trapped : Phase := .trapped (firstBytes true) [] [] labels

private theorem armTrap : TailRuns (.call body) trapped := by
  have returned : behavior first.target (stored initial.data) rootArgs (.returned (stored (firstBytes true)) .trap) :=
    .inl ⟨rfl, rfl, rfl, .inr rfl⟩
  exact entersArm.tail (.returned returned rfl)

-- The inner label closes, then the outer label closes. This exposes the
-- saved prefix and the pending host instruction to trap cleanup.
example : Steps behavior launch
    ⟨stored (firstBytes true), caller, [.frame 1 inside
      [.label 1 [] (values savedPrefix ++ [.trap, .source (.call nextSite.index)])]]⟩ :=
  nativeTail ((armTrap.tail .closeTrap).tail .closeTrap)

example : Steps behavior launch ⟨stored (firstBytes true), caller, [.trap]⟩ := by
  have discarded : TailRuns (.call body) (.trapped (firstBytes true) [] []) :=
    ((armTrap.tail .closeTrap).tail .closeTrap).tail
      (.discard (.cut [] savedPrefix ([.source (.call nextSite.index)] : List Admin) [] (Or.inl (by decide))))
  exact nativeTail ((discarded.tail .closeTrap).tail (.graph (.pure (.frameTrap 1 inside))))

example (run : TailRuns trapped (nextPending true)) : False := by
  rcases Sequence.trapped_run run with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible

-- A mismatched enclosing host signature is rejected before arm selection.
example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (.blockThen scalar arm (.hosts ⟨[], { nextSite with signature := hostType }⟩ [])) = false := rfl

-- A host-free suffix that would lose the typed reentry stack is also rejected.
example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (.blockThen scalar (.plain [.ranked (.numeric (.get ⟨0⟩))]) tailRegion) = false := rfl

namespace Forward

private def target : ForwardBranch := ⟨⟨1⟩, [.int .i32]⟩
private def skippedHost : Source Nat := .hosts ⟨[], first⟩ []
private def writer : HostSegment Nat := ⟨[.get ⟨0⟩, .get ⟨0⟩], first⟩
private def regionWith (segment : HostSegment Nat) (branch : ForwardBranch) : Source Nat :=
  .blockThen scalar (.blockThen scalar (.hosts segment [] (some branch)) skippedHost) tailRegion
private def region : Source Nat := regionWith writer target
private def store := storedFor region
private def inner : OpenLabel Nat := .block [] scalar skippedHost

private theorem linked {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites region) :
    site = first ∨ site = nextSite := by
  change site ∈ [first, first, nextSite] at used
  simpa using used

private theorem admittedBranch : entry.Checked .fixed graph slot .ranked (allocationFor region) caller rootArgs region :=
  admittedFor region (fun _ => linked) rfl ⟨trivial, trivial, trivial⟩

private theorem contracted : entry.Contract (behaviorFor region) .fixed slot initial (allocationFor region) region :=
  embeddingFor region (fun _ => linked)

private abbrev BranchRuns :=
  entry.Runs (behaviorFor region) .fixed graph slot (allocationFor region) initial initial.data caller rootArgs
private abbrev renderBranch := entry.render (allocationFor region) slot initial initial.data caller rootArgs
private def launchBranch : Config Nat := ⟨store initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private theorem readyBranch {phase : Phase} (run : BranchRuns (.call region) phase) :
    entry.Ready .fixed graph slot .ranked initial phase region := by
  induction run with
  | refl => rfl
  | tail _ move ih => exact move.ready rfl admittedBranch (layoutFor region) rfl contracted ih

private theorem nativeBranch {phase : Phase} (run : BranchRuns (.call region) phase) :
    Steps (behaviorFor region) launchBranch (renderBranch phase) :=
  (Sequence.v1_call_run_iff rfl admittedBranch (layoutFor region) trivial rfl contracted).mpr
    ⟨phase, run, readyBranch run, rfl⟩

private theorem firstCall :
    BranchRuns (.call region) (.pending initial.data rootArgs rootArgs first [] [inner, outerLabel] (some (.br target))) := by
  have entered : BranchRuns (.call region)
      (.block initial.data [] scalar (.hosts writer [] (some target)) skippedHost [outerLabel]) :=
    ((Relation.ReflTransGen.single .resolve).tail .enter).tail .openBlock
  exact (((entered.tail .openBlock).tail (.numeric (.get rfl))).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private def lowered (choice : Bool) : Phase :=
  .branching (firstBytes choice) (rootArgs ++ [firstValue choice]) { target with depth := ⟨0⟩ }
    (entry.tailCode inner) [outerLabel]

private theorem cross (choice : Bool) : BranchRuns (.call region) (lowered choice) := by
  have returned : behaviorFor region first.target (store initial.data) rootArgs
      (.returned (store (firstBytes choice)) (.values [firstValue choice])) :=
    .inl ⟨rfl, rfl, rfl, .inl ⟨choice, rfl⟩⟩
  have branch : BranchRuns (.call region)
      (.branching (firstBytes choice) (rootArgs ++ [firstValue choice]) target [] [inner, outerLabel]) :=
    firstCall.tail (.returned returned rfl)
  exact branch.tail (.branchOuter (by decide))

private theorem lands (choice : Bool) : BranchRuns (.call region) (nextPending choice) := by
  have resumes : BranchRuns (.call region)
      (.computing (firstBytes choice) (savedPrefix ++ [firstValue choice]) [] nextSite []) :=
    (cross choice).tail (.branchExit (extra := rootArgs) (payload := [firstValue choice]) rfl)
  exact resumes.tail (.hostResolve (saved := []) rfl)

-- Native intermediate prefix. The intermediate host is still in the code
-- after lowering and is discarded by the next label exit.
example (choice : Bool) : Steps (behaviorFor region) launchBranch
    ⟨store (firstBytes choice), caller, [.frame 1 inside [.label 1 []
      (values savedPrefix ++ [.label 1 []
        (values (rootArgs ++ [firstValue choice]) ++ [.source (.br ⟨0⟩), .source (.call first.index)])]
        ++ [.source (.call nextSite.index)])]]⟩ :=
  nativeBranch (cross choice)

private theorem nativeExit (choice : Bool) : Step (behaviorFor region) (renderBranch (lowered choice))
    (renderBranch (.computing (firstBytes choice) (savedPrefix ++ [firstValue choice]) [] nextSite [])) :=
  .frame (.label (.context (.pure _ _ (.labelBranch 1 [] rootArgs [firstValue choice]
    [.source (.call first.index)] rfl)) savedPrefix [.source (.call nextSite.index)]) 1 []) 1 caller

-- Read the native target exit back into the checked phase relation.
example (choice : Bool) :=
  (Sequence.v1_step_iff rfl admittedBranch (layoutFor region) trivial rfl contracted (readyBranch (cross choice))).mp
    (nativeExit choice)

-- After the target exit, only the saved i64 and the branch's i32 payload
-- are passed to the target host at the store returned by the writer.
example (choice : Bool) : Steps (behaviorFor region) launchBranch
    ⟨store (firstBytes choice), caller, [.frame 1 inside
      [.label 1 [] (values (savedPrefix ++ [firstValue choice]) ++ [.invoke nextSite.address])]]⟩ :=
  nativeBranch (lands choice)

example (choice : Bool) : Steps (behaviorFor region) launchBranch
    ⟨store (firstBytes choice), caller, values [i32 (word choice)]⟩ := by
  have returned : behaviorFor region nextSite.target (store (firstBytes choice)) (savedPrefix ++ [firstValue choice])
      (.returned (store (firstBytes choice)) (.values [i32 (word choice)])) :=
    .inr ⟨choice, rfl, rfl, rfl, .inl rfl⟩
  have deliver := (lands choice).tail (.returned returned rfl)
  exact nativeBranch ((deliver.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word choice)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 inside [i32 (word choice)] rfl))))

-- Depth two names the implicit function label. Its result type matches the payload.
example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (regionWith writer { target with depth := ⟨2⟩ }) = true := rfl

example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (regionWith writer { target with depth := ⟨3⟩ }) = false := rfl

-- The explicit target expects i32. A writer with an i64 result cannot
-- supply the actual branch suffix, even with a correct target annotation.
example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (regionWith { writer with site := { first with signature := ⟨hostType.params, [.int .i64]⟩ } } target) = false := rfl

end Forward


namespace ConditionalBranch

private def middleSite : HostCall.V1.Site Nat := ⟨⟨2⟩, ⟨3⟩, hostType, 23⟩
private def branchModule : ModuleInst := { mod with funcs := mod.funcs ++ [middleSite.address] }
private def branchFn : Function := { entryFn with declaration.module := branchModule }
private def entry : Sequence Nat :=
  ⟨{ EnclosingTail.entry.root with function := branchFn }, []⟩
private def target : ForwardBranch := ⟨⟨1⟩, [.int .i32]⟩
private def writer : HostSegment Nat := ⟨[.get ⟨0⟩, .get ⟨0⟩], first⟩
private def onZero : Source Nat := .hosts ⟨[], middleSite⟩ []
private def testRegion (segment : HostSegment Nat) (branch : ForwardBranch) (fallthrough : Source Nat := onZero) : Source Nat :=
  .blockThen scalar (.blockThen scalar (.hostsThen segment [] (.brIf branch fallthrough)) (.plain [])) tailRegion
private def body : Source Nat := testRegion writer target
private def allocationFor (region : Source Nat) : Store Nat :=
  { funcs := [.host hostType first.target, .host nextType nextSite.target,
      .wasm branchFn.declaration.type branchModule (entry.v1FuncFor region), .host hostType middleSite.target],
    memories := [initial] }
private def liveFor (region : Source Nat) (bytes : ByteArray) := storeWithBytes (allocationFor region) slot initial bytes
private abbrev allocation := allocationFor body
private abbrev live := liveFor body
private def inner : OpenLabel Nat := .block [] scalar (.plain [])
private def labels := [inner, outerLabel]

private def condition (taken : Bool) : BitVec 32 := if taken then 0x80000000 else 0
private def fallthroughBytes : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xcc]⟩
private def finalBytes (taken : Bool) : ByteArray := if taken then firstBytes true else fallthroughBytes
private def resultValue (taken : Bool) : Value := i32 (if taken then 5 else 8)

private def hostFor (region : Source Nat) : HostSemantics Nat := fun id store operands answer =>
  (id = first.target ∧ store = liveFor region initial.data ∧ operands = rootArgs ∧
    ∃ taken : Bool, answer = .returned (liveFor region (firstBytes taken)) (.values [i32 (condition taken)])) ∨
  (id = middleSite.target ∧ store = liveFor region (firstBytes false) ∧ operands = rootArgs ∧
    answer = .returned (liveFor region fallthroughBytes) (.values [resultValue false])) ∨
  (id = nextSite.target ∧ ∃ taken : Bool, store = liveFor region (finalBytes taken) ∧
    operands = savedPrefix ++ [resultValue taken] ∧ answer = .returned store (.values [i32 (word taken)]))

private abbrev host := hostFor body

private theorem siteOf {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites body) :
    site = first ∨ site = middleSite ∨ site = nextSite := by
  change site ∈ [first, middleSite, nextSite] at used
  simpa using used

private theorem admittedFor (region : Source Nat)
    (sites : ∀ site ∈ entry.sourceSites region, site = first ∨ site = middleSite ∨ site = nextSite)
    (typed : entry.checkSource (Prefix.stackTypes branchFn.initial) branchFn.declaration.results branchFn.entryLabels region = true)
    (guarded : Source.Allowed .fixed graph slot .ranked branchFn region) :
    entry.Checked .fixed graph slot .ranked (allocationFor region) caller rootArgs region where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro site used
    rcases sites site used with rfl | rfl | rfl <;> exact ⟨rfl, rfl, by decide⟩
  typedBody := typed
  guardedBody := guarded
  supportedTail := rfl
  linkedTail := by intro _ used; cases used

private theorem admitted : entry.Checked .fixed graph slot .ranked allocation caller rootArgs body :=
  admittedFor body (fun _ => siteOf) rfl (by
    refine ⟨trivial, ?_, trivial⟩
    intro _ used
    cases used)

private theorem layoutFor (region : Source Nat) : Layout graph (allocationFor region) slot initial where
  memory := rfl
  functions := by intro _ _ found; simp [graph, Program.lookup] at found

private abbrev layout := layoutFor body

private theorem contractFor (region : Source Nat)
    (sites : ∀ site ∈ entry.sourceSites region, site = first ∨ site = middleSite ∨ site = nextSite) :
    entry.Contract (hostFor region) .fixed slot initial (allocationFor region) region := by
  intro site used bytes _ operands _ after result outcome
  have signature : site.signature.results = [.int .i32] := by rcases sites site used with rfl | rfl | rfl <;> rfl
  rcases outcome with ⟨_, store, _, taken, equal⟩ | ⟨_, store, _, equal⟩ | ⟨_, taken, store, _, equal⟩
  · cases equal
    rw [store, signature]
    cases taken
    · exact ⟨rfl, initial.data, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases equal
    rw [store, signature]
    exact ⟨rfl, firstBytes false, fallthroughBytes, rfl, rfl, rfl⟩
  · cases equal
    rw [store, signature]
    cases taken
    · exact ⟨rfl, fallthroughBytes, fallthroughBytes, rfl, rfl, rfl⟩
    · exact ⟨rfl, firstBytes true, firstBytes true, rfl, rfl, rfl⟩

private theorem contract : entry.Contract host .fixed slot initial allocation body :=
  contractFor body (fun _ => siteOf)

private abbrev Runs := entry.Runs host .fixed graph slot allocation initial initial.data caller rootArgs
private abbrev cfg := entry.render allocation slot initial initial.data caller rootArgs
private def launch : Config Nat := ⟨live initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩
private def active := branchFn.declaration.frame rootArgs

private theorem ready {phase : Phase} (run : Runs (.call body) phase) : entry.Ready .fixed graph slot .ranked initial phase body := by
  induction run with
  | refl => rfl
  | tail _ step ih => exact step.ready rfl admitted layout rfl contract ih

private theorem native {phase : Phase} (run : Runs (.call body) phase) : Steps host launch (cfg phase) :=
  (Sequence.v1_call_run_iff rfl admitted layout trivial rfl contract).mpr ⟨phase, run, ready run, rfl⟩

private def testPhase (taken : Bool) : Phase :=
  .branchTest (firstBytes taken) (rootArgs ++ [i32 (condition taken)]) target onZero labels

private theorem reachesTest (taken : Bool) : Runs (.call body) (testPhase taken) := by
  have entered : Runs (.call body)
      (.block initial.data [] scalar (.hostsThen writer [] (.brIf target onZero)) (.plain []) [outerLabel]) :=
    ((Relation.ReflTransGen.single .resolve).tail .enter).tail .openBlock
  have pending : Runs (.call body)
      (.pending initial.data rootArgs rootArgs first [] labels (some (.brIf target onZero))) :=
    (((entered.tail .openBlock).tail (.numeric (.get rfl))).tail (.numeric (.get rfl))).tail (.hostResolve rfl)
  have returned : host first.target (live initial.data) rootArgs
      (.returned (live (firstBytes taken)) (.values [i32 (condition taken)])) :=
    .inl ⟨rfl, rfl, rfl, taken, rfl⟩
  exact pending.tail (.returned returned rfl)

private def testingTaken : Phase := .branching (firstBytes true) rootArgs target (expression (entry.sourceCode onZero)) labels
private def testingZero : Phase := .computing (firstBytes false) rootArgs [] middleSite [] labels

-- Reconstruct both actual conditioned native steps and read them back.
private theorem selectsNative (taken : Bool) :
    Step host (cfg (testPhase taken)) (cfg (if taken then testingTaken else testingZero)) := by
  have inContext {body after : List Admin}
      (step : Step host ⟨live (firstBytes taken), active, body⟩ ⟨live (firstBytes taken), active, after⟩) :
      Step host ⟨live (firstBytes taken), caller, (entry.context rootArgs labels).plug value body⟩
        ⟨live (firstBytes taken), caller, (entry.context rootArgs labels).plug value after⟩ :=
    .frame (.label (.context (.label (.label step 1 []) 1 []) savedPrefix [.source (.call nextSite.index)]) 1 []) 1 caller
  cases taken
  · exact inContext (.context (.pure _ _ (.brIfZero target.depth)) rootArgs [.source (.call middleSite.index)])
  · exact inContext (.context (.pure _ _ (.brIfNonzero target.depth (condition true) (by decide)))
      rootArgs [.source (.call middleSite.index)])

example (taken : Bool) :=
  (Sequence.v1_step_iff rfl admitted layout trivial rfl contract (ready (reachesTest taken))).mp (selectsNative taken)

private theorem inMiddle : Runs (.call body) (.pending (firstBytes false) [] rootArgs middleSite [] labels) := by
  have continued : Runs (.call body) testingZero := (reachesTest false).tail .branchZero
  exact continued.tail (.hostResolve (saved := []) rfl)

-- The zero condition leaves the i32 payload on the stack and reaches the
-- intervening host at the store returned by the writer.
example : Steps host launch (cfg (.pending (firstBytes false) [] rootArgs middleSite [] labels)) :=
  native inMiddle

private def finalPending (taken : Bool) : Phase :=
  .pending (finalBytes taken) [] (savedPrefix ++ [resultValue taken]) nextSite []

private theorem reachesFinal (taken : Bool) : Runs (.call body) (finalPending taken) := by
  cases taken
  · have returned : host middleSite.target (live (firstBytes false)) rootArgs
        (.returned (live fallthroughBytes) (.values [resultValue false])) :=
      .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)
    have completed : Runs (.call body) (.completed fallthroughBytes [resultValue false] inner [outerLabel]) :=
      inMiddle.tail (.returned returned rfl)
    exact (((completed.tail (.closeLabel rfl)).tail (.closeLabel rfl)).tail (.hostResolve (saved := []) rfl))
  · have nonzero : condition true ≠ (0 : BitVec 32) := by decide
    have selected : Runs (.call body) testingTaken := (reachesTest true).tail (.branchNonzero nonzero)
    have lowered : Runs (.call body)
        (.branching (firstBytes true) rootArgs { target with depth := ⟨0⟩ } [] [outerLabel]) :=
      selected.tail (.branchOuter (by decide))
    exact (lowered.tail (.branchExit (extra := []) (payload := rootArgs) rfl)).tail (.hostResolve (saved := []) rfl)

-- The taken path reaches this host with the writer's bytes. The zero path
-- reaches it with the intervening host's changed bytes and distinct result.
example (taken : Bool) : Steps host launch
    ⟨live (finalBytes taken), caller, [.frame 1 active [.label 1 []
      (values (savedPrefix ++ [resultValue taken]) ++ [.invoke nextSite.address])]]⟩ :=
  native (reachesFinal taken)

example (taken : Bool) : Steps host launch ⟨live (finalBytes taken), caller, values [i32 (word taken)]⟩ := by
  have returned : host nextSite.target (live (finalBytes taken)) (savedPrefix ++ [resultValue taken])
      (.returned (live (finalBytes taken)) (.values [i32 (word taken)])) :=
    .inr (.inr ⟨rfl, taken, rfl, rfl, rfl⟩)
  have delivered := (reachesFinal taken).tail (.returned returned rfl)
  exact native ((delivered.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word taken)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 active [i32 (word taken)] rfl))))

private abbrev check := entry.checkSource (Prefix.stackTypes savedPrefix) branchFn.declaration.results branchFn.entryLabels

-- Static checking includes the target even though one declared writer result is zero.
example : check (testRegion writer { target with depth := ⟨3⟩ }) = false := rfl
example : check (testRegion { writer with site.signature.results := [.int .i64] } target) = false := rfl
example : check (testRegion { writer with operands := [.get ⟨0⟩] } target) = false := rfl
example : check (testRegion writer target (.hosts ⟨[], { middleSite with signature.params := [.int .i64] }⟩ [])) = false := rfl

namespace TableBranch

private def table : ForwardTable := ⟨[⟨1⟩], ⟨2⟩, [.int .i32]⟩
private def skipped (result : Option NumType) : Source Nat :=
  .hosts ⟨if result.isSome then [] else [.get ⟨0⟩], first⟩ []
private def regionWith (branches : ForwardTable) (innerResult : Option NumType := scalar) : Source Nat :=
  .blockThen scalar
    (.blockThen scalar (.blockThen innerResult (.hostsThen writer [] (.brTable branches)) (skipped innerResult)) onZero)
    tailRegion
private def region : Source Nat := regionWith table
private abbrev allocation := allocationFor region
private abbrev live := liveFor region
private abbrev host := hostFor region
private def inner : OpenLabel Nat := .block [] scalar (skipped scalar)
private def middle : OpenLabel Nat := .block [] scalar onZero
private def labels := [inner, middle, outerLabel]

private theorem siteOf {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites region) :
    site = first ∨ site = middleSite ∨ site = nextSite := by
  change site ∈ [first, first, middleSite, nextSite] at used
  simpa using used

private theorem admitted : entry.Checked .fixed graph slot .ranked allocation caller rootArgs region :=
  admittedFor region (fun _ => siteOf) rfl ⟨trivial, trivial, trivial, trivial⟩
private abbrev layout := layoutFor region
private theorem contract : entry.Contract host .fixed slot initial allocation region :=
  contractFor region (fun _ => siteOf)

private abbrev Runs := entry.Runs host .fixed graph slot allocation initial initial.data caller rootArgs
private abbrev cfg := entry.render allocation slot initial initial.data caller rootArgs
private def launch : Config Nat := ⟨live initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private theorem ready {phase : Phase} (run : Runs (.call region) phase) : entry.Ready .fixed graph slot .ranked initial phase region := by
  induction run with
  | refl => rfl
  | tail _ step ih => exact step.ready rfl admitted layout rfl contract ih

private theorem native {phase : Phase} (run : Runs (.call region) phase) : Steps host launch (cfg phase) :=
  (Sequence.v1_call_run_iff rfl admitted layout trivial rfl contract).mpr ⟨phase, run, ready run, rfl⟩

private def selects (fallback : Bool) : Phase :=
  .tableSelect (firstBytes fallback) (rootArgs ++ [i32 (condition fallback)]) table labels

private theorem reachesTable (fallback : Bool) : Runs (.call region) (selects fallback) := by
  have entersMiddle : Runs (.call region)
      (.block initial.data [] scalar
        (.blockThen scalar (.hostsThen writer [] (.brTable table)) (skipped scalar)) onZero [outerLabel]) :=
    ((Relation.ReflTransGen.single .resolve).tail .enter).tail .openBlock
  have entersInner : Runs (.call region)
      (.block initial.data [] scalar (.hostsThen writer [] (.brTable table)) (skipped scalar) [middle, outerLabel]) :=
    entersMiddle.tail .openBlock
  have pending : Runs (.call region) (.pending initial.data rootArgs rootArgs first [] labels (some (.brTable table))) :=
    (((entersInner.tail .openBlock).tail (.numeric (.get rfl))).tail (.numeric (.get rfl))).tail (.hostResolve rfl)
  have returned : host first.target (live initial.data) rootArgs
      (.returned (live (firstBytes fallback)) (.values [i32 (condition fallback)])) :=
    .inl ⟨rfl, rfl, rfl, fallback, rfl⟩
  exact pending.tail (.returned returned rfl)

private def selected (fallback : Bool) : Phase :=
  .branching (firstBytes fallback) rootArgs (table.select (condition fallback)) [] labels

-- In the native step, the high-bit selector selects the default through
-- unsigned toNat, and zero selects vector entry zero.
private theorem nativeSelect (fallback : Bool) : Step host (cfg (selects fallback)) (cfg (selected fallback)) := by
  have atSite := Step.context
    (Step.pure (host := host) (live (firstBytes fallback)) active (.brTable table.depths table.fallback (condition fallback)))
    rootArgs []
  have withinMiddle := Step.label
    (.context (.label atSite 1 []) [] [.source (.call first.index)]) 1 []
  have withinOuter := Step.label (.context withinMiddle [] [.source (.call middleSite.index)]) 1 []
  exact .frame (.label (.context withinOuter savedPrefix [.source (.call nextSite.index)]) 1 []) 1 caller

example (fallback : Bool) :=
  (Sequence.v1_step_iff rfl admitted layout trivial rfl contract (ready (reachesTable fallback))).mp (nativeSelect fallback)

private theorem afterInner (fallback : Bool) :
    Runs (.call region) (.branching (firstBytes fallback) rootArgs
      ⟨⟨if fallback then 1 else 0⟩, table.results⟩ (entry.tailCode inner) [middle, outerLabel]) := by
  have picked : Runs (.call region) (selected fallback) := (reachesTable fallback).tail .selectTable
  cases fallback <;> exact picked.tail (.branchOuter (by decide))

-- Each path first exposes the innermost label's skipped host. The native target exit or
-- next positive-depth step discards that instruction.
example (fallback : Bool) : Steps host launch
    ⟨live (firstBytes fallback), caller, [.frame 1 active [.label 1 []
      (values savedPrefix ++ [.label 1 [] [.label 1 []
        (values rootArgs ++ [.source (.br ⟨if fallback then 1 else 0⟩), .source (.call first.index)]),
        .source (.call middleSite.index)], .source (.call nextSite.index)])]]⟩ :=
  native (afterInner fallback)

private def indexedHost : Phase := .pending (firstBytes false) [] rootArgs middleSite [] [outerLabel]
private theorem reachesIndexedHost : Runs (.call region) indexedHost := by
  exact ((afterInner false).tail (.branchExit (extra := []) (payload := rootArgs) rfl)).tail
    (.hostResolve (saved := []) rfl)

example : Steps host launch
    ⟨live (firstBytes false), caller, [.frame 1 active [.label 1 []
      (values savedPrefix ++ [.label 1 [] (values rootArgs ++ [.invoke middleSite.address]),
        .source (.call nextSite.index)])]]⟩ :=
  native reachesIndexedHost

private def finalPending (fallback : Bool) : Phase :=
  .pending (finalBytes fallback) [] (savedPrefix ++ [resultValue fallback]) nextSite []

private theorem reachesFinal (fallback : Bool) : Runs (.call region) (finalPending fallback) := by
  cases fallback
  · have returned : host middleSite.target (live (firstBytes false)) rootArgs
        (.returned (live fallthroughBytes) (.values [resultValue false])) :=
      .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)
    have finished : Runs (.call region) (.completed fallthroughBytes [resultValue false] outerLabel []) :=
      reachesIndexedHost.tail (.returned returned rfl)
    exact (finished.tail (.closeLabel rfl)).tail (.hostResolve (saved := []) rfl)
  · have lowered : Runs (.call region)
        (.branching (firstBytes true) rootArgs ⟨⟨0⟩, table.results⟩ (entry.tailCode middle) [outerLabel]) :=
      (afterInner true).tail (.branchOuter (by decide))
    exact (lowered.tail (.branchExit (extra := []) (payload := rootArgs) rfl)).tail (.hostResolve (saved := []) rfl)

-- Indexed and default transfers retain the outer i64. The default skips
-- both hosts and reaches the final host on the writer's bytes and payload.
example (fallback : Bool) : Steps host launch
    ⟨live (finalBytes fallback), caller, [.frame 1 active [.label 1 []
      (values (savedPrefix ++ [resultValue fallback]) ++ [.invoke nextSite.address])]]⟩ :=
  native (reachesFinal fallback)

example (fallback : Bool) : Steps host launch ⟨live (finalBytes fallback), caller, values [i32 (word fallback)]⟩ := by
  have returned : host nextSite.target (live (finalBytes fallback)) (savedPrefix ++ [resultValue fallback])
      (.returned (live (finalBytes fallback)) (.values [i32 (word fallback)])) :=
    .inr (.inr ⟨rfl, fallback, rfl, rfl, rfl⟩)
  have delivered := (reachesFinal fallback).tail (.returned returned rfl)
  exact native ((delivered.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word fallback)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 active [i32 (word fallback)] rfl))))

private abbrev check := entry.checkSource (Prefix.stackTypes savedPrefix) branchFn.declaration.results branchFn.entryLabels

-- These malformed cases still have the valid entry selected by zero.
example : check (regionWith { table with depths := [⟨1⟩, ⟨4⟩] }) = false := rfl
example : check (regionWith { table with fallback := ⟨4⟩ }) = false := rfl

-- The void inner label is admissible until it is listed alongside i32 targets.
example : check (regionWith table none) = true := rfl
example : check (regionWith { table with depths := [⟨1⟩, ⟨0⟩] } none) = false := rfl

example : check (regionWith { table with depths := [] }) = true := rfl

end TableBranch


namespace FunctionTarget

private inductive BranchKind where
  | direct
  | conditional
  | table

private def target : ForwardBranch := ⟨⟨2⟩, [.int .i32]⟩
private def table : ForwardTable := ⟨[⟨1⟩], target.depth, target.results⟩

private def control : BranchKind → Source Nat
  | .direct => .br target
  | .conditional => .brIf target onZero
  | .table => .brTable table

private def region (kind : BranchKind) : Source Nat :=
  .blockThen scalar (.blockThen scalar (.hostsThen writer [] (control kind)) (.plain [])) tailRegion

private theorem siteOf {kind : BranchKind} {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites (region kind)) :
    site = first ∨ site = middleSite ∨ site = nextSite := by
  cases kind with
  | direct | table =>
    have member : site ∈ [first, nextSite] := used
    simp at member
    exact member.imp id Or.inr
  | conditional => exact ConditionalBranch.siteOf used

private theorem admitted (kind : BranchKind) :
    entry.Checked .fixed graph slot .ranked (allocationFor (region kind)) caller rootArgs (region kind) :=
  admittedFor (region kind) (fun _ => siteOf) (by cases kind <;> rfl) (by
    cases kind <;> (refine ⟨trivial, ?_, trivial⟩; intro _ used; cases used))

private theorem contract (kind : BranchKind) :
    entry.Contract (hostFor (region kind)) .fixed slot initial (allocationFor (region kind)) (region kind) :=
  contractFor (region kind) (fun _ => siteOf)

private abbrev live (kind : BranchKind) := liveFor (region kind)
private abbrev host (kind : BranchKind) := hostFor (region kind)
private abbrev Runs (kind : BranchKind) :=
  entry.Runs (host kind) .fixed graph slot (allocationFor (region kind)) initial initial.data caller rootArgs
private abbrev cfg (kind : BranchKind) := entry.render (allocationFor (region kind)) slot initial initial.data caller rootArgs
private def launch (kind : BranchKind) : Config Nat := ⟨live kind initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private theorem ready {kind : BranchKind} {phase : Phase} (run : Runs kind (.call (region kind)) phase) :
    entry.Ready .fixed graph slot .ranked initial phase (region kind) := by
  induction run with
  | refl => rfl
  | tail _ step ih => exact step.ready rfl (admitted kind) (layoutFor (region kind)) rfl (contract kind) ih

private theorem native {kind : BranchKind} {phase : Phase} (run : Runs kind (.call (region kind)) phase) :
    Steps (host kind) (launch kind) (cfg kind phase) :=
  (Sequence.v1_call_run_iff rfl (admitted kind) (layoutFor (region kind)) trivial rfl (contract kind)).mpr
    ⟨phase, run, ready run, rfl⟩

private theorem reachesControl (kind : BranchKind) (selected : Bool) :
    Runs kind (.call (region kind))
      (entry.beginBody caller rootArgs (firstBytes selected) (rootArgs ++ [i32 (condition selected)]) labels (control kind)) := by
  have entered : Runs kind (.call (region kind))
      (.block initial.data [] scalar (.hostsThen writer [] (control kind)) (.plain []) [outerLabel]) :=
    ((Relation.ReflTransGen.single .resolve).tail .enter).tail .openBlock
  have pending : Runs kind (.call (region kind))
      (.pending initial.data rootArgs rootArgs first [] labels (some (control kind))) :=
    (((entered.tail .openBlock).tail (.numeric (.get rfl))).tail (.numeric (.get rfl))).tail (.hostResolve rfl)
  have returned : host kind first.target (live kind initial.data) rootArgs
      (.returned (live kind (firstBytes selected)) (.values [i32 (condition selected)])) :=
    .inl ⟨rfl, rfl, rfl, selected, rfl⟩
  exact pending.tail (.returned returned rfl)

private def branchStack : BranchKind → List Value
  | .direct => rootArgs ++ [i32 (condition true)]
  | _ => rootArgs

private def payload : BranchKind → List Value
  | .direct => [i32 (condition true)]
  | _ => rootArgs

private def scratch : BranchKind → List Value
  | .direct => savedPrefix ++ rootArgs
  | _ => savedPrefix

private def skipped : BranchKind → List Admin
  | .conditional => expression (entry.sourceCode onZero)
  | _ => []

private theorem selected (kind : BranchKind) :
    Runs kind (.call (region kind)) (.branching (firstBytes true) (branchStack kind) target (skipped kind) labels) := by
  cases kind with
  | direct => exact reachesControl .direct true
  | conditional =>
    have nonzero : condition true ≠ (0 : BitVec 32) := by decide
    exact (reachesControl .conditional true).tail (.branchNonzero nonzero)
  | table => exact (reachesControl .table true).tail .selectTable

private def atFunction (kind : BranchKind) : Phase :=
  .branching (firstBytes true) (scratch kind ++ payload kind) { target with depth := ⟨0⟩ } (entry.tailCode outerLabel) []

private theorem reachesFunction (kind : BranchKind) : Runs kind (.call (region kind)) (atFunction kind) := by
  have crossed : Runs kind (.call (region kind))
      (.branching (firstBytes true) (branchStack kind) { target with depth := ⟨1⟩ } [] [outerLabel]) :=
    (selected kind).tail (.branchOuter (by decide))
  cases kind <;> exact crossed.tail (.branchOuter (by decide))

-- After the two explicit labels close, the branch still has to exit
-- the function label. Its skipped host and scratch values are visible.
example (kind : BranchKind) : Steps (host kind) (launch kind)
    ⟨live kind (firstBytes true), caller, [.frame 1 active
      [.label 1 [] (values (scratch kind ++ payload kind) ++ [.source (.br ⟨0⟩), .source (.call nextSite.index)])]]⟩ :=
  native (reachesFunction kind)

private theorem payloadTyped (kind : BranchKind) : (payload kind).map Value.type = branchFn.declaration.results := by
  cases kind <;> rfl

private theorem payloadCount (kind : BranchKind) : (payload kind).length = 1 := by
  cases kind <;> rfl

private def resultFrame (kind : BranchKind) : State := ⟨firstBytes true, caller, [.frame 1 active (values (payload kind))]⟩

private theorem exitsLabel (kind : BranchKind) : Runs kind (.call (region kind)) (.graph (resultFrame kind)) :=
  (reachesFunction kind).tail (.branchFunction (payloadTyped kind))

-- Pure native function-label exit, read back as delivery inside the frame.
private theorem nativeExit (kind : BranchKind) : Step (host kind) (cfg kind (atFunction kind)) (cfg kind (.graph (resultFrame kind))) := by
  have move := Step.frame (Step.pure (host := host kind) (live kind (firstBytes true)) active
    (.labelBranch 1 [] (scratch kind) (payload kind) [.source (.call nextSite.index)] (payloadCount kind))) 1 caller
  simpa only [cfg, atFunction, resultFrame, Sequence.render, Sequence.afterLabel, Sequence.context, Sequence.insert,
    OpenLabel.labelArity, Execution.Runtime.EvalCtx.comp,
    Execution.Runtime.EvalCtx.plug, Memory32.render, values_append, List.append_assoc, List.singleton_append,
    expression, List.map_nil, List.append_nil] using! move

example (kind : BranchKind) :=
  (Sequence.v1_function_branch_step_iff (ready (reachesFunction kind))).mp (nativeExit kind)

example (kind : BranchKind) : Steps (host kind) (launch kind)
    ⟨live kind (firstBytes true), caller, [.frame 1 active (values (payload kind))]⟩ :=
  native (exitsLabel kind)

example (kind : BranchKind) :=
  (Sequence.v1_step_iff rfl (admitted kind) (layoutFor (region kind)) trivial rfl (contract kind)
    (ready (exitsLabel kind))).mp
    (show Step (host kind) (cfg kind (.graph (resultFrame kind)))
      ⟨live kind (firstBytes true), caller, values (payload kind)⟩ from
        .pure _ _ (.frameDone 1 active (payload kind) (payloadCount kind)))

-- Frame completion is a separate successor and restores the caller while
-- leaving the writer's Memory32 and the declared result in place.
example (kind : BranchKind) : Steps (host kind) (launch kind) ⟨live kind (firstBytes true), caller, values (payload kind)⟩ :=
  native ((exitsLabel kind).tail (.graph (.pure (.frameDone 1 active (payload kind) (payloadCount kind)))))

-- The zero case of the same conditional reaches its host instead of
-- unwinding any label or the enclosing frame.
example : Steps (host .conditional) (launch .conditional)
    ⟨live .conditional (firstBytes false), caller, [.frame 1 active [.label 1 []
      (values savedPrefix ++ [.label 1 [] [.label 1 [] (values rootArgs ++ [.invoke middleSite.address])],
        .source (.call nextSite.index)])]]⟩ := by
  have continued : Runs .conditional (.call (region .conditional))
      (.computing (firstBytes false) rootArgs [] middleSite [] labels) :=
    (reachesControl .conditional false).tail .branchZero
  exact native (continued.tail (.hostResolve (saved := []) rfl))

-- The actual i64 suffix fits the annotation but disagrees with the
-- enclosing function's declared i32 result.
example : entry.checkSource (Prefix.stackTypes savedPrefix) branchFn.declaration.results branchFn.entryLabels
    (.br ⟨⟨0⟩, [.int .i64]⟩) = false := rfl

end FunctionTarget


namespace VoidLoop

private def target : ForwardBranch := ⟨⟨0⟩, []⟩
private def test (branch : ForwardBranch) : Source Nat := .brIf branch (.plain [])
private def iteration (branch : ForwardBranch) : Source Nat := .hostsThen ⟨[.get ⟨0⟩], first⟩ [] (test branch)
private def tail : Source Nat := .hosts ⟨[.get ⟨0⟩], nextSite⟩ []
private def region (branch : ForwardBranch) : Source Nat := .loopThen (iteration branch) tail
private def body : Source Nat := region target
private abbrev allocation := allocationFor body
private abbrev live := liveFor body
private def scope : OpenLabel Nat := .loop savedPrefix (iteration target) tail

private def hostForBody (region : Source Nat) : HostSemantics Nat := fun id store operands answer =>
  (id = first.target ∧ operands = rootArgs ∧
    ((store = liveFor region initial.data ∧ answer = .returned (liveFor region (firstBytes false)) (.values [i32 1])) ∨
      (store = liveFor region (firstBytes false) ∧
        (answer = .returned (liveFor region (firstBytes true)) (.values [i32 0]) ∨
          answer = .returned (liveFor region (firstBytes true)) .trap)))) ∨
  (id = nextSite.target ∧ store = liveFor region (firstBytes true) ∧ operands = savedPrefix ++ rootArgs ∧
    answer = .returned store (.values [i32 (word true)]))

private abbrev host := hostForBody body

private theorem siteOf {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites body) :
    site = first ∨ site = nextSite := by
  change site ∈ [first, nextSite] at used
  simpa using used

private theorem admitted : entry.Checked .fixed graph slot .ranked allocation caller rootArgs body :=
  admittedFor body (fun _ used => (siteOf used).imp id Or.inr) rfl (by
    refine ⟨trivial, ?_⟩
    intro _ used
    cases used)

private abbrev layout := layoutFor body

private theorem contractForBody (region : Source Nat)
    (sites : ∀ site ∈ entry.sourceSites region, site = first ∨ site = nextSite) :
    entry.Contract (hostForBody region) .fixed slot initial (allocationFor region) region := by
  intro site used bytes _ operands _ after result outcome
  have signature : site.signature.results = [.int .i32] := by rcases sites site used with rfl | rfl <;> rfl
  rcases outcome with ⟨_, _, ⟨store, equal⟩ | ⟨store, equal | trap⟩⟩ | ⟨_, store, _, equal⟩
  · cases equal
    rw [store, signature]
    exact ⟨rfl, initial.data, firstBytes false, rfl, rfl, rfl⟩
  · cases equal
    rw [store, signature]
    exact ⟨rfl, firstBytes false, firstBytes true, rfl, rfl, rfl⟩
  · cases trap
    rw [store]
    exact ⟨trivial, firstBytes false, firstBytes true, rfl, rfl, rfl⟩
  · cases equal
    rw [store, signature]
    exact ⟨rfl, firstBytes true, firstBytes true, rfl, rfl, rfl⟩

private theorem contract : entry.Contract host .fixed slot initial allocation body :=
  contractForBody body (fun _ => siteOf)

private abbrev Runs := entry.Runs host .fixed graph slot allocation initial initial.data caller rootArgs
private abbrev cfg := entry.render allocation slot initial initial.data caller rootArgs
private def launch : Config Nat := ⟨live initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private theorem ready {phase : Phase} (run : Runs (.call body) phase) : entry.Ready .fixed graph slot .ranked initial phase body := by
  induction run with
  | refl => rfl
  | tail _ step ih => exact step.ready rfl admitted layout rfl contract ih

private theorem native {phase : Phase} (run : Runs (.call body) phase) : Steps host launch (cfg phase) :=
  (Sequence.v1_call_run_iff rfl admitted layout trivial rfl contract).mpr ⟨phase, run, ready run, rfl⟩

private def pending (bytes : ByteArray) : Phase := .pending bytes [] rootArgs first [] [scope] (some (test target))

private theorem entersIteration {bytes : ByteArray}
    (run : Runs (.call body) (.loop bytes savedPrefix (iteration target) tail [])) :
    Runs (.call body) (pending bytes) :=
  ((run.tail .openLoop).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private theorem firstRun : Runs (.call body) (pending initial.data) :=
  entersIteration ((Relation.ReflTransGen.single .resolve).tail .enter)

private def selected : Phase := .branching (firstBytes false) [] target [] [scope]

private theorem takesBranch : Runs (.call body) selected := by
  have returned : host first.target (live initial.data) rootArgs
      (.returned (live (firstBytes false)) (.values [i32 1])) := .inl ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  have tests : Runs (.call body) (.branchTest (firstBytes false) [i32 1] target (.plain []) [scope]) :=
    firstRun.tail (.returned returned rfl)
  exact tests.tail (.branchNonzero (saved := []) (condition := 1) (by decide))

private def reentry : Phase := .loop (firstBytes false) savedPrefix (iteration target) tail []
private def sourceLoop : Wasm.V1.Instr := .loop none (entry.sourceCode (iteration target))

-- A zero-depth branch reinstalls the source loop before the next entry step.
private theorem nativeRestart : Step host (cfg selected) (cfg reentry) :=
  .frame (.label (.context (.pure _ _ (.labelBranch 0 [sourceLoop] [] [] [] rfl))
    savedPrefix (expression (entry.sourceCode tail))) 1 []) 1 caller

example :=
  (Sequence.v1_step_iff rfl admitted layout trivial rfl contract (ready takesBranch)).mp nativeRestart

example : Steps host launch ⟨live (firstBytes false), caller, [.frame 1 active [.label 1 []
    (values savedPrefix ++ .source sourceLoop :: expression (entry.sourceCode tail))]]⟩ :=
  native (takesBranch.tail .restartLoop)

private theorem secondRun : Runs (.call body) (pending (firstBytes false)) :=
  entersIteration (takesBranch.tail .restartLoop)

-- The re-entered host sees the writer's returned memory and the same local.
example : Steps host launch ⟨live (firstBytes false), caller, [.frame 1 active [.label 1 []
    (values savedPrefix ++ .label 0 [sourceLoop] (values rootArgs ++ [.invoke first.address, .source (.brIf ⟨0⟩)]) ::
      expression (entry.sourceCode tail))]]⟩ :=
  native secondRun

private theorem reachesTail :
    Runs (.call body) (.pending (firstBytes true) [] (savedPrefix ++ rootArgs) nextSite []) := by
  have returned : host first.target (live (firstBytes false)) rootArgs
      (.returned (live (firstBytes true)) (.values [i32 0])) := .inl ⟨rfl, rfl, .inr ⟨rfl, .inl rfl⟩⟩
  have tests : Runs (.call body) (.branchTest (firstBytes true) [i32 0] target (.plain []) [scope]) :=
    secondRun.tail (.returned returned rfl)
  have finishes : Runs (.call body) (.completed (firstBytes true) [] scope []) := tests.tail (.branchZero (saved := []))
  exact ((finishes.tail (.closeLabel rfl)).tail (.numeric (.get rfl))).tail (.hostResolve (saved := []) rfl)

-- Zero finishes the live loop label. The later host sees its saved i64,
-- the preserved local i32, and the second iteration's bytes.
example : Steps host launch ⟨live (firstBytes true), caller, [.frame 1 active [.label 1 []
    (values (savedPrefix ++ rootArgs) ++ [.invoke nextSite.address])]]⟩ :=
  native reachesTail

example : Steps host launch ⟨live (firstBytes true), caller, values [i32 (word true)]⟩ := by
  have returned : host nextSite.target (live (firstBytes true)) (savedPrefix ++ rootArgs)
      (.returned (live (firstBytes true)) (.values [i32 (word true)])) := .inr ⟨rfl, rfl, rfl, rfl⟩
  have delivered := reachesTail.tail (.returned returned rfl)
  exact native ((delivered.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word true)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 active [i32 (word true)] rfl))))

-- A trap after restart retains the second store and discards both the
-- pending branch and the later host.
example : Steps host launch ⟨live (firstBytes true), caller, [.trap]⟩ := by
  have returned : host first.target (live (firstBytes false)) rootArgs
      (.returned (live (firstBytes true)) .trap) := .inl ⟨rfl, rfl, .inr ⟨rfl, .inr rfl⟩⟩
  have trapped : Runs (.call body) (.trapped (firstBytes true) [] [.source (.brIf ⟨0⟩)] [scope]) :=
    secondRun.tail (.returned returned rfl)
  have discarded : Runs (.call body) (.trapped (firstBytes true) [] [] [scope]) :=
    trapped.tail (.discard (.cut [] [] ([.source (.brIf ⟨0⟩)] : List Admin) [] (.inr (by decide))))
  have closed : Runs (.call body) (.trapped (firstBytes true) savedPrefix (entry.tailCode scope) []) :=
    discarded.tail .closeTrap
  have clean : Runs (.call body) (.trapped (firstBytes true) [] []) :=
    closed.tail (.discard (.cut [] savedPrefix (entry.tailCode scope) [] (.inl (by decide))))
  exact native ((clean.tail .closeTrap).tail (.graph (.pure (.frameTrap 1 active))))

private abbrev check := entry.checkSource (Prefix.stackTypes savedPrefix) branchFn.declaration.results branchFn.entryLabels

example : check (region { target with depth := ⟨2⟩ }) = false := rfl
example : check (region { target with results := [.int .i32] }) = false := rfl


namespace ScalarLoop

private def iteration (branch : ForwardBranch) : Source Nat :=
  .hostsThen ⟨[.get ⟨0⟩, .get ⟨0⟩], first⟩ [] (test branch)
private def tail : Source Nat := .hosts ⟨[], nextSite⟩ []
private def body : Source Nat := .loopThen (iteration target) tail scalar
private abbrev allocation := allocationFor body
private abbrev live := liveFor body
private abbrev host := hostForBody body
private def scope : OpenLabel Nat := .loop savedPrefix (iteration target) tail scalar

private theorem sites {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites body) :
    site = first ∨ site = nextSite := by
  change site ∈ [first, nextSite] at used
  simpa using used

private theorem admitted : entry.Checked .fixed graph slot .ranked allocation caller rootArgs body :=
  admittedFor body (fun _ used => (sites used).imp id Or.inr) rfl (by
    refine ⟨trivial, ?_⟩
    intro _ used
    cases used)

private abbrev layout := layoutFor body
private theorem contract : entry.Contract host .fixed slot initial allocation body :=
  contractForBody body (fun _ => sites)

private abbrev Runs := entry.Runs host .fixed graph slot allocation initial initial.data caller rootArgs
private abbrev cfg := entry.render allocation slot initial initial.data caller rootArgs
private def launch : Config Nat := ⟨live initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private theorem ready {phase : Phase} (run : Runs (.call body) phase) : entry.Ready .fixed graph slot .ranked initial phase body := by
  induction run with
  | refl => rfl
  | tail _ step ih => exact step.ready rfl admitted layout rfl contract ih

private theorem native {phase : Phase} (run : Runs (.call body) phase) : Steps host launch (cfg phase) :=
  (Sequence.v1_call_run_iff rfl admitted layout trivial rfl contract).mpr ⟨phase, run, ready run, rfl⟩

private def pending (bytes : ByteArray) : Phase := .pending bytes rootArgs rootArgs first [] [scope] (some (test target))

private theorem entersIteration {bytes : ByteArray}
    (run : Runs (.call body) (.loop bytes savedPrefix (iteration target) tail [] scalar)) :
    Runs (.call body) (pending bytes) :=
  (((run.tail .openLoop).tail (.numeric (.get rfl))).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private theorem firstRun : Runs (.call body) (pending initial.data) :=
  entersIteration ((Relation.ReflTransGen.single .resolve).tail .enter)

private def selected : Phase := .branching (firstBytes false) rootArgs target [] [scope]

private theorem takesBranch : Runs (.call body) selected := by
  have returned : host first.target (live initial.data) rootArgs
      (.returned (live (firstBytes false)) (.values [i32 1])) := .inl ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  have tests : Runs (.call body)
      (.branchTest (firstBytes false) (rootArgs ++ [i32 1]) target (.plain []) [scope]) :=
    firstRun.tail (.returned returned rfl)
  exact tests.tail (.branchNonzero (condition := 1) (by decide))

private def sourceLoop : Wasm.V1.Instr := .loop scalar (entry.sourceCode (iteration target))
private def restart : Phase := .loop (firstBytes false) savedPrefix (iteration target) tail [] scalar

-- Despite the scalar result and the i32 below the condition, the restarted
-- label accepts zero values. The native successor reinstalls the source loop.
private theorem nativeRestart : Step host (cfg selected) (cfg restart) :=
  .frame (.label (.context (.pure _ _ (.labelBranch 0 [sourceLoop] rootArgs [] [] rfl))
    savedPrefix (expression (entry.sourceCode tail))) 1 []) 1 caller

example := (Sequence.v1_loop_restart_iff.mp nativeRestart)

private theorem secondRun : Runs (.call body) (pending (firstBytes false)) :=
  entersIteration (takesBranch.tail .restartLoop)

example : Steps host launch ⟨live (firstBytes false), caller, [.frame 1 active [.label 1 []
    (values savedPrefix ++ .label 0 [sourceLoop]
      (values (rootArgs ++ rootArgs) ++ [.invoke first.address, .source (.brIf ⟨0⟩)]) ::
      expression (entry.sourceCode tail))]]⟩ :=
  native secondRun

private def completed : Phase := .completed (firstBytes true) rootArgs scope []

private theorem finishes : Runs (.call body) completed := by
  have returned : host first.target (live (firstBytes false)) rootArgs
      (.returned (live (firstBytes true)) (.values [i32 0])) := .inl ⟨rfl, rfl, .inr ⟨rfl, .inl rfl⟩⟩
  have tests : Runs (.call body)
      (.branchTest (firstBytes true) (rootArgs ++ [i32 0]) target (.plain []) [scope]) :=
    secondRun.tail (.returned returned rfl)
  exact tests.tail (.branchZero (saved := rootArgs))

private def tailComputing : Phase := .computing (firstBytes true) (savedPrefix ++ rootArgs) [] nextSite []

-- Normal completion of the same zero-arity label delivers one scalar
-- above the saved outer operand and retains the live post-host store.
private theorem nativeFallthrough : Step host (cfg completed) (cfg tailComputing) :=
  .frame (.label (.context (.pure _ _ (.labelDone 0 [sourceLoop] rootArgs))
    savedPrefix (expression (entry.sourceCode tail))) 1 []) 1 caller

example := (Sequence.v1_loop_fallthrough_iff (ready finishes)).mp nativeFallthrough

private theorem reachesTail :
    Runs (.call body) (.pending (firstBytes true) [] (savedPrefix ++ rootArgs) nextSite []) := by
  have resumed : Runs (.call body) tailComputing := finishes.tail (.closeLabel rfl)
  exact resumed.tail (.hostResolve (saved := []) rfl)

example : Steps host launch ⟨live (firstBytes true), caller, [.frame 1 active [.label 1 []
    (values (savedPrefix ++ rootArgs) ++ [.invoke nextSite.address])]]⟩ :=
  native reachesTail

example : Steps host launch ⟨live (firstBytes true), caller, values [i32 (word true)]⟩ := by
  have returned : host nextSite.target (live (firstBytes true)) (savedPrefix ++ rootArgs)
      (.returned (live (firstBytes true)) (.values [i32 (word true)])) := .inr ⟨rfl, rfl, rfl, rfl⟩
  have delivered := reachesTail.tail (.returned returned rfl)
  exact native ((delivered.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word true)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 active [i32 (word true)] rfl))))

private abbrev check := entry.checkSource (Prefix.stackTypes savedPrefix) branchFn.declaration.results branchFn.entryLabels

-- An i32 is available below the condition and is the declared result.
-- The restart signature must still be empty.
example : check (.loopThen (iteration { target with results := [.int .i32] }) tail scalar) = false := rfl

-- The adjusted tail accepts an i64 result. The loop body supplies i32.
private def i64Tail : Source Nat :=
  .hosts ⟨[], { nextSite with signature.params := [.int .i64, .int .i64] }⟩ []

example : check (.loopThen (iteration target) i64Tail (some (.int .i64))) = false := rfl

end ScalarLoop

end VoidLoop

end ConditionalBranch

end EnclosingTail
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.SequenceExamples
