module

import Silmaril.Wasm.Institution.Operational.HostCall.V1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.V1

open Execution.Runtime (Frame MemAddr MemInst Value HostOutcome)
open Wasm.V1.Execution
open CallContinuation.OuterCall.Ranked.Graph

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def signature : Wasm.V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩
private def site : Site Nat := ⟨⟨1⟩, ⟨0⟩, signature, 7⟩
private def slot : MemAddr := ⟨0⟩
private def memory : MemInst := ⟨⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩, none⟩
private def base : Store Nat := { funcs := [.host signature 7], memories := [memory] }
private def caller : Frame := ⟨[i32 91], { funcs := [⟨1⟩, site.address], memories := [slot] }⟩
private def saved : List Value := [i32 0]
private def args : List Value := [i64 81, i32 9]
private def recorded (answer : BitVec 32) : Frame := { caller with locals := [i32 answer] }
private def load : Admin := .source (.intLoad .i32 none (Memory32.immediate 1))
private def tail : List Admin := [.source (.localSet ⟨0⟩), load]
private def source : Config Nat := site.source base caller saved args tail
private def pending : Config Nat := site.pending base caller saved args tail

private def firstBytes : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def secondBytes : ByteArray := ⟨#[0xaa, 0x99, 0x88, 0x77, 0x66, 0xbb]⟩
private def firstStore : Store Nat := Memory32.storeWithBytes base slot memory firstBytes
private def secondStore : Store Nat := Memory32.storeWithBytes base slot memory secondBytes

private inductive HostAnswer : HostOutcome Wasm.V1.Func Nat → Prop
  | first : HostAnswer (.returned firstStore (.values [i32 7]))
  | second : HostAnswer (.returned secondStore (.values [i32 8]))
  | trap : HostAnswer (.returned secondStore .trap)
  | diverge : HostAnswer .diverged

-- The same concrete input admits two distinct answers, a trap and divergence.
private def host : HostSemantics Nat :=
  fun target s given answer => target = 7 ∧ s = base ∧ given = args ∧ HostAnswer answer

private theorem checked : site.Checked base caller args := ⟨rfl, rfl, rfl, by decide⟩

private def shared : Store Nat → Store Nat → Prop :=
  fun _ live => Memory32.SharedStore base slot memory live

private theorem contract : site.ReturnContract host shared base args := by
  rintro s r ⟨_, _, _, answer⟩
  cases answer with
  | first => exact ⟨rfl, firstBytes, rfl, rfl⟩
  | second => exact ⟨rfl, secondBytes, rfl, rfl⟩
  | trap => exact ⟨trivial, secondBytes, rfl, rfl⟩

example : ¬ site.Checked base caller [i32 9, i64 81] := by
  intro bad
  cases bad.arguments

example : ¬ site.Checked base { caller with module := { caller.module with funcs := [site.address] } } args := by
  intro bad
  cases bad.resolved

example : ¬ site.Checked { base with funcs := [.host signature 8] } caller args := by
  intro bad
  cases bad.allocated

private theorem resolve : Step host source pending :=
  (source_step_iff (site := site) (saved := saved) (args := args) (tail := tail) checked.resolved).mpr rfl

private theorem answerStep {s : Store Nat} {r : Execution.Runtime.Result}
    (answer : HostAnswer (.returned s r)) :
    Step host pending (resumed s caller saved tail r) :=
  (pending_step_iff (saved := saved) (tail := tail) checked).mpr (.inl ⟨s, r, ⟨rfl, rfl, rfl, answer⟩, rfl⟩)

private theorem loops : Step host pending pending :=
  (checked_pending_step_iff (saved := saved) (tail := tail) checked contract).mpr
    (.inr ⟨⟨rfl, rfl, rfl, .diverge⟩, rfl⟩)

example : Steps host source pending := (Relation.ReflTransGen.single resolve).tail loops

example {dst : Config Nat} : ¬ Step Execution.Runtime.noHostCalls pending dst := by
  intro step
  rcases (pending_step_iff (saved := saved) (tail := tail) checked).mp step with ⟨_, _, bad, _⟩ | ⟨bad, _⟩
  · exact bad
  · exact bad

-- The native caller observes the answer in its locals and the returned store
-- through the saved pointer. The two returns have different memory effects.
private theorem recordRead {s : Store Nat} {mem : MemInst} {answer word : BitVec 32}
    (allocated : frameMemory s (recorded answer) = some (slot, mem))
    (read : MemoryQuery.EdgeAt mem.data 1 (.load 0) (.value word)) :
    Steps host (resumed s caller saved tail (.values [i32 answer]))
      ⟨s, recorded answer, values [i32 word]⟩ := by
  have record : Step host (resumed s caller saved tail (.values [i32 answer]))
      ⟨s, recorded answer, values saved ++ [load]⟩ :=
    .context (.localSet s caller ⟨0⟩ (i32 answer) (i32 91) rfl) saved [load]
  have loadStep := (MemoryWrite.v1_context_load_step_iff_at (host := host) (immediate := Memory32.immediate 1)
    (address := 0) (saved := []) (tail := []) allocated).mpr ⟨.value word, read, rfl⟩
  exact (Relation.ReflTransGen.single record).tail loadStep

private def observedFirst : Config Nat := ⟨firstStore, recorded 7, values [i32 0x11223344]⟩
private def observedSecond : Config Nat := ⟨secondStore, recorded 8, values [i32 0x66778899]⟩
private theorem first : Steps host source observedFirst :=
  .head resolve (.head loops (.head (answerStep .first)
    (recordRead (show frameMemory firstStore (recorded 7) = some (slot, { memory with data := firstBytes }) from rfl)
      (MemoryQuery.fact_at (.load _ _ (by decide))))))
private theorem second : Steps host source observedSecond :=
  .head resolve (.head (answerStep .second)
    (recordRead (show frameMemory secondStore (recorded 8) = some (slot, { memory with data := secondBytes }) from rfl)
      (MemoryQuery.fact_at (.load _ _ (by decide)))))

private def trapped : Config Nat := ⟨secondStore, caller, [.trap]⟩
private theorem trap : Steps host source trapped :=
  .head resolve (.head (answerStep .trap) (.single (.pure _ _ (.trapValues (i32 0) [] tail))))

private theorem readback {dst : Config Nat} (run : Steps host source dst) (length : dst.code.length = 1) :
    ∃ s r, host site.target base args (.returned s r) ∧ ResultTyped signature.results r ∧
      Memory32.SharedStore base slot memory s ∧ Steps host (resumed s caller saved tail r) dst := by
  rcases (run_iff (saved := saved) (tail := tail) checked contract).mp run with same | same | answer
  · rw [same] at length
    cases length
  · rw [same] at length
    cases length
  · exact answer

example := readback first rfl
example := readback second rfl
example := readback trap rfl

-- The untyped native interface still allows these returns. Neither embedding
-- can supply the contract for this checked call.
private def wrongResult : HostSemantics Nat := fun _ _ _ out => out = .returned base (.values [i64 9])
private def wrongStore : Store Nat := { base with memories := [] }
private def removesMemory : HostSemantics Nat := fun _ _ _ out => out = .returned wrongStore (.values [i32 9])

example : Step wrongResult pending (resumed base caller saved tail (.values [i64 9])) :=
  (pending_step_iff (saved := saved) (tail := tail) checked).mpr (.inl ⟨_, _, rfl, rfl⟩)

example : ¬ site.ReturnContract wrongResult shared base args := by
  intro bad
  cases (bad base (.values [i64 9]) rfl).1

example : ¬ site.ReturnContract removesMemory shared base args := by
  intro bad
  obtain ⟨bytes, _, eq⟩ := (bad wrongStore (.values [i32 9]) rfl).2
  have lengths := congrArg (fun s : Store Nat => s.memories.length) eq
  change 0 = 1 at lengths
  cases lengths

end Silmaril.Wasm.Institution.Operational.HostCall.V1
