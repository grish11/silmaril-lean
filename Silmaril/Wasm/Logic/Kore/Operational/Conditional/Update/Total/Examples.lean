module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Total.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Native

abbrev local0 : LocalIdx := ⟨⟨0, by decide⟩⟩
abbrev local1 : LocalIdx := ⟨⟨1, by decide⟩⟩
def frame (q k : BitVec 32) : Frame := { locals := [some (Val.i32 q), some (Val.i32 k)] }

def layout : Layout where
  entry := "a"
  zero := "b"
  nonzero := "c"
  entry_ne_zero := by decide
  entry_ne_nonzero := by decide
  zero_ne_nonzero := by decide
  blockType := .empty
  zeroBody := BodyDraft.assignBody local1 (BitVec.ofInt 32 11)
  nonzeroBody := BodyDraft.assignBody local1 (BitVec.ofInt 32 13)
  tailCode _ := []

/-- Fully initialized premises are jointly satisfiable. For every input i32
condition/counter, the real update hits its post-state and then really diverges. -/
theorem concrete_progress_and_divergence {H : Type} (P : Profile) (host : HostSemantics H)
    (s : Store H) (q k : BitVec 32) :
    Silmaril.Logic.CTL.AllEventually (Core.Step P host)
      (postRelated layout s (frame q k) [] [] [.plain loopBody] local0 local1 q 11 13
        (afterSource layout [] q 11 13))
      (native layout .entry s (frame q k) [] [] [.plain loopBody] local0) ∧
      Core.Diverges P host (native layout .entry s (frame q k) [] [] [.plain loopBody] local0) :=
  entry_eventual_with_loop_divergence layout P host s (frame q k) [] [.plain loopBody]
    local0 local1 q k 11 13 (by decide) (by change (1 : Nat) < 2; decide) ⟨rfl, rfl⟩ rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) rfl

/-- The same concrete actual source step reaches the graph's pointed matching
endpoint with the stronger AF meaning, even with a looping continuation. -/
theorem concrete_source_matching {H : Type} (P : Profile) (host : HostSemantics H)
    (s : Store H) (q k : BitVec 32) :
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (predicateModel P host (native layout .entry s (frame q k) [] [] [.plain loopBody] local0)
          (postRelated layout s (frame q k) [] [] [.plain loopBody] local0 local1 q 11 13
            (afterSource layout [] q 11 13))))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal eventuallyTarget.toMu) :=
  source_entry_matching layout P host s (frame q k) [] [] [.plain loopBody]
    local0 local1 q k 11 13 (by decide) (by change (1 : Nat) < 2; decide) ⟨rfl, rfl⟩ rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) _
    ((source_step_iff layout [] q k 11 13 _).mpr rfl)

/-- Empty initialization still fails the stronger claim on the actual native
entry, using the already established finite-path deadlock counterexample. -/
theorem empty_frame_no_progress {H : Type} (P : Profile) (host : HostSemantics H)
    (s : Store H) (q : BitVec 32) :
    ¬ Silmaril.Logic.CTL.AllEventually (Core.Step P host)
      (postRelated layout s {} [] [] [] local0 local1 q 11 13
        (afterSource layout [] q 11 13))
      (native layout .entry s {} [] [] [] local0) :=
  fun total => NativeAllPath.empty_frame_counterexample layout P host s
    local0 local1 q 11 13 total.2

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples
