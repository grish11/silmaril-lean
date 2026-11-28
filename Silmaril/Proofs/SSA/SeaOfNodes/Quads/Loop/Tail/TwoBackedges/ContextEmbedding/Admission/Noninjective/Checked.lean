module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Defs

/-! Check the concrete intersections, FIFO rows, and compiler refusals in the kernel. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Proofs

open Identification (pushFacts)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)

theorem suffix_identifies :
    first _ seed ≠ first _ multiplier ∧ second _ (first _ seed) = second _ (first _ multiplier) :=
  ⟨fun same => (show (2 : Nat) ≠ 3 by decide) (congrArg slot same), rfl⟩

theorem writeChecks_exact : writeChecks = (true, true, true) := rfl

theorem intersections_exact :
    pushFacts first oldFacts = some middleFacts ∧
    pushFacts second middleFacts = some finalFacts ∧
    pushFacts composed oldFacts = some finalFacts :=
  ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem rows_exact :
    rows = some [⟨.overdefined, .overdefined, .overdefined, .overdefined, [true, true, false, true]⟩,
      ⟨.overdefined, .constant 7, .overdefined, .overdefined, [true, true, false, true]⟩,
      ⟨.constant 1, .constant 7, .constant 7, .constant ⟨false⟩, [true, false, false, true]⟩,
      ⟨.constant 1, .constant 7, .constant 7, .constant ⟨false⟩, [true, false, false, true]⟩] := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem outcomes_exact :
    outcomes = some ⟨.ok true, .error (.second (.checker .neitherMarked)), .error (.checker .neitherMarked)⟩ := rfl

private theorem map_refuses {A B E : Type} (answer : Except E A) (f : A → B) (reason : E)
    (refused : answer.map f = .error reason) : answer = .error reason := by
  cases answer <;> simp_all [Except.map]

theorem compiler_differential :
    ∃ (source : AdmittedAt old width) (intermediate : Generated middle width),
      original = .ok source ∧
      Identification.compile first source = .ok intermediate ∧
      selectedSide intermediate.source = true ∧
      Identification.compile second intermediate.source = .error (.checker .neitherMarked) ∧
      LiftComposition.compare first second source = .error (.second (.checker .neitherMarked)) ∧
      Identification.compile composed source = .error (.checker .neitherMarked) := by
  cases seeded : original with
  | error reason =>
    have observed := outcomes_exact
    simp [outcomes, seeded, Except.toOption] at observed
  | ok source =>
    have observed := outcomes_exact
    simp only [outcomes, seeded, Except.toOption] at observed
    have observed : Outcomes.mk
        ((Identification.compile first source).map (fun p => selectedSide p.source))
        ((LiftComposition.compare first second source).map (fun p => selectedSide p.staged.source))
        ((Identification.compile composed source).map (fun p => selectedSide p.source)) =
        ⟨.ok true, .error (.second (.checker .neitherMarked)), .error (.checker .neitherMarked)⟩ :=
      Option.some.inj observed
    have firstTag := congrArg Outcomes.first observed
    have staged := map_refuses _ _ _ (congrArg Outcomes.staged observed)
    have direct := map_refuses _ _ _ (congrArg Outcomes.direct observed)
    cases firstOk : Identification.compile first source with
    | error reason =>
      change (Identification.compile first source).map _ = .ok true at firstTag
      rw [firstOk] at firstTag
      cases firstTag
    | ok mid =>
      change (Identification.compile first source).map _ = .ok true at firstTag
      rw [firstOk] at firstTag
      have side := Except.ok.inj firstTag
      have secondRefuses : Identification.compile second mid.source = .error (.checker .neitherMarked) := by
        unfold LiftComposition.compare at staged
        split at staged
        · cases staged
        · rename_i intermediate ran
          have same := Except.ok.inj (ran.symm.trans firstOk)
          subst intermediate
          split at staged
          · rename_i reason refused
            cases staged
            exact refused
          · split at staged <;> cases staged
      exact ⟨source, mid, rfl, firstOk, side, secondRefuses, staged, direct⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Proofs
