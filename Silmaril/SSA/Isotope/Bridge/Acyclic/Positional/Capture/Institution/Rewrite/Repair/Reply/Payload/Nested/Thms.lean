module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Recovery
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Replay

/-! # Native replay and validated reflection for nested payload requests -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested

local notation "J" => Kleisli.J (m := Trace)

/-- Replay both case bindings and the payload tables under the actual
native binders and the shared packed-exit continuation. -/
theorem derive_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : p.normal = q.normal) : Derivable false (equation H L p q) :=
  derive_normal_proof H L p q h

theorem derive_render (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Derivable false (equation H L p p.normal.render) :=
  derive_render_proof H L p

/-- Evaluation of the native packed term gives the independently specified
trace paths. Each executed request contributes one tag and payload pair. -/
theorem programOutcomes_eq (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    programOutcomes H L p = p.normal.outcomes :=
  programOutcomes_proof H L p

/-- The observation recovers all reachable request paths, including the
ordered effects and typed exits selected by both reply values. -/
theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    programOutcomes H L p = programOutcomes H L q ↔ p.normal = q.normal := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => outcomes_injective_proof _ h, congrArg Normal.outcomes⟩

/-- Reading the outer reply leaves the chosen outer arm's observation
with the exact retained value, including any nested request. -/
theorem programAfterOuter (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L))
    (right b : Bool) :
    afterPayload p.request right b (programOutcomes H L p) =
      ((if right then p.normal.right else p.normal.left).traceTree b).outcomesWith Exits.Exit.packed := by
  rw [programOutcomes_eq]
  cases right <;> exact afterRequest Exits.Exit.packed p.request p.normal.left.traceTree p.normal.right.traceTree _ b

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ p.normal = q.normal :=
  (Payload.separator_sat_iff _).trans
    ⟨fun h => (programOutcomes_iff_normal H L p q).mp (programOutcomes_eq_of_sat_proof H L p q h),
      fun h => Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative (derive_normal H L p q h))⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Repaired false (equation H L p q) :=
  ⟨fun h => Repaired.ofNative (derive_normal H L p q ((separator_sat_iff_normal H L p q).mp h)),
    fun h => (Payload.separator_sat_iff _).mpr
      (Kleisli.sat_of_repaired model model_respectsPure _ h)⟩

/-- Validity in the unchanged room reflects to native derivability on
this grammar of at most two requests along each path. -/
theorem derive_of_validated_valid (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Derivable false (equation H L p q) :=
  derive_normal H L p q ((separator_sat_iff_normal H L p q).mp (valid separator))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested
