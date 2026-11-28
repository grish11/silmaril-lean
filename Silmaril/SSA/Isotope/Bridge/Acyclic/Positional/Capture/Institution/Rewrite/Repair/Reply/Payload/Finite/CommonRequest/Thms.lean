module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Factor
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Recovery
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Replay

/-! # Factoring and reflection of guarded common requests -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)
open Kleisli (value)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "J" => Kleisli.J (m := Trace)

/-- A shared computation in the ambient context can run before testing a
bound bit. The two continuations have the same result binder, and weakening
moves them across the test's unit binder without giving them access to it. -/
theorem factor_common {k : Nat} {β : BoundCtx Sorts k} {i : Fin k} {A B : Sorts}
    {q : Tm Empty signature.Instr k} {l r : Tm Empty signature.Instr (k + 1)}
    (hd : HasType signature.Instr Γ₀ β (.bv i) Bit)
    (hq : HasType signature.Instr Γ₀ β q A)
    (hl : HasType signature.Instr Γ₀ (β.snoc A) l B)
    (hr : HasType signature.Instr Γ₀ (β.snoc A) r B) :
    Equiv false Γ₀ β (.case (.bv i) (.let₁ q.lift l.underBinder) (.let₁ q.lift r.underBinder))
      (.let₁ q (.case (.bv i.succ) l.lift r.lift)) B :=
  factor_proof hd hq hl hr

/-- Move the pure test past the common request in the actual open terms. -/
theorem factor_request {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (req : Bool) (arms : Arms L n) (slots : Retained β (n + 1)) (test : Fin (n + 1)) :
    Equiv false Γ₀ β ((Source.mk req false arms).operand slots test).1
      ((Source.mk req true arms).operand slots test).1 (packedExitType L) :=
  factor_source_proof req arms slots test

theorem Source.replay {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (p : Source L n) (slots : Retained β (n + 1)) (test : Fin (n + 1)) :
    Equiv false Γ₀ β (p.operand slots test).1 (p.normal.render.operand slots test).1 (packedExitType L) :=
  source_replay_proof p slots test

theorem derive_normal (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n) (h : p.normal = q.normal) :
    Derivable false (equation H L test p q) :=
  derive_normal_proof H L test p q h

/-- Reading one reply of the common request exposes the trace of the
continuation selected by the retained guard and the reply tag. -/
theorem NormalSource.afterRequest {L : List Sorts} {n : Nat} (p : NormalSource L n) (test : Fin (n + 1))
    (env : Assignment (n + 1)) (right b : Bool) :
    afterPayload p.request right b (p.outcomes test env) =
      (if env test then (if right then p.arms.trueRight else p.arms.trueLeft)
        else (if right then p.arms.falseRight else p.arms.falseLeft)).outcomes ((env.without test).push b) :=
  after_request_proof p test env right b

theorem bitSlots_matches (n : Nat) (env : Assignment n) :
    (bitSlots n).Matches (boundEnv value (packedAssignment n env)) env :=
  bitSlots_matches_proof n env

theorem programOutcomes_eq (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p : Source (H :: L) n) (env : Assignment (n + 1)) :
    programOutcomes H L test p env = p.normal.outcomes test env :=
  programOutcomes_proof H L test p env

/-- With the test slot fixed, all assignments recover both continuations
for both reply tags. This also permits the guard to be observationally irrelevant. -/
theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n) :
    (∀ env, programOutcomes H L test p env = programOutcomes H L test q env) ↔ p.normal = q.normal := by
  simp only [programOutcomes_eq]
  exact ⟨normal_inj_proof test p.normal q.normal, fun h env => congrArg (fun r => r.outcomes test env) h⟩

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n) :
    (grammarRoom J signature).Sat separator (equation H L test p q) ↔ p.normal = q.normal :=
  (Payload.separator_sat_iff _).trans
    ⟨fun h => (programOutcomes_iff_normal H L test p q).mp (programOutcomes_eq_of_sat_proof H L test p q h),
      fun h => Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative (derive_normal H L test p q h))⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n) :
    (grammarRoom J signature).Sat separator (equation H L test p q) ↔ Repaired false (equation H L test p q) :=
  ⟨fun h => Repaired.ofNative (derive_normal H L test p q ((separator_sat_iff_normal H L test p q).mp h)),
    fun h => (Payload.separator_sat_iff _).mpr (Kleisli.sat_of_repaired model model_respectsPure _ h)⟩

theorem derive_of_validated_valid (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n)
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L test p q)) :
    Derivable false (equation H L test p q) :=
  derive_normal H L test p q ((separator_sat_iff_normal H L test p q).mp (valid separator))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
