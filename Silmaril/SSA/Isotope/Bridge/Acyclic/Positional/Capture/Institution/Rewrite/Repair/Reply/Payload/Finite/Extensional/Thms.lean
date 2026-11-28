module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Cover
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Observe
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Specialize

/-! # Extensional native reflection at finite retained assignments -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional

open Isotope.LetCase.LocallyNameless (Equiv HasType PureTypedSubst Tm)
open LambdaSSA.Region (packedExitType)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "J" => Kleisli.J (m := Trace)
local notation "Term" => Tm Empty signature.Instr

/-- Reassemble both constructor specializations under the actual bit
binder. The ambient context and result may be arbitrary. -/
theorem bit_ext {k : Nat} {β : BoundCtx Sorts k} {A : Sorts} {t u : Term (k + 1)}
    (ht : HasType signature.Instr Γ₀ (β.snoc Bit) t A)
    (hu : HasType signature.Instr Γ₀ (β.snoc Bit) u A)
    (lo : Equiv false Γ₀ β (t.instantiate (.inl .unit)) (u.instantiate (.inl .unit)) A)
    (hi : Equiv false Γ₀ β (t.instantiate (.inr .unit)) (u.instantiate (.inr .unit)) A) :
    Equiv false Γ₀ (β.snoc Bit) t u A :=
  bit_ext_proof ht hu lo hi

/-- An assignment substitutes just the retained bits. Under each executed
request the proof specializes its two reply constructors inside the
continuation, using the same single request at the original effect position. -/
theorem Source.specialize {L : List Sorts} {n k m : Nat}
    {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} (p : Source L n) (slots : Retained β n)
    {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (env : Assignment n) (h : assignmentMatches γ slots σ env) :
    Equiv false Γ₀ γ ((p.operand slots).1.bsubst σ) ((p.normal env).operand γ).1 (packedExitType L) :=
  specialize_source_proof p slots s env h

/-- Replay pointwise equality of the assignment normal form on the native
packed witnesses, even when the original tests use different slots. -/
theorem derive_normal (H : Sorts) (L : List Sorts) {n : Nat} (p q : Source (H :: L) n)
    (h : ∀ env, p.normal env = q.normal env) : Derivable false (equation H L p q) :=
  derive_normal_proof H L p q h

theorem Path.traceTree_injective (L : List Sorts) : Function.Injective (@Path.traceTree L) :=
  path_trace_inj_proof L

/-- At any retained assignment, the open packed program agrees with the
finite tree's observations in the same native bit context and exit list. -/
theorem tree_programOutcomes_eq (H : Sorts) (L : List Sorts) {n : Nat}
    (t : Tree (H :: L) n) (env : Assignment n) :
    programOutcomes H L (.tree t) env = t.normal.outcomes env :=
  tree_programOutcomes_proof H L t env

theorem programOutcomes_eq (H : Sorts) (L : List Sorts) {n : Nat}
    (p : Source (H :: L) n) (env : Assignment n) :
    programOutcomes H L p env = (p.normal env).traceTree.outcomesWith Exits.Exit.packed :=
  programOutcomes_proof H L p env

theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) {n : Nat}
    (p q : Source (H :: L) n) (env : Assignment n) :
    programOutcomes H L p env = programOutcomes H L q env ↔ p.normal env = q.normal env := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => Path.traceTree_injective _
    (Reply.Normal.outcomesWith_injective _ (Exits.Exit.packed_injective _) h), fun h => by rw [h]⟩

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) {n : Nat} (p q : Source (H :: L) n) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ ∀ env, p.normal env = q.normal env :=
  (Payload.separator_sat_iff _).trans
    ⟨fun h env => (programOutcomes_iff_normal H L p q env).mp (programOutcomes_eq_of_sat_proof H L p q h env),
      fun h => Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative (derive_normal H L p q h))⟩

theorem separator_sat_iff_native (H : Sorts) (L : List Sorts) {n : Nat} (p q : Source (H :: L) n) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Derivable false (equation H L p q) :=
  ⟨fun h => derive_normal H L p q ((separator_sat_iff_normal H L p q).mp h),
    fun h => (Payload.separator_sat_iff _).mpr (Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative h))⟩

/-- Validity in the existing room reflects to native derivability on the
finite witnessed binary grammar with a retained bit context. -/
theorem derive_of_validated_valid (H : Sorts) (L : List Sorts) {n : Nat} (p q : Source (H :: L) n)
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Derivable false (equation H L p q) :=
  (separator_sat_iff_native H L p q).mp (valid separator)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional
