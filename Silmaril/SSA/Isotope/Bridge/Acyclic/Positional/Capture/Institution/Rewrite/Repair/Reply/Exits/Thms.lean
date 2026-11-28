module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Packing
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Reflection

/-! # Reflection at the original typed exit positions -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits

open Kleisli (value)
open Isotope.Semantics (BoundEnv InstructionModel)
open LambdaSSA (At Ren)
open LambdaSSA.Acyclic (Operand FiniteExit)
open LambdaSSA.Acyclic.Positional.Capture (Scope)
open LambdaSSA.Region (packedExitType)

local notation "J" => Kleisli.J (m := Trace)

section Packing

variable {P : InstrSig Sorts Bool} {m : Type → Type} [Monad m] [LawfulMonad m]
  (M : InstructionModel value P.Instr m)

theorem run_tag {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β)
    (L : List Sorts) (i : Nat) {A : Sorts} (h : At L i A) (x : value A)
    (a : Operand P.Instr β A) (ha : Kleisli.run M a.2 ρ = pure x) :
    Kleisli.run M (FiniteExit.tag L i h a).2 ρ = pure (packAt L i h x) :=
  tag_run_proof M ρ L i h x a ha

/-- A well-formed packed input is routed to the encoded image of its
original position with the same payload. -/
theorem run_router {K : List Sorts} {j : Nat} {D : Sorts} (fallback : At K j D)
    (L : List Sorts) {f : Nat → Nat} (ren : Ren L K f)
    {k n : Nat} {γ : BoundCtx Sorts k} {β : BoundCtx Sorts n}
    (s : Scope γ β) (ρ : BoundEnv value β)
    (i : Nat) {A : Sorts} (h : At L i A) (x : value A) :
    Kleisli.run M ((router fallback L ren).render s).encode.toLetCase.2
      (ρ.snoc (A := packedExitType L) (packAt L i h x)) = pure (packAt K (f i) (ren h) x) :=
  router_run_proof M fallback L ren s ρ i h x

end Packing

/-- The packed success value determines the position and its typed payload. -/
theorem Exit.packed_injective (L : List Sorts) : Function.Injective (@Exit.packed L) :=
  packed_injective_proof L

/-- The actual packed emitted terms replay the same case and abort rules
under the shared native exit continuation. -/
theorem repaired_of_normal (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L)))
    (h : p.normal = q.normal) : Repaired false (equation H L p q) :=
  repaired_of_normal_proof H L p q h

/-- Observations of the captured term retain the original outward tag in
each successful leaf. -/
theorem programOutcomes_eq (H : Sorts) (L : List Sorts) (p : Tree (Exit (H :: L))) :
    programOutcomes H L p = p.normal.outcomesWith Exit.packed :=
  programOutcomes_proof H L p

theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) :
    programOutcomes H L p = programOutcomes H L q ↔ p.normal = q.normal := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => Normal.outcomesWith_injective _ (Exit.packed_injective _) h,
    congrArg (Normal.outcomesWith Exit.packed)⟩

theorem programAfterReply (H : Sorts) (L : List Sorts) (req bound right : Bool)
    (l r : Tree (Exit (H :: L))) :
    afterReply req right (programOutcomes H L (.ask req bound l r)) =
      programOutcomes H L (if right then r else l) := by
  rw [programOutcomes_eq, programOutcomes_eq, Tree.normal]
  have h := Normal.afterReply_outcomesWith (@Exit.packed (H :: L)) req right l.normal r.normal
  cases right <;> exact h

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ p.normal = q.normal :=
  (Reply.separator_sat_iff _).trans
    ⟨fun h => (programOutcomes_iff_normal H L p q).mp (programOutcomes_eq_of_sat_proof H L p q h),
      fun h => Kleisli.sat_of_repaired model model_respectsPure _ (repaired_of_normal H L p q h)⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Repaired false (equation H L p q) :=
  ⟨fun h => repaired_of_normal H L p q ((separator_sat_iff_normal H L p q).mp h),
    fun h => (Reply.separator_sat_iff _).mpr (Kleisli.sat_of_repaired model model_respectsPure _ h)⟩

theorem repaired_of_validated_valid (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L)))
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Repaired false (equation H L p q) :=
  (separator_sat_iff_repaired H L p q).mp (valid separator)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits
