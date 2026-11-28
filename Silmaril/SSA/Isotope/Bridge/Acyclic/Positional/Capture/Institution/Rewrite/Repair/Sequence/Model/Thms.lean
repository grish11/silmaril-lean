module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Coherence.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Trace

/-! # Reflection on ordered effect sequences -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open Isotope.Semantics (BoundEnv)
open LetIter.Semantics.Categorical (boundEnv boundObj)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

theorem Body.run_operand (p : Body) {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) :
    run (p.operand β).2 ρ = p.normal.observe PUnit.unit :=
  operand_run_proof p ρ

theorem Normal.observe_injective {A : Type} (a : A) :
    Function.Injective (fun nf : Normal => nf.observe a) :=
  observe_injective_proof a

/-- Packing a successful unit result at exit zero preserves both the emitted
word and any terminal fault. -/
theorem run_tag_unit {B : Type} (a : Trace PUnit) :
    ((a >>= fun u => (pure (.inl u) : Trace (PUnit ⊕ B))).run.run) =
      (fun (result, word) => (result.map Sum.inl, word)) <$> a.run.run :=
  sum_tag_run_proof a

/-- Satisfaction implies agreement at each supplied concrete input. -/
theorem traceSat_run (e : GrammarEquation signature)
    (h : ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase e))
    (ρ : boundObj traceTypes e.1.bound) :
    run (grammarCase e).2.1.2 (boundEnv value ρ) =
      run (grammarCase e).2.2.2 (boundEnv value ρ) :=
  traceSat_run_proof e h ρ

/-- The full repaired relation at bottom effect is sound in this concrete
algebra, where all primitives are declared effectful. -/
theorem traceSat_of_repaired (e : GrammarEquation signature) (h : Repaired false e) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase e) :=
  traceSat_of_repaired_proof e h

/-- The concrete Freyd trace algebra observes the order of emits and the
identity of a terminating empty-producing operation. -/
theorem traceSat_iff_normal (tail : List Sorts) (p q : Body) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      p.normal = q.normal :=
  ⟨traceSat_normal_proof tail p q,
    fun h => traceSat_of_repaired _ (sequencesEmpty_of_normal tail p q h).repaired⟩

/-- The normal form decides the full opt-in relation on this slice. The
forward implication tests all repaired derivations in the trace algebra. -/
theorem repaired_iff_normal (tail : List Sorts) (p q : Body) :
    Repaired false (equation tail p q) ↔ p.normal = q.normal :=
  ⟨fun h => (traceSat_iff_normal tail p q).mp (traceSat_of_repaired _ h),
    fun h => (sequencesEmpty_of_normal tail p q h).repaired⟩

/-- Concrete satisfaction reflects back to the typed rewrite derivation
on these witnessed equations. -/
theorem traceSat_iff_repaired (tail : List Sorts) (p q : Body) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      Repaired false (equation tail p q) :=
  (traceSat_iff_normal tail p q).trans (repaired_iff_normal tail p q).symm

/-- The separator reflects validity in the existing validated room. -/
theorem validatedTrace_iff_repaired (tail : List Sorts) (p q : Body) :
    (∀ B : (grammarRoom traceJ signature).Mod, (grammarRoom traceJ signature).Sat B (equation tail p q)) ↔
      Repaired false (equation tail p q) :=
  ⟨fun h => (traceSat_iff_repaired tail p q).mp ((validatedTraceModel_sat_iff _).mp (h validatedTraceModel)),
    fun h => (sequencesEmpty_of_normal tail p q ((repaired_iff_normal tail p q).mp h)).sat⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
