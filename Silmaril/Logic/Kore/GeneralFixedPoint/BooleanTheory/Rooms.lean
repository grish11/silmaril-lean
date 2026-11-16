module

public import Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
open CategoryTheory Silmaril.Logic.Institution
open Predicates

namespace Package
variable (p : Package)

/-- Source models retain all declared total-singleton contracts. -/
def sourceRoom : Room :=
  ⟨Sentence p.source.scope, Cat.of (Model p), fun M q => q.Satisfies M.base⟩

/-- Native sentences are whole families. Models are precisely canonical
expansions of source models, not arbitrary definedness graphs. -/
def nativeRoom : Room :=
  ⟨Set (Matching.GeneralFixedPoint.Sentence (Predicates.signature p.source.scope)),
    Cat.of (Model p), fun M Q => ∀ q ∈ Q,
      Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q⟩

def lowering : Corridor p.sourceRoom p.nativeRoom :=
  ⟨Sentence.lower, 𝟭 _, fun M q => (q.lower_satisfies M.base).symm⟩

theorem lowering_modelExpansive : p.lowering.ModelExpansive :=
  fun M => ⟨M, rfl⟩

def lowerTheory (H : Set (Sentence p.source.scope)) :
    Set (Matching.GeneralFixedPoint.Sentence (Predicates.signature p.source.scope)) :=
  {q | ∃ a ∈ H, q ∈ a.lower}

theorem models_native_iff (H : Set (Sentence p.source.scope)) (M : Model p) :
    (∀ a ∈ H, a.Satisfies M.base) ↔
      (∀ q ∈ p.lowerTheory H,
        Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q) := by
  constructor
  · intro h q ⟨a, ha, hq⟩
    exact (a.lower_satisfies M.base).mp (h a ha) q hq
  · intro h a ha
    exact (a.lower_satisfies M.base).mpr (fun q hq => h q ⟨a, ha, hq⟩)

theorem satisfiable_native_iff (H : Set (Sentence p.source.scope)) :
    (∃ M : Model p, ∀ a ∈ H, a.Satisfies M.base) ↔
      (∃ M : Model p, ∀ q ∈ p.lowerTheory H,
        Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q) :=
  exists_congr (p.models_native_iff H)

theorem unsatisfiable_native_iff (H : Set (Sentence p.source.scope)) :
    (¬ ∃ M : Model p, ∀ a ∈ H, a.Satisfies M.base) ↔
      (¬ ∃ M : Model p, ∀ q ∈ p.lowerTheory H,
        Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q) :=
  not_congr (p.satisfiable_native_iff H)

theorem consequence_native_iff (H : Set (Sentence p.source.scope))
    (a : Sentence p.source.scope) :
    (∀ M : Model p, (∀ b ∈ H, b.Satisfies M.base) → a.Satisfies M.base) ↔
      (∀ M : Model p, (∀ q ∈ p.lowerTheory H,
        Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q) →
          ∀ q ∈ a.lower, Matching.GeneralFixedPoint.Sentence.Satisfies (expand M.base) q) := by
  simp_rw [← Sentence.lower_satisfies, ← p.models_native_iff H]

end Package
end Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
