module

public import Silmaril.Logic.Egglog.Core.Egg.Defs
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Egg
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem guards_holds {S : EQ.Signature} {n : Nat} {Γ : Fin n → S.S}
    (M : Core.Model (signature S)) (ρ : ∀ i, M.carrier (Γ i))
    (guards : List (Silmaril.Logic.Egg.Core.Equality S Γ)) :
    (∀ a ∈ guards.map atom, a.Holds M ρ) ↔
      ∀ e ∈ guards, e.Holds ((models S).obj M) ρ := by
  constructor
  · intro h e he
    exact h (atom e) (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro h a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact h e he

theorem sentence_holds {S : EQ.Signature} (M : Core.Model (signature S))
    (r : Silmaril.Logic.Egg.Core.Rule S) :
    (sentence r).Holds M ↔ r.Holds ((models S).obj M) := by
  apply forall_congr'
  intro ρ
  exact imp_congr (guards_holds M ρ r.guards) Iff.rfl

theorem sentence_map {S T : EQ.Signature} (f : S ⟶ T)
    (r : Silmaril.Logic.Egg.Core.Rule S) :
    sentence (r.map f) = (sentence r).map (signatures.map f) := by
  simp only [sentence, Silmaril.Logic.Egg.Core.Rule.map, Core.Sentence.map,
    Core.Rule.map, List.map_map]
  rfl

/-- The signature square commutes as actual model functors, including all arrows. -/
theorem models_natural {S T : EQ.Signature} (f : S ⟶ T) :
    Core.Model.reduct (signatures.map f) ⋙ models S = models T ⋙ EQ.Algebra.reduct f := rfl

/-- A genuine varying-signature conditional-equation translation into egglog. -/
def fromEgg : Inst.CoHom Silmaril.Logic.Egg.Core.inst Core.inst where
  Φ := signatures
  ρ :=
    { app := fun S => ⟨sentence, models S, sentence_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (sentence_map f)) (models_natural f) }

@[simp] theorem decode_expansion {S : EQ.Signature} (M : EQ.Algebra S) :
    (models S).obj (expansion M) = M := rfl

/-- Every source algebra has an actual table-free expansion. -/
theorem fromEgg_modelExpansive : fromEgg.ModelExpansive :=
  fun _ M => ⟨expansion M, decode_expansion M⟩

@[simp] theorem models_liftHom {S : EQ.Signature} {M N : Core.Model (signature S)}
    (h : (models S).obj M ⟶ (models S).obj N) : (models S).map (liftHom h) = h := by
  cases h
  rfl

instance models_full (S : EQ.Signature) : (models S).Full where
  map_surjective h := ⟨liftHom h, models_liftHom h⟩

instance models_faithful (S : EQ.Signature) : (models S).Faithful where
  map_injective h := Core.Model.Hom.ext _ _ (congrArg EQ.Algebra.Hom.map h)

theorem entails_iff (S : EQ.Signature) (H : Set (Silmaril.Logic.Egg.Core.Rule S))
    (r : Silmaril.Logic.Egg.Core.Rule S) :
    (Silmaril.Logic.Egg.Core.room S).Entails H r ↔
      (Core.room (signature S)).Entails (sentence '' H) (sentence r) :=
  fromEgg.entails_iff fromEgg_modelExpansive S H r

theorem theory_holds_iff {S : EQ.Signature} (M : Core.Model (signature S))
    (H : Set (Silmaril.Logic.Egg.Core.Rule S)) :
    (∀ r ∈ H, r.Holds ((models S).obj M)) ↔ ∀ s ∈ sentence '' H, s.Holds M := by
  constructor
  · rintro h s ⟨r, hr, rfl⟩
    exact (sentence_holds M r).mpr (h r hr)
  · intro h r hr
    exact (sentence_holds M r).mp (h _ ⟨r, hr, rfl⟩)

theorem satisfiable_iff {S : EQ.Signature} (H : Set (Silmaril.Logic.Egg.Core.Rule S)) :
    (∃ M : EQ.Algebra S, ∀ r ∈ H, r.Holds M) ↔
      ∃ N : Core.Model (signature S), ∀ s ∈ sentence '' H, s.Holds N := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨expansion M, (theory_holds_iff (expansion M) H).mp hM⟩
  · rintro ⟨N, hN⟩
    exact ⟨(models S).obj N, (theory_holds_iff N H).mpr hN⟩

theorem unsatisfiable_iff {S : EQ.Signature} (H : Set (Silmaril.Logic.Egg.Core.Rule S)) :
    (¬ ∃ M : EQ.Algebra S, ∀ r ∈ H, r.Holds M) ↔
      ¬ ∃ N : Core.Model (signature S), ∀ s ∈ sentence '' H, s.Holds N :=
  not_congr (satisfiable_iff H)

end Silmaril.Logic.Egglog.Core.Egg
