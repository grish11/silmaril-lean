module

public import Silmaril.Proofs.Logic.Kore.Modules.Semantics.Adequacy

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules.Semantics
open Silmaril.Logic.Kore Silmaril.Logic.Kore.Modules
open Silmaril.Logic.Kore.Modules.Semantics
variable {scope : Scope} (M : Silmaril.Logic.Matching.FirstOrder.Model scope.signature)

/-- Actual source-sentence validity agrees with typed universal closure after
successful source context construction and intrinsic elaboration. -/
theorem sentence_sound (fuel : Nat) (raw : RawPattern)
    (typed : FirstOrder.Sentence scope.signature)
    (accepted : Checking.sentence scope fuel raw = some typed) :
    Satisfies M fuel raw ↔ FirstOrder.Sentence.Satisfies M typed := by
  unfold Checking.sentence at accepted
  obtain ⟨names, contextRead, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · obtain ⟨s, sortRead, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨body, bodyRead, result⟩ := Option.bind_eq_some_iff.mp accepted
    have eq := Option.some.inj result
    subst typed
    have bodyMeaning (v : Valuation M names.eraseDups) :
        denote M fuel (initial M names.eraseDups v) s raw =
          FirstOrder.denote scope.signature M v body := by
      simpa only [interpret, List.map_map, Function.comp_def, FirstOrder.denote, initial]
        using elaborate_sound M fuel _ v s raw body bodyRead
    constructor
    · rintro ⟨sourceVariables, sourceSort, hv, hs, sourceValid⟩
      rw [contextRead] at hv
      cases Option.some.inj hv
      rw [sortRead] at hs
      cases Option.some.inj hs
      intro v result
      rw [← bodyMeaning v]
      exact sourceValid v result
    · intro typedValid
      refine ⟨names, s, contextRead, sortRead, ?_⟩
      intro v result
      rw [bodyMeaning v]
      exact typedValid v result
end Silmaril.Proofs.Logic.Kore.Modules.Semantics
