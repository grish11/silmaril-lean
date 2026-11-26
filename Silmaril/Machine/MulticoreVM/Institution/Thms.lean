module

public import Silmaril.Machine.MulticoreVM.Institution.Defs
import Silmaril.Proofs.Machine.MulticoreVM.Institution.Laws

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {O P Q : Type u}

/-- Translating along the identity leaves the sentence unchanged. -/
@[simp] theorem sentenceMap_id (φ : Sentence O) : φ.map id = φ :=
  Proofs.Machine.MulticoreVM.Institution.sentenceMap_id φ

/-- Translation respects composition of observation maps. -/
theorem sentenceMap_comp (f : O → P) (g : P → Q) (φ : Sentence O) :
    φ.map (g ∘ f) = (φ.map f).map g :=
  Proofs.Machine.MulticoreVM.Institution.sentenceMap_comp f g φ

/-- Truth is invariant under translation and behavioral reduct, including negative tests. -/
theorem satisfaction (f : O → P) (M : Model P) (φ : Sentence O) :
    (φ.map f).Holds M ↔ φ.Holds (reduct f M) :=
  Proofs.Machine.MulticoreVM.Institution.satisfaction f M φ

/-- Sentence translation and behavioral reduct form a corridor for any observation map. -/
def room (O : Type u) : Room.{u, u, u} :=
  ⟨Sentence O, Cat.of (Model O), Sentence.Holds⟩

/-- The reduct preserves the inclusion arrows between behavior sets. -/
def corridor (f : O → P) : room O ⟶ room P :=
  ⟨Sentence.map f, (Monotone.functor (f := reduct f) (fun _ _ h => Set.preimage_mono h) :
    Model P ⥤ Model O), satisfaction f⟩

/-- The institution of propositional observation tests over types and functions. -/
def observationInstitution : Type u ⥤ Room.{u, u, u} where
  obj := room
  map f := corridor f
  map_id _ := Room.hom_ext (funext sentenceMap_id) rfl
  map_comp f g := Room.hom_ext (funext (sentenceMap_comp f g)) rfl

open Proofs.Machine.MulticoreVM.Institution (mapNamed_id mapNamed_comp mapConcurrent_id
  mapConcurrent_comp mapCore_id mapCore_comp)

/-- Thread-named chronological observations. -/
def namedWords : Sig.{u} ⥤ Type u where
  obj := Sig.NamedWord
  map f := TypeCat.ofHom (Sig.Hom.mapNamed f)
  map_id _ := by
    exact TypeCat.homEquiv.injective (funext mapNamed_id)
  map_comp f g := by
    exact TypeCat.homEquiv.injective (funext (mapNamed_comp f g))

/-- Thread-named observations modulo independent swaps. -/
def concurrentTraces : Sig.{u} ⥤ Type u where
  obj := Sig.ConcurrentTrace
  map f := TypeCat.ofHom (Sig.Hom.mapConcurrent f)
  map_id _ := by
    exact TypeCat.homEquiv.injective (funext mapConcurrent_id)
  map_comp f g := by
    exact TypeCat.homEquiv.injective (funext (mapConcurrent_comp f g))

/-- Chronological observations with explicit core tags. -/
def coreWords : Sig.{u} ⥤ Type u where
  obj := Sig.CoreWord
  map f := TypeCat.ofHom (Sig.Hom.mapCore f)
  map_id _ := by
    exact TypeCat.homEquiv.injective (funext mapCore_id)
  map_comp f g := by
    exact TypeCat.homEquiv.injective (funext (mapCore_comp f g))

/-- The Goguen–Burstall institution for a functor of observations, for example
`namedWords`, `concurrentTraces`, or `coreWords`. -/
def classic (observations : Sig.{u} ⥤ Type u) :
    ClassicInstitution.{u + 1, u, u, u, u} Sig.{u} :=
  ClassicInstitution.ofRoomFunctor (observations ⋙ observationInstitution)

/-- The VM interpretation also observes exactly the outcomes of the monadic finite runner. -/
theorem mem_ofVM_iff_run {State Thread Choice Event : Type u}
    (observe : Word Thread Event → O) (step : Transition State Thread Choice Event)
    (initial : State) (obs : O) :
    obs ∈ ofVM observe step initial ↔
      ∃ n word final, (final, word) ∈ namedOutcomes (run step n) initial ∧ observe word = obs :=
  Proofs.Machine.MulticoreVM.Institution.mem_ofVM_iff_run observe step initial obs

end Silmaril.Machine.MulticoreVM.Institution
