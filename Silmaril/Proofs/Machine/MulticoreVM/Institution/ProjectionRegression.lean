module

import Silmaril.Machine.MulticoreVM.Institution.Placed.Thms
import Silmaril.Machine.MulticoreVM.Toy.Thms

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution

private abbrev source : Sig := ⟨Fin 2, Bool, Bool⟩
private abbrev target : Sig := ⟨Nat, Nat, Option Bool⟩

private def rename : source ⟶ target where
  thread := ⟨Fin.val, fun _ _ h => Fin.eq_of_val_eq h⟩
  core := fun _ => 0
  event := some

private def sourceWord : source.PlacedWord := [.sync true 1 [1, 0], .event false 0 true]
private def renamedWord : target.PlacedWord := [.sync 0 1 [1, 0], .event 0 0 (some true)]

example : Sig.Hom.mapPlaced rename sourceWord = renamedWord := rfl

-- Both source cores map to 0. The core projection retains payloads and opaque syncs in order.
example : placedToCore.app target (Sig.Hom.mapPlaced rename sourceWord) =
    [.event 0 none, .event 0 (some (some true))] := rfl

example {Core Thread Choice : Type}
    (instruction : Placed.Instruction source.CoreId source.ThreadId Core Thread Choice source.Event)
    (initial : Placed.Config source.CoreId source.ThreadId Core Thread) :
    let M := ofPlaced (A := source) instruction initial
    (placedToCore.app target) '' (Sig.Hom.mapPlaced rename '' M) =
      (Sig.Hom.mapCoreLocal rename) '' ((placedToCore.app source) '' M) :=
  image_natural placedToCore rename (ofPlaced instruction initial)

example (M : Model target.NamedWord) :
    reduct (Sig.Hom.mapPlaced rename) (reduct (placedToNamed.app target) M) =
      reduct (placedToNamed.app source) (reduct (Sig.Hom.mapNamed rename) M) :=
  reduct_natural placedToNamed rename M

example (φ : Sentence source.PlacedWord) :
    ((φ.map (Sig.Hom.mapPlaced rename)).map (placedToNamed.app target)) =
      ((φ.map (placedToNamed.app source)).map (Sig.Hom.mapNamed rename)) :=
  sentence_natural placedToNamed rename φ

private def threadWord : source.NamedWord := [.event 0 true]
private def unreachableTag : target.PlacedWord := [.event 1 0 (some true)]
private abbrev singletonBehavior : Model target.PlacedWord := {unreachableTag}

-- The mixed square can be strict. The visible word has a target witness on core 1,
-- while all source cores rename to 0.
example :
    threadWord ∈ reduct (Sig.Hom.mapNamed rename) ((placedToNamed.app target) '' singletonBehavior)
      ∧ threadWord ∉ (placedToNamed.app source) '' reduct (Sig.Hom.mapPlaced rename) singletonBehavior := by
  refine ⟨⟨unreachableTag, rfl, rfl⟩, ?_⟩
  rintro ⟨word, hword, _⟩
  change Sig.Hom.mapPlaced rename word ∈ singletonBehavior at hword
  have heq := Set.mem_singleton_iff.mp hword
  cases word with
  | nil => cases heq
  | cons letter rest => cases letter <;> cases heq

private abbrev toySig : Sig := ⟨Toy.ThreadId, Unit, Nat⟩

example (initial : Toy.Config) :
    (namedToConcurrent.app toySig) '' namedModel (A := toySig) Toy.step initial =
      concurrentModel (A := toySig) Toy.step initial :=
  image_ofVM (namedToConcurrent.app toySig) id Toy.step initial

end Silmaril.Proofs.Machine.MulticoreVM.Institution
