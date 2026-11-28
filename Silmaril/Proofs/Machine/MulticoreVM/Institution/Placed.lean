module

public import Silmaril.Machine.MulticoreVM.Institution.Placed.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution
open Silmaril.Semantics.ConcurrentTrace (Letter mapWord)

universe u

variable {A B C : Sig.{u}}

theorem mapPlaced_id (word : A.PlacedWord) : Sig.Hom.mapPlaced (𝟙 A) word = word := by
  unfold Sig.Hom.mapPlaced
  refine (List.map_congr_left (g := id) ?_).trans (List.map_id word)
  intro letter _
  cases letter with
  | event => rfl
  | sync core thread participants =>
    exact congrArg (Placed.TaggedLetter.sync core thread) (List.map_id participants)

theorem mapPlaced_comp (f : A ⟶ B) (g : B ⟶ C) (word : A.PlacedWord) :
    Sig.Hom.mapPlaced (f ≫ g) word = Sig.Hom.mapPlaced g (Sig.Hom.mapPlaced f word) := by
  unfold Sig.Hom.mapPlaced
  rw [List.map_map]
  refine List.map_congr_left fun letter _ => ?_
  cases letter with
  | event => rfl
  | sync core thread _ =>
    exact congrArg (Placed.TaggedLetter.sync (g.core (f.core core)) (g.thread (f.thread thread)))
      (List.map_map (f := f.thread) (g := g.thread)).symm

theorem mapCoreLocal_id (word : A.CoreLocalWord) :
    Sig.Hom.mapCoreLocal (𝟙 A) word = word := by
  unfold Sig.Hom.mapCoreLocal mapWord
  refine (List.map_congr_left (g := id) ?_).trans (List.map_id word)
  intro letter _
  cases letter with
  | event core value => cases value <;> rfl
  | sync participants => exact congrArg Letter.sync (List.map_id participants)

theorem mapCoreLocal_comp (f : A ⟶ B) (g : B ⟶ C) (word : A.CoreLocalWord) :
    Sig.Hom.mapCoreLocal (f ≫ g) word = Sig.Hom.mapCoreLocal g (Sig.Hom.mapCoreLocal f word) := by
  unfold Sig.Hom.mapCoreLocal mapWord
  rw [List.map_map]
  refine List.map_congr_left fun letter _ => ?_
  cases letter with
  | event core value => cases value <;> rfl
  | sync => exact congrArg Letter.sync (List.map_map (f := f.core) (g := g.core)).symm

theorem placedToNamed_natural (f : A ⟶ B) (word : A.PlacedWord) :
    Placed.threadWord (Sig.Hom.mapPlaced f word) =
      Sig.Hom.mapNamed f (Placed.threadWord word) := by
  unfold Placed.threadWord Sig.Hom.mapPlaced Sig.Hom.mapNamed mapWord
  simp only [List.map_map]
  exact List.map_congr_left fun letter _ => by cases letter <;> rfl

theorem placedToCore_natural (f : A ⟶ B) (word : A.PlacedWord) :
    Placed.coreWord (Sig.Hom.mapPlaced f word) =
      Sig.Hom.mapCoreLocal f (Placed.coreWord word) := by
  unfold Placed.coreWord Sig.Hom.mapPlaced Sig.Hom.mapCoreLocal mapWord
  simp only [List.map_map]
  exact List.map_congr_left fun letter _ => by cases letter <;> rfl

theorem placed_named_subset {Core Thread Choice : Type u} [DecidableEq A.CoreId]
    {instruction : Placed.Instruction A.CoreId A.ThreadId Core Thread Choice A.Event}
    {step : Transition (A.ThreadId → Option Thread) A.ThreadId Choice A.Event}
    (refines : instruction.Refines step)
    (initial : Placed.Config A.CoreId A.ThreadId Core Thread) :
    Placed.threadWord '' ofPlaced (A := A) instruction initial ⊆
      namedModel (A := A) step initial.threads := by
  rintro _ ⟨_, ⟨schedule, final, execution⟩, rfl⟩
  exact ⟨Placed.threadSchedule schedule, _, final.threads, execution.refines refines, rfl⟩

end Silmaril.Proofs.Machine.MulticoreVM.Institution
