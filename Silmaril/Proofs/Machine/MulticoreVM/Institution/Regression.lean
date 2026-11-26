module

import Silmaril.Machine.MulticoreVM.Institution.Thms
import Silmaril.Machine.MulticoreVM.Toy.Thms
import Silmaril.Semantics.ConcurrentTrace.Thms

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution
open Silmaril.Semantics.ConcurrentTrace (ofWord mapTrace_ofWord)

private abbrev source : Sig := ⟨Fin 2, Bool, Bool⟩
private abbrev target : Sig := ⟨Nat, Nat, Option Bool⟩

private def rename : source ⟶ target where
  thread := ⟨Fin.val, fun _ _ h => Fin.eq_of_val_eq h⟩
  core := fun c => if c then 5 else 3
  event := some

private def sourceWord : source.NamedWord := [.event 1 true, .sync [1, 0]]
private def targetWord : target.NamedWord := [.event 1 (some true), .sync [1, 0]]

-- The cross-type renaming takes both the event owner and the synchronization participants.
example : Sig.Hom.mapNamed rename sourceWord = targetWord := rfl

example : Sig.Hom.mapConcurrent rename (ofWord sourceWord) = ofWord targetWord :=
  mapTrace_ofWord rename.thread rename.thread.injective rename.event sourceWord

private def coreWord : source.CoreWord := [(true, .event 1 true), (false, .sync [1, 0])]
private def otherCoreWord : source.CoreWord := [(false, .event 1 true), (false, .sync [1, 0])]
private def targetCoreWord : target.CoreWord :=
  [(5, .event 1 (some true)), (3, .sync [1, 0])]

example : Sig.Hom.mapCore rename coreWord = targetCoreWord := rfl

private abbrev targetModel : Model target.CoreWord := {targetCoreWord}

-- Require the event on the first core and forbid the same word with its event on the other core.
example : (Sentence.conj (.possible coreWord) (.neg (.possible otherCoreWord))).Holds
    (reduct (Sig.Hom.mapCore rename) targetModel) := by
  have sat := (classic coreWords).satisfaction rename targetModel
    (Sentence.conj (.possible coreWord) (.neg (.possible otherCoreWord)))
  apply sat.mp
  refine ⟨rfl, ?_⟩
  intro h
  change Sig.Hom.mapCore rename otherCoreWord ∈ targetModel at h
  have heq := Set.mem_singleton_iff.mp h
  have hcores := congrArg (List.map Prod.fst) heq
  change [3, 3] = [5, 3] at hcores
  exact (by decide : [3, 3] ≠ [5, 3]) hcores

private abbrev toySig : Sig := ⟨Toy.ThreadId, Unit, Nat⟩
private def initial : Toy.Config := Toy.init 0 ⟨7, [.emit]⟩

-- The initial state contributes the empty word. A successful scheduled emit contributes [7].
example : (Sentence.conj (.possible ([] : toySig.NamedWord)) (.possible [.event 0 7])).Holds
    (namedModel (A := toySig) Toy.step initial) := by
  refine ⟨⟨[], [], initial, .nil initial, rfl⟩, ?_⟩
  refine ⟨[⟨0, none⟩], [.event 0 7], Toy.put initial 0 ⟨7, []⟩, ?_, rfl⟩
  exact (execute_iff_scheduled Toy.exec _).mp rfl

example : (ofWord ([.event 0 7] : toySig.NamedWord)) ∈
    concurrentModel (A := toySig) Toy.step initial :=
  ⟨[⟨0, none⟩], [.event 0 7], Toy.put initial 0 ⟨7, []⟩,
    (execute_iff_scheduled Toy.exec _).mp rfl, rfl⟩

end Silmaril.Proofs.Machine.MulticoreVM.Institution
