module

public import Silmaril.Machine.MulticoreVM.Institution.Schedulers.Defs
public import Silmaril.Machine.MulticoreVM.Institution.Projection.Thms
public import Silmaril.Machine.MulticoreVM.CriticalRegion.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers.Laws

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers
  (mapNamed_id mapNamed_comp mapScheduled_id mapScheduled_comp)

universe u

variable {A B : Sig.{u}} {State Instruction Abstract : Type u}

/-- The schedule and the counted effect word are two profiles of the existing
institution, usable with `classic scheduledWords` and `classic countedWords`. -/
def scheduledWords : Sig.{u} ⥤ Type u where
  obj := Sig.ScheduledWord
  map f := TypeCat.ofHom f.mapScheduled
  map_id _ := by exact TypeCat.homEquiv.injective (funext mapScheduled_id)
  map_comp f g := by exact TypeCat.homEquiv.injective (funext (mapScheduled_comp f g))

def countedWords : Sig.{u} ⥤ Type u where
  obj := Sig.CountedWord
  map f := TypeCat.ofHom f.mapCounted
  map_id _ := by exact TypeCat.homEquiv.injective (funext fun w => Prod.ext rfl (mapNamed_id w.2))
  map_comp f g := by
    exact TypeCat.homEquiv.injective (funext fun w => Prod.ext rfl (mapNamed_comp f g w.2))

/-- Erasure commutes with thread and event renaming. -/
def scheduledToCounted : scheduledWords.{u} ⟶ countedWords.{u} where
  app _ := TypeCat.ofHom eraseAdministration
  naturality {_ _} f := by
    exact TypeCat.homEquiv.injective
      (funext (Proofs.Machine.MulticoreVM.Institution.Schedulers.eraseAdministration_commutes f))

def countedToNamed : countedWords.{u} ⟶ namedWords.{u} where
  app _ := TypeCat.ofHom Prod.snd
  naturality {_ _} _ := rfl

theorem Scheduler.satisfaction_renaming (f : A ⟶ B) (vm : Scheduler B) (initial : vm.State)
    (sentence : Sentence A.ScheduledWord) :
    (sentence.map f.mapScheduled).Holds (vm.model initial) ↔
      sentence.Holds (reduct f.mapScheduled (vm.model initial)) :=
  satisfaction f.mapScheduled (vm.model initial) sentence

theorem Scheduler.satisfaction_counted_renaming (f : A ⟶ B) (vm : Scheduler B)
    (initial : vm.State) (sentence : Sentence A.CountedWord) :
    (sentence.map f.mapCounted).Holds (vm.countedModel initial) ↔
      sentence.Holds (reduct f.mapCounted (vm.countedModel initial)) :=
  satisfaction f.mapCounted (vm.countedModel initial) sentence

/-- Translating a schedule sentence along erasure evaluates it on the counted
behavior, or equivalently on its inverse-image reduct to candidate schedules. -/
theorem Scheduler.satisfaction_erasure (vm : Scheduler A) (initial : vm.State)
    (sentence : Sentence A.ScheduledWord) :
    (sentence.map (eraseAdministration (A := A))).Holds (vm.countedModel initial) ↔
      sentence.Holds (reduct (eraseAdministration (A := A)) (vm.countedModel initial)) :=
  satisfaction eraseAdministration (vm.countedModel initial) sentence

/-- Direct-image erasure and renaming commute on the source behavior itself. -/
theorem Scheduler.countedImage_natural (f : A ⟶ B) (vm : Scheduler A) (initial : vm.State) :
    eraseAdministration '' (f.mapScheduled '' vm.model initial) =
      f.mapCounted '' vm.countedModel initial :=
  image_natural scheduledToCounted f (vm.model initial)

/-- Every source schedule maps to a target execution with the mapped endpoints
and the renamed chronological effects. -/
theorem StepMap.scheduled (f : A ⟶ B) {S T I J : Type u}
    {source : Transition S A.ThreadId I A.Event} {target : Transition T B.ThreadId J B.Event}
    (m : StepMap f source target) {moves : Schedule A.ThreadId I} {initial final : S}
    {word : A.NamedWord} (path : Scheduled source moves initial word final) :
    Scheduled target (f.mapSchedule m.instruction moves) (m.state initial) (f.mapNamed word)
      (m.state final) :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.map_scheduled f m path

/-- A forward map supplies actual executions in the target interpretation. -/
theorem Scheduler.Forward.model_image_subset {f : A ⟶ B} {source : Scheduler A} {target : Scheduler B}
    (m : Scheduler.Forward f source target) (initial : source.State) :
    f.mapScheduled '' source.model initial ⊆ target.model (m.state initial) :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.model_image_subset f m initial

theorem Scheduler.Forward.countedModel_image_subset {f : A ⟶ B}
    {source : Scheduler A} {target : Scheduler B}
    (m : Scheduler.Forward f source target) (initial : source.State) :
    f.mapCounted '' source.countedModel initial ⊆ target.countedModel (m.state initial) := by
  rw [← source.countedImage_natural f initial]
  exact Set.image_mono (m.model_image_subset initial)

def StepMap.schedulerForward {f : A ⟶ B} {S T I J : Type u}
    {source : Transition S A.ThreadId I A.Event} {target : Transition T B.ThreadId J B.Event}
    (m : StepMap f source target) : Scheduler.Forward f (Scheduler.atomic source) (Scheduler.atomic target) where
  toStepMap := m
  classify _ := rfl

def CriticalMap.schedulerForward {S T I J : Type u} {f : A ⟶ B}
    {source : CriticalRegion.Program S A.ThreadId I A.Event}
    {target : CriticalRegion.Program T B.ThreadId J B.Event} (m : CriticalMap f source target) :
    Scheduler.Forward f (Scheduler.critical source) (Scheduler.critical target) where
  state := m.config
  instruction := m.action
  step := by exact Proofs.Machine.MulticoreVM.Institution.Schedulers.critical_step m
  classify choice := by cases choice <;> rfl

def CooperativeMap.schedulerForward {S T I J : Type u} {f : A ⟶ B}
    {source : Cooperative.Program S A.ThreadId I A.Event}
    {target : Cooperative.Program T B.ThreadId J B.Event}
    {policy : Cooperative.DispatchPolicy S A.ThreadId} {policy' : Cooperative.DispatchPolicy T B.ThreadId}
    (m : CooperativeMap f source target policy policy') :
    Scheduler.Forward f (Scheduler.cooperative source policy) (Scheduler.cooperative target policy') where
  state := m.config
  instruction := m.action
  step := by exact Proofs.Machine.MulticoreVM.Institution.Schedulers.cooperative_step m
  classify choice := by cases choice <;> rfl

/-- Transport and refinement erase the same critical scheduler decisions in either order. -/
theorem CriticalMap.atomicSchedule_map {S T I J : Type u} {f : A ⟶ B}
    {source : CriticalRegion.Program S A.ThreadId I A.Event}
    {target : CriticalRegion.Program T B.ThreadId J B.Event} (m : CriticalMap f source target)
    (moves : Schedule A.ThreadId (CriticalRegion.Action I)) :
    CriticalRegion.atomicSchedule (f.mapSchedule m.action moves) =
      f.mapSchedule m.instruction (CriticalRegion.atomicSchedule moves) :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.critical_erase_map m moves

/-- Transport and refinement erase the same yield dispatcher decisions in either order. -/
theorem CooperativeMap.atomicSchedule_map {S T I J : Type u} {f : A ⟶ B}
    {source : Cooperative.Program S A.ThreadId I A.Event}
    {target : Cooperative.Program T B.ThreadId J B.Event}
    {policy : Cooperative.DispatchPolicy S A.ThreadId} {policy' : Cooperative.DispatchPolicy T B.ThreadId}
    (m : CooperativeMap f source target policy policy')
    (moves : Schedule A.ThreadId (Cooperative.Action I)) :
    Cooperative.atomicSchedule (f.mapSchedule m.action moves) =
      f.mapSchedule m.instruction (Cooperative.atomicSchedule moves) :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.cooperative_erase_map m moves

/-- Ignoring decisions gives the same named model as the original VM adapter. -/
theorem Scheduler.namedModel_eq (vm : Scheduler A) (initial : vm.State) :
    Prod.snd '' vm.model initial = namedModel vm.step initial :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.namedModel_eq vm initial

theorem Scheduler.mem_atomic_counted (step : Transition State A.ThreadId Instruction A.Event)
    (initial : State) (n : Nat) (word : A.NamedWord) :
    (n, word) ∈ (Scheduler.atomic step).countedModel initial ↔
      ∃ final, (final, word) ∈ namedOutcomes (run step n) initial :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.mem_atomic_counted step initial n word

theorem Scheduler.mem_critical_counted (program : CriticalRegion.Program State A.ThreadId Instruction A.Event)
    (view : State → Abstract) (initial : CriticalRegion.Config State A.ThreadId)
    (n : Nat) (word : A.NamedWord) :
    (n, word) ∈ (Scheduler.critical program).countedModel initial ↔
      ∃ final, (final, word) ∈ CriticalRegion.observedOutcomes program view initial n :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.mem_critical_counted program view initial n word

theorem Scheduler.mem_cooperative_counted (program : Cooperative.Program State A.ThreadId Instruction A.Event)
    (policy : Cooperative.DispatchPolicy State A.ThreadId) (view : State → Abstract)
    (initial : Cooperative.Config State A.ThreadId) (n : Nat) (word : A.NamedWord) :
    (n, word) ∈ (Scheduler.cooperative program policy).countedModel initial ↔
      ∃ final, (final, word) ∈ Cooperative.observedOutcomes program policy view initial n :=
  Proofs.Machine.MulticoreVM.Institution.Schedulers.mem_cooperative_counted program policy view initial n word

theorem Scheduler.critical_counted_subset {program : CriticalRegion.Program State A.ThreadId Instruction A.Event}
    {view : State → Abstract} {step : Transition Abstract A.ThreadId Instruction A.Event}
    (refines : program.Refines view step) (initial : CriticalRegion.Config State A.ThreadId) :
    (Scheduler.critical program).countedModel initial ⊆ (Scheduler.atomic step).countedModel (view initial.vm) := by
  rintro ⟨n, word⟩ h
  obtain ⟨final, run⟩ := (Scheduler.mem_critical_counted program view initial n word).1 h
  exact (Scheduler.mem_atomic_counted step _ _ _).2
    ⟨final, CriticalRegion.observedOutcomes_subset refines initial n run⟩

theorem Scheduler.cooperative_counted_subset
    {program : Cooperative.Program State A.ThreadId Instruction A.Event}
    {view : State → Abstract} {step : Transition Abstract A.ThreadId Instruction A.Event}
    (refines : program.Refines view step) (policy : Cooperative.DispatchPolicy State A.ThreadId)
    (initial : Cooperative.Config State A.ThreadId) :
    (Scheduler.cooperative program policy).countedModel initial ⊆
      (Scheduler.atomic step).countedModel (view initial.vm) := by
  rintro ⟨n, word⟩ h
  obtain ⟨_, moves, final, count, path, _⟩ :=
    (Scheduler.mem_cooperative_counted program policy view initial n word).1 h
  exact (Scheduler.mem_atomic_counted step _ _ _).2 ⟨view final.vm,
    (mem_run_iff_exists_schedule n).2
      ⟨Cooperative.atomicSchedule moves, count, Cooperative.scheduled_refines refines path⟩⟩

theorem Scheduler.countedModel_regionFree (step : Transition State A.ThreadId Instruction A.Event)
    (initial : State) :
    (Scheduler.critical (CriticalRegion.regionFree step)).countedModel (CriticalRegion.Config.start initial) =
      (Scheduler.atomic step).countedModel initial := by
  ext ⟨n, word⟩
  rw [Scheduler.mem_critical_counted _ id, Scheduler.mem_atomic_counted,
    CriticalRegion.observedOutcomes_regionFree]

theorem Scheduler.countedModel_everyAtomic (step : Transition State A.ThreadId Instruction A.Event)
    (initial : State) :
    (Scheduler.cooperative (Cooperative.everyAtomic step) Cooperative.anyDispatch).countedModel
      (Cooperative.Config.start (initial, false)) =
      (Scheduler.atomic step).countedModel initial := by
  ext ⟨n, word⟩
  rw [Scheduler.mem_cooperative_counted _ _ Prod.fst, Scheduler.mem_atomic_counted,
    Cooperative.observedOutcomes_everyAtomic]

end Silmaril.Machine.MulticoreVM.Institution
