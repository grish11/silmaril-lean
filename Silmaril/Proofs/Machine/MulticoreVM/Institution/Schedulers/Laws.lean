module

public import Silmaril.Machine.MulticoreVM.Institution.Schedulers.Defs
public import Silmaril.Machine.MulticoreVM.Institution.Projection.Thms
public import Silmaril.Machine.MulticoreVM.CriticalRegion.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution
open Silmaril.Semantics.ConcurrentTrace (Word mapWord)

universe u

variable {A B C : Sig.{u}} {State Instruction Abstract : Type u}

theorem mapNamed_id (w : A.NamedWord) : Sig.Hom.mapNamed (𝟙 A) w = w := by
  exact congrFun (congrArg (fun f : A.NamedWord ⟶ A.NamedWord => TypeCat.homEquiv f)
    (namedWords.map_id A)) w

theorem mapNamed_comp (f : A ⟶ B) (g : B ⟶ C) (w : A.NamedWord) :
    (f ≫ g).mapNamed w = g.mapNamed (f.mapNamed w) := by
  exact congrFun (congrArg (fun h : A.NamedWord ⟶ C.NamedWord => TypeCat.homEquiv h)
    (namedWords.map_comp f g)) w

theorem mapScheduled_id (w : A.ScheduledWord) : Sig.Hom.mapScheduled (𝟙 A) w = w := by
  refine Prod.ext ?_ (mapNamed_id w.2)
  change (w.1.map fun (t, move) => (t, move)) = w.1
  simp

theorem mapScheduled_comp (f : A ⟶ B) (g : B ⟶ C) (w : A.ScheduledWord) :
    (f ≫ g).mapScheduled w = g.mapScheduled (f.mapScheduled w) := by
  refine Prod.ext ?_ (mapNamed_comp f g w.2)
  simp [Sig.Hom.mapScheduled, List.map_map, Function.comp_def]
  intros
  rfl

theorem eraseAdministration_commutes (f : A ⟶ B) (w : A.ScheduledWord) :
    eraseAdministration (f.mapScheduled w) = f.mapCounted (eraseAdministration w) := by
  apply Prod.ext
  · simp [eraseAdministration, Sig.Hom.mapScheduled, Sig.Hom.mapCounted,
      List.countP_map, Function.comp_def]
  · rfl

theorem mapNamed_nameFragment (f : A ⟶ B) (thread : A.ThreadId)
    (fragment : Fragment A.ThreadId A.Event) :
    f.mapNamed (nameFragment thread fragment) = nameFragment (f.thread thread) (f.mapFragment fragment) := by
  simp only [Sig.Hom.mapNamed, nameFragment, Sig.Hom.mapFragment, mapWord, List.map_map]
  congr 1
  funext letter
  cases letter <;> rfl

theorem map_scheduled (f : A ⟶ B) {S T I J : Type u}
    {source : Transition S A.ThreadId I A.Event} {target : Transition T B.ThreadId J B.Event}
    (m : StepMap f source target) {moves : Schedule A.ThreadId I} {initial final : S}
    {word : A.NamedWord} (path : Scheduled source moves initial word final) :
    Scheduled target (f.mapSchedule m.instruction moves) (m.state initial) (f.mapNamed word)
      (m.state final) := by
  induction path with
  | nil => exact .nil _
  | @cons decision schedule initial next final fragment tail first _ ih =>
    have append : f.mapNamed (nameFragment decision.thread fragment ++ tail) =
        nameFragment (f.thread decision.thread) (f.mapFragment fragment) ++ f.mapNamed tail :=
      (List.map_append ..).trans (congrArg (· ++ f.mapNamed tail) (mapNamed_nameFragment f _ _))
    rw [append]
    exact .cons (m.step first) ih

theorem log_map (f : A ⟶ B) {source : Scheduler A} {target : Scheduler B}
    (m : Scheduler.Forward f source target) (moves : Schedule A.ThreadId source.Instruction) :
    target.log (f.mapSchedule m.instruction moves) =
      (source.log moves).map (fun (t, move) => (f.thread t, move)) := by
  simp [Scheduler.log, Sig.Hom.mapSchedule, List.map_map, Function.comp_def, m.classify]

theorem model_image_subset (f : A ⟶ B) {source : Scheduler A} {target : Scheduler B}
    (m : Scheduler.Forward f source target) (initial : source.State) :
    f.mapScheduled '' source.model initial ⊆ target.model (m.state initial) := by
  rintro _ ⟨_, ⟨moves, word, final, path, rfl⟩, rfl⟩
  exact ⟨f.mapSchedule m.instruction moves, f.mapNamed word, m.state final,
    map_scheduled f m.toStepMap path, congrArg (·, f.mapNamed word) (log_map f m moves)⟩

theorem critical_step {S T I J : Type u} {f : A ⟶ B}
    {source : CriticalRegion.Program S A.ThreadId I A.Event}
    {target : CriticalRegion.Program T B.ThreadId J B.Event} (m : CriticalMap f source target)
    {thread action initial fragment final}
    (run : CriticalRegion.Step source thread action initial fragment final) :
    CriticalRegion.Step target (f.thread thread) (m.action action) (m.config initial)
      (f.mapFragment fragment) (m.config final) := by
  cases run with
  | atomic allowed active first =>
    have mapped := allowed.imp (congrArg (Option.map f.thread)) (congrArg (Option.map f.thread))
    exact .atomic mapped (active ∘ m.finished _ _) (m.step first)
  | enter active enter => exact .enter (active ∘ m.finished _ _) (m.enter enter)
  | leave active leave => exact .leave (active ∘ m.finished _ _) (m.leave leave)

theorem cooperative_step {S T I J : Type u} {f : A ⟶ B}
    {source : Cooperative.Program S A.ThreadId I A.Event}
    {target : Cooperative.Program T B.ThreadId J B.Event}
    {policy : Cooperative.DispatchPolicy S A.ThreadId} {policy' : Cooperative.DispatchPolicy T B.ThreadId}
    (m : CooperativeMap f source target policy policy') {thread action initial fragment final}
    (run : Cooperative.Step source policy thread action initial fragment final) :
    Cooperative.Step target policy' (f.thread thread) (m.action action) (m.config initial)
      (f.mapFragment fragment) (m.config final) := by
  cases run with
  | dispatch allowed ready =>
    refine .dispatch (m.dispatch allowed) ⟨ready.1 ∘ (m.finished _ _).1, ?_⟩
    rcases ready.2 with ⟨i, fragment, next, first⟩ | ⟨next, didYield⟩
    · exact Or.inl ⟨m.instruction i, f.mapFragment fragment, m.state next, m.step first⟩
    · exact Or.inr ⟨m.state next, m.yieldTo didYield⟩
  | atomic active first => exact .atomic (active ∘ (m.finished _ _).1) (m.step first)
  | yield active didYield => exact .yield (active ∘ (m.finished _ _).1) (m.yieldTo didYield)
  | complete finished => exact .complete ((m.finished _ _).2 finished)

theorem critical_erase_map {S T I J : Type u} {f : A ⟶ B}
    {source : CriticalRegion.Program S A.ThreadId I A.Event}
    {target : CriticalRegion.Program T B.ThreadId J B.Event} (m : CriticalMap f source target)
    (moves : Schedule A.ThreadId (CriticalRegion.Action I)) :
    CriticalRegion.atomicSchedule (f.mapSchedule m.action moves) =
      f.mapSchedule m.instruction (CriticalRegion.atomicSchedule moves) := by
  induction moves with
  | nil => rfl
  | cons decision moves ih =>
    obtain ⟨thread, action⟩ := decision
    cases action <;>
      simp only [Sig.Hom.mapSchedule, List.map_cons, CriticalMap.action,
        CriticalRegion.atomicSchedule] at ih ⊢
    all_goals rw [ih]

theorem cooperative_erase_map {S T I J : Type u} {f : A ⟶ B}
    {source : Cooperative.Program S A.ThreadId I A.Event}
    {target : Cooperative.Program T B.ThreadId J B.Event}
    {policy : Cooperative.DispatchPolicy S A.ThreadId} {policy' : Cooperative.DispatchPolicy T B.ThreadId}
    (m : CooperativeMap f source target policy policy')
    (moves : Schedule A.ThreadId (Cooperative.Action I)) :
    Cooperative.atomicSchedule (f.mapSchedule m.action moves) =
      f.mapSchedule m.instruction (Cooperative.atomicSchedule moves) := by
  induction moves with
  | nil => rfl
  | cons decision moves ih =>
    obtain ⟨thread, action⟩ := decision
    cases action <;>
      simp only [Sig.Hom.mapSchedule, List.map_cons, CooperativeMap.action,
        Cooperative.atomicSchedule] at ih ⊢
    all_goals rw [ih]

theorem namedModel_eq (vm : Scheduler A) (initial : vm.State) :
    Prod.snd '' vm.model initial = namedModel vm.step initial := by
  ext obs
  constructor
  · rintro ⟨_, ⟨moves, word, final, path, rfl⟩, rfl⟩
    exact ⟨moves, word, final, path, rfl⟩
  · rintro ⟨moves, word, final, path, rfl⟩
    exact ⟨(vm.log moves, word), ⟨moves, word, final, path, rfl⟩, rfl⟩

theorem mem_countedModel (vm : Scheduler A) (initial : vm.State) (obs : A.CountedWord) :
    obs ∈ vm.countedModel initial ↔
      ∃ moves final, Scheduled vm.step moves initial obs.2 final ∧
        (vm.log moves).countP (fun decision => decision.2.isAtomic) = obs.1 := by
  constructor
  · rintro ⟨_, ⟨moves, word, final, path, rfl⟩, rfl⟩
    exact ⟨moves, final, path, rfl⟩
  · rintro ⟨moves, final, path, count⟩
    exact ⟨(vm.log moves, obs.2), ⟨moves, obs.2, final, path, rfl⟩, Prod.ext count rfl⟩

theorem atomic_count (step : Transition State A.ThreadId Instruction A.Event)
    (moves : Schedule A.ThreadId Instruction) :
    ((Scheduler.atomic step).log moves).countP (fun decision => decision.2.isAtomic) =
      moves.length := by
  induction moves with
  | nil => rfl
  | cons _ _ ih => simp [Scheduler.log, Scheduler.atomic, Move.isAtomic, ← ih]

theorem critical_count (program : CriticalRegion.Program State A.ThreadId Instruction A.Event)
    (moves : Schedule A.ThreadId (CriticalRegion.Action Instruction)) :
    ((Scheduler.critical program).log moves).countP (fun decision => decision.2.isAtomic) =
      (CriticalRegion.atomicSchedule moves).length := by
  induction moves with
  | nil => rfl
  | cons decision moves ih =>
    obtain ⟨thread, choice⟩ := decision
    cases choice <;> simp [Scheduler.log, Scheduler.critical, Move.isAtomic,
      CriticalRegion.atomicSchedule, ← ih]

theorem cooperative_count (program : Cooperative.Program State A.ThreadId Instruction A.Event)
    (policy : Cooperative.DispatchPolicy State A.ThreadId)
    (moves : Schedule A.ThreadId (Cooperative.Action Instruction)) :
    ((Scheduler.cooperative program policy).log moves).countP (fun decision => decision.2.isAtomic) =
      (Cooperative.atomicSchedule moves).length := by
  induction moves with
  | nil => rfl
  | cons decision moves ih =>
    obtain ⟨thread, choice⟩ := decision
    cases choice <;> simp [Scheduler.log, Scheduler.cooperative, Move.isAtomic,
      Cooperative.atomicSchedule, ← ih]

theorem mem_atomic_counted (step : Transition State A.ThreadId Instruction A.Event)
    (initial : State) (n : Nat) (word : A.NamedWord) :
    (n, word) ∈ (Scheduler.atomic step).countedModel initial ↔
      ∃ final, (final, word) ∈ namedOutcomes (run step n) initial := by
  rw [mem_countedModel]
  simp only [atomic_count, mem_run_iff_exists_schedule]
  constructor
  · rintro ⟨moves, final, path, count⟩
    exact ⟨final, moves, count, path⟩
  · rintro ⟨final, moves, count, path⟩
    exact ⟨moves, final, path, count⟩

theorem mem_critical_counted (program : CriticalRegion.Program State A.ThreadId Instruction A.Event)
    (view : State → Abstract) (initial : CriticalRegion.Config State A.ThreadId)
    (n : Nat) (word : A.NamedWord) :
    (n, word) ∈ (Scheduler.critical program).countedModel initial ↔
      ∃ final, (final, word) ∈ CriticalRegion.observedOutcomes program view initial n := by
  rw [mem_countedModel]
  constructor
  · rintro ⟨moves, final, path, count⟩
    exact ⟨view final.vm, moves, final, (critical_count program moves).symm.trans count, path, rfl⟩
  · rintro ⟨_, moves, final, count, path, _⟩
    exact ⟨moves, final, path, (critical_count program moves).trans count⟩

theorem mem_cooperative_counted (program : Cooperative.Program State A.ThreadId Instruction A.Event)
    (policy : Cooperative.DispatchPolicy State A.ThreadId) (view : State → Abstract)
    (initial : Cooperative.Config State A.ThreadId) (n : Nat) (word : A.NamedWord) :
    (n, word) ∈ (Scheduler.cooperative program policy).countedModel initial ↔
      ∃ final, (final, word) ∈ Cooperative.observedOutcomes program policy view initial n := by
  rw [mem_countedModel]
  constructor
  · rintro ⟨moves, final, path, count⟩
    exact ⟨view final.vm, moves, final, (cooperative_count program policy moves).symm.trans count, path, rfl⟩
  · rintro ⟨_, moves, final, count, path, _⟩
    exact ⟨moves, final, path, (cooperative_count program policy moves).trans count⟩

end Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers
