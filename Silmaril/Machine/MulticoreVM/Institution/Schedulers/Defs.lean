module

public import Silmaril.Machine.MulticoreVM.CriticalRegion.Defs
public import Silmaril.Machine.MulticoreVM.Cooperative.Defs
public import Silmaril.Machine.MulticoreVM.Institution.Defs

/-! # Scheduler interpretations of the finite trace institution -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Semantics.ConcurrentTrace (LocalLetter)

universe u

/-- The decision log distinguishes ordinary instructions, including silent ones,
from scheduler controls. Instruction operands belong to the interpretation. -/
inductive Move where
  | atomic
  | enter
  | leave
  | dispatch
  | yield
  | complete

def Move.isAtomic : Move → Bool
  | .atomic => true
  | _ => false

/-- The chronological decisions and the chronological effect word are recorded separately. -/
abbrev Sig.ScheduledWord (A : Sig.{u}) := List (A.ThreadId × Move) × A.NamedWord

abbrev Sig.CountedWord (A : Sig.{u}) := Nat × A.NamedWord

variable {A B : Sig.{u}} {State Instruction : Type u}

def Sig.Hom.mapScheduled (f : A ⟶ B) (w : A.ScheduledWord) : B.ScheduledWord :=
  (w.1.map fun (thread, move) => (f.thread thread, move), f.mapNamed w.2)

def Sig.Hom.mapCounted (f : A ⟶ B) (w : A.CountedWord) : B.CountedWord :=
  (w.1, f.mapNamed w.2)

/-- Drop the scheduler controls and retain the number of ordinary instructions
and the original chronological effect word. -/
def eraseAdministration (w : A.ScheduledWord) : A.CountedWord :=
  (w.1.countP fun decision => decision.2.isAtomic, w.2)

/-- The operational carriers live in the interpretation of a signature.
A state can contain thread-local data, program control or shared state. -/
structure Scheduler (A : Sig.{u}) where
  State : Type u
  Instruction : Type u
  step : Transition State A.ThreadId Instruction A.Event
  classify : Instruction → Move

namespace Scheduler

abbrev atomic (step : Transition State A.ThreadId Instruction A.Event) : Scheduler A :=
  ⟨State, Instruction, step, fun _ => .atomic⟩

abbrev critical (program : CriticalRegion.Program State A.ThreadId Instruction A.Event) :
    Scheduler A :=
  ⟨CriticalRegion.Config State A.ThreadId, CriticalRegion.Action Instruction,
    CriticalRegion.Step program, fun
      | .atomic _ => .atomic
      | .enter => .enter
      | .leave => .leave⟩

abbrev cooperative (program : Cooperative.Program State A.ThreadId Instruction A.Event)
    (policy : Cooperative.DispatchPolicy State A.ThreadId) : Scheduler A :=
  ⟨Cooperative.Config State A.ThreadId, Cooperative.Action Instruction,
    Cooperative.Step program policy, fun
      | .atomic _ => .atomic
      | .dispatch => .dispatch
      | .yield => .yield
      | .complete => .complete⟩

def log (vm : Scheduler A) (moves : Schedule A.ThreadId vm.Instruction) :
    List (A.ThreadId × Move) :=
  moves.map fun decision => (decision.thread, vm.classify decision.choice)

/-- The behavior of all successful prefixes, with both decisions and effects visible.
As in `ofVM`, the endpoint state is existentially quantified. -/
def model (vm : Scheduler A) (initial : vm.State) : Model A.ScheduledWord :=
  { obs | ∃ moves word final, Scheduled vm.step moves initial word final ∧
      (vm.log moves, word) = obs }

def countedModel (vm : Scheduler A) (initial : vm.State) : Model A.CountedWord :=
  eraseAdministration '' vm.model initial

end Scheduler

/-- Rename the effects observed in an ordinary instruction, including synchronization names. -/
def Sig.Hom.mapFragment (f : A ⟶ B) (fragment : Fragment A.ThreadId A.Event) :
    Fragment B.ThreadId B.Event :=
  fragment.map (LocalLetter.map f.thread f.event)

def Sig.Hom.mapSchedule (f : A ⟶ B) {I J : Type u} (instruction : I → J)
    (schedule : Schedule A.ThreadId I) : Schedule B.ThreadId J :=
  schedule.map fun d => ⟨f.thread d.thread, instruction d.choice⟩

/-- A forward operational map has to preserve a transition and its observed effects.
State and instruction maps are allowed to identify values. -/
structure StepMap (f : A ⟶ B) {S T I J : Type u}
    (source : Transition S A.ThreadId I A.Event) (target : Transition T B.ThreadId J B.Event) where
  state : S → T
  instruction : I → J
  step : ∀ {thread choice initial fragment final}, source thread choice initial fragment final →
    target (f.thread thread) (instruction choice) (state initial) (f.mapFragment fragment)
      (state final)

structure Scheduler.Forward (f : A ⟶ B) (source : Scheduler A) (target : Scheduler B)
    extends StepMap f source.step target.step where
  classify : ∀ choice, target.classify (instruction choice) = source.classify choice

/-- A program with internal effects can interpret them into the existing fragment carrier. -/
def interpretEffects {Effect : Type u}
    (step : A.ThreadId → Instruction → State → Effect → State → Prop)
    (observe : Effect → Fragment A.ThreadId A.Event) :
    Transition State A.ThreadId Instruction A.Event :=
  fun thread instruction initial fragment final =>
    ∃ effect, step thread instruction initial effect final ∧ observe effect = fragment

/-- A map of internal effects must preserve raw execution and commute with observation. -/
def StepMap.ofEffects (f : A ⟶ B) {S T I J E F : Type u}
    {source : A.ThreadId → I → S → E → S → Prop}
    {target : B.ThreadId → J → T → F → T → Prop}
    {observe : E → Fragment A.ThreadId A.Event} {observe' : F → Fragment B.ThreadId B.Event}
    (state : S → T) (instruction : I → J) (effect : E → F)
    (step : ∀ {thread choice initial e final}, source thread choice initial e final →
      target (f.thread thread) (instruction choice) (state initial) (effect e) (state final))
    (commutes : ∀ e, observe' (effect e) = f.mapFragment (observe e)) :
    StepMap f (interpretEffects source observe) (interpretEffects target observe') where
  state := state
  instruction := instruction
  step := fun ⟨e, run, same⟩ => ⟨effect e, step run, (commutes e).trans (congrArg _ same)⟩

/-- Critical control maps must commute with both continuation relations.
Completion is reflected on mapped threads so that running threads stay runnable
with respect to the finished guard. The dispatcher only tests owner equality. -/
structure CriticalMap (f : A ⟶ B) {S T I J : Type u}
    (source : CriticalRegion.Program S A.ThreadId I A.Event)
    (target : CriticalRegion.Program T B.ThreadId J B.Event)
    extends StepMap f source.atomic target.atomic where
  finished : ∀ thread s, target.finished (f.thread thread) (state s) → source.finished thread s
  enter : ∀ {thread s t}, source.enter thread s t → target.enter (f.thread thread) (state s) (state t)
  leave : ∀ {thread s t}, source.leave thread s t → target.leave (f.thread thread) (state s) (state t)

def CriticalMap.config {S T I J : Type u}
    {source : CriticalRegion.Program S A.ThreadId I A.Event}
    {target : CriticalRegion.Program T B.ThreadId J B.Event}
    {f : A ⟶ B} (m : CriticalMap f source target)
    (cfg : CriticalRegion.Config S A.ThreadId) : CriticalRegion.Config T B.ThreadId :=
  ⟨m.state cfg.vm, cfg.owner.map f.thread⟩

def CriticalMap.action {S T I J : Type u}
    {source : CriticalRegion.Program S A.ThreadId I A.Event}
    {target : CriticalRegion.Program T B.ThreadId J B.Event}
    {f : A ⟶ B} (m : CriticalMap f source target) :
    CriticalRegion.Action I → CriticalRegion.Action J
  | .atomic i => .atomic (m.instruction i)
  | .enter => .enter
  | .leave => .leave

/-- Yield-only maps preserve the yield continuation and the dispatch policy.
The equivalence for finished guards preserves both activity and retirement. -/
structure CooperativeMap (f : A ⟶ B) {S T I J : Type u}
    (source : Cooperative.Program S A.ThreadId I A.Event)
    (target : Cooperative.Program T B.ThreadId J B.Event)
    (policy : Cooperative.DispatchPolicy S A.ThreadId)
    (policy' : Cooperative.DispatchPolicy T B.ThreadId)
    extends StepMap f source.atomic target.atomic where
  finished : ∀ thread s, target.finished (f.thread thread) (state s) ↔ source.finished thread s
  yieldTo : ∀ {thread s t}, source.yieldTo thread s t →
    target.yieldTo (f.thread thread) (state s) (state t)
  dispatch : ∀ {s thread}, policy s thread → policy' (state s) (f.thread thread)

def CooperativeMap.config {S T I J : Type u}
    {source : Cooperative.Program S A.ThreadId I A.Event}
    {target : Cooperative.Program T B.ThreadId J B.Event}
    {policy : Cooperative.DispatchPolicy S A.ThreadId} {policy' : Cooperative.DispatchPolicy T B.ThreadId}
    {f : A ⟶ B} (m : CooperativeMap f source target policy policy')
    (cfg : Cooperative.Config S A.ThreadId) : Cooperative.Config T B.ThreadId :=
  ⟨m.state cfg.vm, cfg.owner.map f.thread⟩

def CooperativeMap.action {S T I J : Type u}
    {source : Cooperative.Program S A.ThreadId I A.Event}
    {target : Cooperative.Program T B.ThreadId J B.Event}
    {policy : Cooperative.DispatchPolicy S A.ThreadId} {policy' : Cooperative.DispatchPolicy T B.ThreadId}
    {f : A ⟶ B} (m : CooperativeMap f source target policy policy') :
    Cooperative.Action I → Cooperative.Action J
  | .atomic i => .atomic (m.instruction i)
  | .dispatch => .dispatch
  | .yield => .yield
  | .complete => .complete

end Silmaril.Machine.MulticoreVM.Institution
