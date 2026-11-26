module

public import Silmaril.Semantics.Brookes.TreeSC.Thms
public import Silmaril.Semantics.TrackA.Interaction.WeakITree.Thms

@[expose] public section

namespace Silmaril.Proofs.Semantics.Brookes.TreeSC.Regression

open Silmaril.Semantics.Brookes.TreeSC
open Silmaril.Semantics.TrackA.Concurrency
open Silmaril.Semantics.TrackA.Interaction

def reader : Code Unit :=
  .load .plain () fun _ => .load .plain () fun _ => .done

def writer : Code Unit := .store .plain () 1 .done

def start : Config Bool Empty Unit :=
  Config.initial (fun th => if th then writer else reader) (fun _ => 0)

def scheduledEvents : List (Event Bool Empty Unit) :=
  [⟨false, .read .plain () 0⟩, ⟨true, .write .plain () 1⟩, ⟨false, .read .plain () 1⟩]

/-- The peer's write occurs between the two reader primitives. Both threads
finish, and the read results differ. -/
theorem scheduled_interference :
    (replay start [false, true, false]).map
        (fun (es, finish) => (es, finish.shared.memory (), finish.code false, finish.code true)) =
      some (scheduledEvents, 1, .done, .done) :=
  rfl

theorem reader_boundary_stores :
    (replay start [false]).map (fun run => run.2.shared.memory ()) = some 0 ∧
    (replay start [false, true]).map (fun run => run.2.shared.memory ()) = some 1 :=
  ⟨rfl, rfl⟩

def readFrame (v : Nat) : Frame Unit :=
  ⟨⟨Request.read .plain (), v⟩, fun _ => v, fun _ => v⟩

def projected : List (Frame Unit) := [readFrame 0, readFrame 1]

/-- Admit idle gaps and the peer's 0-to-1 write at this cell. -/
def peerGap (s t : Store Unit) : Prop :=
  s = t ∨ (s = fun _ => 0) ∧ (t = fun _ => 1)

theorem reader_projection :
    scheduledEvents.filter (fun e => !e.thread) = projected.map (Frame.event false) :=
  rfl

theorem reader_open :
    Returns WeakITree.unfold peerGap reader.toTree (fun _ => 0) projected () (fun _ => 1) := by
  apply returns_iff_machine.mpr
  exact .cons (Or.inl rfl) rfl (.cons (Or.inr ⟨rfl, rfl⟩) rfl (.nil _ _))

/-- The same projected observation fails a closed run's store continuity. -/
theorem reader_not_closed :
    ¬ Returns WeakITree.unfold Eq reader.toTree (fun _ => 0) projected () (fun _ => 1) := by
  rintro ⟨_, _, ⟨_, stores⟩, _, _⟩
  change StoreFollows Eq (fun _ => 0) [readFrame 0, readFrame 1] (fun _ => 1) at stores
  cases stores with
  | cons _ _ tail =>
    cases tail with
    | cons continuity _ _ =>
      have impossible : (0 : Nat) = 1 := congrFun continuity ()
      cases impossible

def alternatives (i : Fin 2) : Code Unit := if i = 0 then .done else writer

def written : Frame Unit :=
  ⟨⟨Request.write .plain () 1, ()⟩, fun _ => 0, fun _ => 1⟩

theorem choice_returns (kind : ChoiceKind) :
    ForestReturns (choose kind alternatives) Eq (fun _ => 0) [written] () (fun _ => 1) := by
  apply choice_returns_iff_machine.mpr
  exact ⟨1, .cons rfl rfl (.nil _ _)⟩

theorem empty_forest_no_return :
    ¬ ForestReturns (Code.forest (Empty.elim : Empty → Code Unit))
      Eq (fun _ => 0) [] () (fun _ => 0) := by
  rintro ⟨root, _⟩
  exact root.elim

noncomputable def zeroChoice := choose .stepping (Fin.elim0 : Fin 0 → Code Unit)

theorem zero_way_deadlock :
    Trace.finite [] (.deadlock .stepping) ∈ zeroChoice.observes :=
  ⟨(), _, _, .nil _, .refl, ⟨(0 : Nat), ⟨Fin.elim0⟩, _, rfl⟩⟩

theorem zero_way_no_return :
    ¬ ForestReturns zeroChoice Eq (fun _ => 0) [] () (fun _ => 0) := by
  intro h
  obtain ⟨i, _⟩ := choice_returns_iff_machine.mp h
  exact i.elim0

theorem divergence_has_empty_prefix :
    Follows WeakITree.unfold Eq
      (Elgot.ITree.diverge : Tree Unit) (fun _ => 0) [] Elgot.ITree.diverge (fun _ => 0) :=
  ⟨.nil _, .nil _⟩

theorem divergence_is_observed :
    Trace.finite [] .diverge ∈ (WeakITree.toDelayed (Elgot.ITree.diverge : Tree Unit)).observes :=
  WeakITree.observes_diverge

end Silmaril.Proofs.Semantics.Brookes.TreeSC.Regression
