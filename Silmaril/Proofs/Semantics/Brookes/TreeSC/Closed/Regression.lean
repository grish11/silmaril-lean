module

public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms
public import Silmaril.Semantics.TrackA.Interaction.Thms

public section

namespace Silmaril.Semantics.Brookes.TreeSC.Closed.Regression

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.TrackA.Concurrency (sequential primitive Shared)
open Silmaril.Semantics.TrackA.Interaction

def zero : Store Unit := fun _ => 0
def one : Store Unit := fun _ => 1
def two : Store Unit := fun _ => 2

def set (value : Nat) : Code Unit := .store .plain () value .done
def loadThenSet : Code Unit :=
  .load .scAtomic () fun reply => if reply = 0 then set 2 else .done

private theorem runWithInterference :
    MachineFollows openGap ((set 1).seq loadThenSet) zero
      [⟨⟨Request.write .plain () 1, ()⟩, zero, one⟩,
       ⟨⟨Request.read .scAtomic (), (0 : Nat)⟩, zero, zero⟩,
       ⟨⟨Request.write .plain () 2, ()⟩, zero, two⟩] .done two := by
  refine .cons (q := loadThenSet) trivial ?_ (.cons (q := set 2) trivial ?_ (.cons trivial ?_ (.nil _ _)))
  · simp [MachineStep, sequential, primitive, Frame.event,
      set, Code.seq, Shared.initial]
    funext loc
    cases loc
    simp [one]
  · rfl
  · simp [MachineStep, sequential, primitive, Frame.event,
      set, Shared.initial]
    funext loc
    cases loc
    simp [two]

theorem open_join_accepts :
    (treeBehavior WeakITree.unfold ((set 1).seq loadThenSet).toTree).accepts
      [(zero, one), (zero, two)] () := by
  rw [treeBehavior_eq_machine]
  have raw : (machineBehavior ((set 1).seq loadThenSet)).accepts
      [(zero, one), (zero, zero), (zero, two)] () :=
    Behavior.generate_accepts (by simp) ⟨zero, _, two, runWithInterference, rfl⟩
  exact (machineBehavior ((set 1).seq loadThenSet)).stable raw
    ((Reduces.refl _).tail (Rewrite.mumble [(zero, one)] [] zero zero two))

private theorem set_completes_iff {s t : Store Unit} {value : Nat} :
    (set value).denote.completes s t () ↔ t = Function.update s () value := by
  change ((writeBehavior () value).bind Behavior.ret).completes s t () ↔ _
  rw [Behavior.bind_ret, writeBehavior, Behavior.atomic_completes_iff]

private theorem loadThenSet_completes_at_one {t : Store Unit} :
    loadThenSet.denote.completes one t () → t = one := by
  simp only [loadThenSet, Code.denote, Behavior.completes, Behavior.bind_accepts_iff]
  rintro ⟨left, right, reply, read, rest, reduces⟩
  obtain ⟨mid, runsLeft, runsRight⟩ :=
    Runs.append_iff.mp (Runs.of_reduces reduces (Runs.cons (Runs.nil t)))
  have completedRead : (readBehavior (R := Unit) ()).completes one mid reply :=
    (readBehavior ()).stable read (runsLeft.reduces_singleton ((readBehavior ()).nonempty read))
  obtain ⟨rfl, rfl⟩ := Behavior.atomic_completes_iff.mp completedRead
  change (if one () = 0 then set 2 else .done : Code Unit).denote.accepts right () at rest
  have ret : (Behavior.ret (Store := Store Unit) ()).accepts right () := by
    simpa only [one, Nat.one_ne_zero, ite_false, Code.denote] using rest
  have completeRet : (Behavior.ret ()).completes one t () :=
    (Behavior.ret ()).stable ret (runsRight.reduces_singleton ((Behavior.ret ()).nonempty ret))
  exact (Behavior.atomic_completes_iff.mp completeRet).1.symm

theorem no_singleton_with_interference :
    ¬ (treeBehavior WeakITree.unfold ((set 1).seq loadThenSet).toTree).completes zero two () := by
  rw [treeBehavior_code, denote_seq, Command.seq_completes_iff]
  rintro ⟨mid, first, second⟩
  have same : mid = one := by
    rw [set_completes_iff.mp first]
    funext loc
    cases loc
    simp [one]
  subst mid
  have impossible := congrFun (loadThenSet_completes_at_one second) ()
  exact (by decide : (2 : Nat) ≠ 1) impossible

inductive Nest where
  | root | inner | leaf (result : Bool)

def nested : Coalgebra (signature Unit) Signature.finiteChoice Bool Nest
  | .root => .branch .delayed (1 : Nat) fun _ => .inner
  | .inner => .branch .stepping (2 : Nat) fun i => .leaf (decide (i.val = 1))
  | .leaf result => .ret result

private theorem nested_result (i : Fin 2) :
    (treeBehavior nested .root).completes zero zero (decide (i.val = 1)) := by
  have root : nested .root = .branch .delayed (1 : Nat) (fun _ => .inner) := rfl
  rw [treeBehavior_branch root]
  refine ⟨(0 : Fin 1), ?_⟩
  have inner : nested .inner = .branch .stepping (2 : Nat)
      (fun j => .leaf (decide (j.val = 1))) := rfl
  rw [treeBehavior_branch inner]
  refine ⟨i, ?_⟩
  apply treeBehavior_completes_iff.mpr
  exact ⟨[], _, _, ⟨.nil _, .nil _⟩, .refl, rfl⟩

theorem nested_results :
    (treeBehavior nested .root).completes zero zero false ∧
      (treeBehavior nested .root).completes zero zero true :=
  ⟨nested_result 0, nested_result 1⟩

theorem mapped_result :
    (treeBehavior (mapReturns (fun b => if b then 2 else 1) nested) .root).completes zero zero 2 := by
  rw [treeBehavior_map]
  exact ⟨true, rfl, nested_results.2⟩

def looping : Coalgebra (signature Unit) Signature.finiteChoice Unit Unit :=
  fun _ => .tau ()

def blocked : Coalgebra (signature Unit) Signature.finiteChoice Unit Unit :=
  fun _ => .branch .stepping Nat.zero Fin.elim0

private theorem blocked_no_edge {x y : Unit} : ¬ blocked.Internal x y := by
  rintro (step | ⟨_, _, i, step⟩)
  · cases step with
    | tau layer => cases layer
  · cases step with
    | choice layer _ =>
      have root : blocked x = .branch .stepping Nat.zero Fin.elim0 := rfl
      have zeroShape := (Node.branch.inj (root.symm.trans layer)).2.1
      cases zeroShape
      exact Fin.elim0 i

theorem divergence_and_deadlock_collapse :
    treeBehavior looping () = treeBehavior blocked () := by
  apply Behavior.ext
  intro word result
  have branch : blocked () = .branch .stepping Nat.zero Fin.elim0 := rfl
  rw [treeBehavior_branch branch]
  constructor
  · rintro ⟨_, ⟨_, _, _, _, ⟨_, z, _, _, ret⟩, _⟩, _⟩
    cases ret
  · rintro ⟨i, _⟩
    exact Fin.elim0 i

theorem divergence_and_deadlock_differ :
    Trace.finite [] .diverge ∈ looping.observes () ∧
    Trace.finite [] (.deadlock .stepping) ∈ blocked.observes () ∧
    Trace.finite [] .diverge ∉ blocked.observes () := by
  refine ⟨Coalgebra.observes_silent_loop rfl,
    ⟨(), (), .nil _, .refl, ⟨Nat.zero, ⟨Fin.elim0⟩, Fin.elim0, rfl⟩⟩, ?_⟩
  rintro ⟨_, _, _, _, diverges⟩
  obtain ⟨_, edge, _⟩ := diverges.unfold
  exact blocked_no_edge edge

end Silmaril.Semantics.Brookes.TreeSC.Closed.Regression
