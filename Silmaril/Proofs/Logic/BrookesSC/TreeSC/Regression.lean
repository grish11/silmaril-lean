module

public import Silmaril.Logic.BrookesSC.TreeSC.Thms

public section

namespace Silmaril.Proofs.Logic.BrookesSC.TreeSC.Regression

open CategoryTheory Silmaril.Logic.BrookesSC Silmaril.Logic.BrookesSC.TreeSC
open Silmaril.Semantics.Brookes (Behavior Reduces Rewrite Trace)
open Silmaril.Semantics.Brookes.TreeSC (Code Store readBehavior writeBehavior treeBehavior treeBehavior_code)
open Silmaril.Semantics.TrackA.Interaction (WeakITree)

def store (n : Nat) : Store Unit := fun _ => n

def set (value : Nat) : Code Unit := .store .plain () value .done

def increment (amount : Nat) : Code Unit := .load .scAtomic () fun reply => set (reply + amount)

@[expose] def tagged : Signature (world Unit) where
  Op _ := Bool

def relabel : signature Unit ⟶ tagged where
  label _ := true

def model : Concrete.TraceModel tagged where
  external {sort} := sort.elim

/-- The nonidentity label map retains both modes and the write's reply-dependent payload. -/
theorem translated_increment (amount : Nat) :
    (encode (𝟙 (signature Unit)) (increment amount)).translate relabel =
      .call (d := .primitive (.load () .scAtomic ())) true (fun reply =>
        .call (d := .primitive (.store () .plain () (reply + amount))) true (fun _ => .ret ())) := by
  rw [encode_translate]
  rfl

private theorem update_store (before value : Nat) :
    store value = Function.update (store before) () value := by
  funext loc
  cases loc
  simp [store]

private theorem increment_word (amount reply writeFrom : Nat) :
    (model.eval (encode relabel (increment amount))).accepts
      (Trace.mapStores (storeEquiv Unit)
        [(store reply, store reply), (store writeFrom, store (reply + amount))]) () := by
  rw [eval_encode, Behavior.transport_accepts_iff, Trace.mapStores_inverse, treeBehavior_code]
  change ((readBehavior ()).bind (fun n => (set (n + amount)).denote)).accepts _ ()
  apply Behavior.bind_accepts_iff.mpr
  refine ⟨[(store reply, store reply)], [(store writeFrom, store (reply + amount))], reply,
    ?_, ?_, .refl _⟩
  · exact Behavior.atomic_accepts_iff.mpr ⟨_, _, ⟨rfl, rfl⟩, .refl _⟩
  · change ((writeBehavior () (reply + amount)).bind Behavior.ret).accepts _ ()
    rw [Behavior.bind_ret]
    exact Behavior.atomic_accepts_iff.mpr ⟨_, _, update_store _ _, .refl _⟩

/-- The load sees 1 and writes 2 even though the write starts at the environment's 0. -/
theorem accepts_gapped_increment :
    (model.eval (encode relabel (increment 1))).accepts
      [(storeEquiv Unit (store 1), storeEquiv Unit (store 1)),
       (storeEquiv Unit (store 0), storeEquiv Unit (store 2))] () :=
  increment_word 1 1 0

/-- The translated open inequation fails at amount 1. From 1 the increment ends
at 2, while setting the input amount can only end at 1. -/
theorem translated_inequation_fails :
    ¬ ((inequation (𝟙 (signature Unit)) increment set).translate relabel).Satisfies model := by
  rw [inequation_translate, Category.id_comp]
  intro satisfies
  have step := increment_word 1 1 1
  have complete : (model.eval (encode relabel (increment 1))).completes
      (storeEquiv Unit (store 1)) (storeEquiv Unit (store 2)) () :=
    (model.eval (encode relabel (increment 1))).stable step
      ((Reduces.refl _).tail (Rewrite.mumble [] [] _ _ _))
  rw [eval_encode, Behavior.transport_completes_iff] at complete
  have rhs : (treeBehavior WeakITree.unfold (set 1).toTree).completes (store 1) (store 2) () :=
    (satisfies_iff relabel model increment set).mp satisfies 1 _ complete
  rw [treeBehavior_code] at rhs
  change ((writeBehavior () 1).bind Behavior.ret).completes (store 1) (store 2) () at rhs
  rw [Behavior.bind_ret, writeBehavior, Behavior.atomic_completes_iff] at rhs
  have impossible := congrFun rhs ()
  simp [store] at impossible

end Silmaril.Proofs.Logic.BrookesSC.TreeSC.Regression
