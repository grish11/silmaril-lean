module

public import Silmaril.Formats.Dasl.Resolve.View.Defs
import Silmaril.Formats.Dasl.Thms
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

variable {Name : Type}

theorem observeWith_shallow (objects : Name → Option (Partial Name)) (blobs : Name → Option ByteArray)
    (tree : Shallow Name) : (tree.observeWith objects blobs).shallow = tree := by
  induction tree with
  | ref link =>
    cases link <;> simp only [Shallow.observeWith] <;> split <;> rfl
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict keys _ ih => exact congrArg (Tree.dict keys) (funext ih)
  | list len _ ih => exact congrArg (Tree.list len) (funext ih)
  | _ => rfl

private theorem emptyBindings {store : Store Name} {tree : Partial Name}
    (objects : ∀ name payload, ¬ tree.bindings.objects name payload)
    (blobs : ∀ name payload, ¬ tree.bindings.blobs name payload) : tree.bindings.Subset store :=
  ⟨by intro name payload hit; exact (objects name payload hit).elim,
   by intro name payload hit; exact (blobs name payload hit).elim⟩

theorem observeWith_bindings {store : Store Name} {objects : Name → Option (Partial Name)}
    {blobs : Name → Option ByteArray}
    (objectSound : ∀ name target, objects name = some target → PartialNames store name target)
    (blobSound : ∀ name payload, blobs name = some payload → store.blobs name payload)
    (tree : Shallow Name) : (tree.observeWith objects blobs).bindings.Subset store := by
  induction tree with
  | ref link =>
    cases link with
    | obj name =>
      simp only [Shallow.observeWith]
      split
      · exact emptyBindings (fun _ _ => id) (fun _ _ => id)
      · rename_i target found
        have sound := objectSound name target found
        refine ⟨?_, sound.2.2⟩
        intro key payload hit
        rcases hit with ⟨rfl, rfl⟩ | deeper
        · exact sound.1
        · exact sound.2.1 deeper
    | blob name =>
      simp only [Shallow.observeWith]
      split
      · exact emptyBindings (fun _ _ => id) (fun _ _ => id)
      · rename_i payload found
        refine ⟨by intro key value impossible; exact impossible.elim, ?_⟩
        rintro key value ⟨rfl, rfl⟩
        exact blobSound key value found
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ _ ih | list _ _ ih =>
    refine ⟨?_, ?_⟩ <;> rintro name payload ⟨index, hit⟩
    · exact (ih index).1 hit
    · exact (ih index).2 hit
  | _ => exact emptyBindings (fun _ _ => id) (fun _ _ => id)

theorem observe_shallow (reader : Reader Name) (fuel : Nat) (tree : Shallow Name) :
    (reader.observe fuel tree).shallow = tree := by
  cases fuel with
  | zero => exact Shallow.shallow_embed tree
  | succ => exact observeWith_shallow _ _ tree

theorem observe_bindings (reader : Reader Name) (fuel : Nat) (tree : Shallow Name) :
    (reader.observe fuel tree).bindings.Subset reader.store := by
  induction fuel generalizing tree with
  | zero =>
    induction tree with
    | obj impossible _ _ | blob impossible _ => exact impossible.elim
    | dict _ _ ih | list _ _ ih =>
      refine ⟨?_, ?_⟩ <;> rintro name payload ⟨index, hit⟩
      · exact (ih index).1 hit
      · exact (ih index).2 hit
    | _ => exact emptyBindings (fun _ _ => id) (fun _ _ => id)
  | succ fuel ih =>
    apply observeWith_bindings (store := reader.store)
    · intro name target found
      obtain ⟨source, hit, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨(observe_shallow reader fuel source).symm ▸ hit, ih source⟩
    · intro name payload hit; exact hit

theorem observeWith_mono {older newer : Name → Option (Partial Name)} (blobs : Name → Option ByteArray)
    (advances : ∀ name old, older name = some old → ∃ next, newer name = some next ∧ Extends old next)
    (tree : Shallow Name) : Extends (tree.observeWith older blobs) (tree.observeWith newer blobs) := by
  induction tree with
  | ref link =>
    cases link with
    | obj name =>
      cases old : older name with
      | none =>
        cases next : newer name with
        | none => simpa [Shallow.observeWith, old, next] using Extends.refl (.ref (.obj name))
        | some target => simpa [Shallow.observeWith, old, next] using Extends.openObj name target
      | some target =>
        obtain ⟨result, next, step⟩ := advances name target old
        simpa [Shallow.observeWith, old, next] using Extends.obj name step
    | blob => exact .same _
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ _ ih => exact .dict ih
  | list _ _ ih => exact .list ih
  | _ => exact .same _

theorem observe_succ (reader : Reader Name) (fuel : Nat) (tree : Shallow Name) :
    Extends (reader.observe fuel tree) (reader.observe (fuel + 1) tree) := by
  induction fuel generalizing tree with
  | zero =>
    have base := (reader.observe 1 tree).shallow_le
    rw [observe_shallow] at base
    exact base
  | succ fuel ih =>
    apply observeWith_mono
    intro name old found
    obtain ⟨source, hit, rfl⟩ := Option.map_eq_some_iff.mp found
    exact ⟨reader.observe (fuel + 1) source, by simp [hit], ih source⟩

theorem observe_mono (reader : Reader Name) (tree : Shallow Name) {low high : Nat} (order : low ≤ high) :
    Extends (reader.observe low tree) (reader.observe high tree) := by
  induction order with
  | refl => exact .same _
  | step _ ih => exact ih.trans (observe_succ reader _ tree)

private theorem commonFuel {Index : Type} (indices : Finset Index) (covers : ∀ index, index ∈ indices)
    {Ready : Nat → Index → Prop} (bounds : ∀ index, ∃ bound, ∀ fuel, bound ≤ fuel → Ready fuel index) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ index, Ready fuel index := by
  classical
  let need (index : Index) := (bounds index).choose
  refine ⟨indices.sup need, ?_⟩
  intro fuel enough index
  exact (bounds index).choose_spec fuel ((Finset.le_sup (f := need) (covers index)).trans enough)

theorem observe_eventually (reader : Reader Name) {source : Shallow Name} {target : Named Name}
    (expanded : Expands reader.store source target) :
    ∃ bound, ∀ fuel, bound ≤ fuel → reader.observe fuel source = target.embed := by
  induction expanded with
  | @obj name source target hit _ ih =>
    change reader.object? name = some source at hit
    obtain ⟨bound, ready⟩ := ih
    refine ⟨bound + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      have child := ready fuel (Nat.le_of_succ_le_succ enough)
      simp [Reader.observe, Shallow.observeWith, hit, child, Named.embed, Tree.map]
  | @blob name payload hit =>
    change reader.blob? name = some payload at hit
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ => simp [Reader.observe, Shallow.observeWith, hit, Named.embed, Tree.map]
  | @dict keys source target _ ih =>
    obtain ⟨bound, ready⟩ := commonFuel keys.attach keys.mem_attach ih
    refine ⟨bound, ?_⟩
    intro fuel enough
    have children := funext (ready fuel enough)
    cases fuel <;> exact congrArg (Tree.dict keys) children
  | @list len source target _ ih =>
    obtain ⟨bound, ready⟩ := commonFuel Finset.univ (fun _ => Finset.mem_univ _) ih
    refine ⟨bound, ?_⟩
    intro fuel enough
    have children := funext (ready fuel enough)
    cases fuel <;> exact congrArg (Tree.list len) children
  | _ => exact ⟨0, fun fuel _ => by cases fuel <;> rfl⟩

end Silmaril.Proofs.Formats.Dasl
