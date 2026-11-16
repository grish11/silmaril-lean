module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Elaboration.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open Kore.Modules.Checking
open Silmaril.Proofs.Logic.Kore.FixedPoint (collect_some collect_pure)

private theorem some_heq {α β : Type} {x : α} {y : β} (h : HEq x y) : HEq (some x) (some y) := by
  cases h
  rfl

private theorem elaboratePackage_sort_heq (A : Package) (mi fuel : Nat) (sets objects : Names)
    {s t : String} (same : s = t) (raw : RawPattern) :
    HEq (elaboratePackage A mi fuel sets objects s raw)
      (elaboratePackage A mi fuel sets objects t raw) := by
  cases same
  rfl

private theorem collect_of_pointwise {n : Nat} {α : Fin n → Type}
    (check : (i : Fin n) → Option (α i)) (xs : (i : Fin n) → α i)
    (accepted : ∀ i, check i = some (xs i)) : collect check = some xs := by
  have checks : check = fun i => some (xs i) := funext accepted
  rw [checks]
  exact collect_pure xs

/-- One alias-argument collection step. The recursive checker premise is at
this collection's body fuel; the outer alias constructor consumes one more. -/
theorem alias_arguments_forward {A B : Package} (f : Step A B) {fuel : Nat}
    (ih : FuelTransport f fuel) (mi : Nat) (sets objects : Names) (d : Alias)
    (args : List RawPattern) (isSet : Bool)
    (xs : (i : Fin (d.names isSet).length) → @Pattern A.base.scope sets objects (context (d.names isSet) i))
    (checked : collect (fun i : Fin (d.names isSet).length => do
      let arg ← d.argument args isSet ((d.names isSet).get i).1
      elaboratePackage A mi fuel sets objects (context (d.names isSet) i) arg) = some xs) :
    collect (fun i : Fin (mapNames f.semantic.native.sorts (d.names isSet)).length => do
      let arg ← (renameAlias f.semantic.native.sorts f.names d).argument
        (args.map (raw f.semantic.native.sorts f.names)) isSet
        ((mapNames f.semantic.native.sorts (d.names isSet)).get i).1
      elaboratePackage B mi fuel (mapNames f.semantic.native.sorts sets)
        (mapNames f.semantic.native.sorts objects)
        (context (mapNames f.semantic.native.sorts (d.names isSet)) i) arg) =
      some (reindexFamily f xs) := by
  let target := fun i : Fin (mapNames f.semantic.native.sorts (d.names isSet)).length => do
    let arg ← (renameAlias f.semantic.native.sorts f.names d).argument
      (args.map (raw f.semantic.native.sorts f.names)) isSet
      ((mapNames f.semantic.native.sorts (d.names isSet)).get i).1
    elaboratePackage B mi fuel (mapNames f.semantic.native.sorts sets)
      (mapNames f.semantic.native.sorts objects)
      (context (mapNames f.semantic.native.sorts (d.names isSet)) i) arg
  have each (i : Fin (d.names isSet).length) :
      target (mapIndex f.semantic.native.sorts (d.names isSet) i) =
        some (reindexFamily f xs (mapIndex f.semantic.native.sorts (d.names isSet) i)) := by
    obtain ⟨arg, argument, accepted⟩ := Option.bind_eq_some_iff.mp (collect_some _ _ checked i)
    dsimp only [target]
    rw [name_mapNames, alias_argument, argument]
    simp only [Option.map_some]
    apply eq_of_heq
    exact (elaboratePackage_sort_heq B mi fuel
      (mapNames f.semantic.native.sorts sets) (mapNames f.semantic.native.sorts objects)
      (context_mapNames f.semantic.native.sorts (d.names isSet) i) _).trans
      ((heq_of_eq (ih mi sets objects (context (d.names isSet) i) arg (xs i) accepted)).trans
        (some_heq ((reindexPattern_heq f (xs i)).trans (reindexFamily_at_heq f xs i).symm)))
  apply collect_of_pointwise target (reindexFamily f xs)
  intro j
  let i : Fin (d.names isSet).length := Fin.cast (mapNames_length f.semantic.native.sorts (d.names isSet)) j
  have back : mapIndex f.semantic.native.sorts (d.names isSet) i = j := Fin.ext rfl
  exact Eq.mp (congrArg (fun k => target k = some (reindexFamily f xs k)) back) (each i)

/-- One declared-symbol argument collection step preserves the complete
ordered family, including the exact raw argument at each finite coordinate. -/
theorem symbol_arguments_forward {A B : Package} (f : Step A B) {fuel : Nat}
    (ih : FuelTransport f fuel) (mi : Nat) (sets objects : Names)
    (inputs : List String) (args : List RawPattern) (arity : args.length = inputs.length)
    (xs : (i : Fin inputs.length) → @Pattern A.base.scope sets objects (inputs.get i))
    (checked : collect (fun i : Fin inputs.length =>
      elaboratePackage A mi fuel sets objects (inputs.get i) (args.get ⟨i.val, by omega⟩)) = some xs) :
    collect (fun i : Fin (inputs.map f.semantic.native.sorts).length =>
      elaboratePackage B mi fuel (mapNames f.semantic.native.sorts sets)
        (mapNames f.semantic.native.sorts objects) ((inputs.map f.semantic.native.sorts).get i)
        ((args.map (raw f.semantic.native.sorts f.names)).get ⟨i.val, by simpa only [List.length_map, arity] using i.isLt⟩)) =
      some (reindexArguments f xs) := by
  let target := fun i : Fin (inputs.map f.semantic.native.sorts).length =>
    elaboratePackage B mi fuel (mapNames f.semantic.native.sorts sets)
      (mapNames f.semantic.native.sorts objects) ((inputs.map f.semantic.native.sorts).get i)
      ((args.map (raw f.semantic.native.sorts f.names)).get ⟨i.val, by simpa only [List.length_map, arity] using i.isLt⟩)
  have each (i : Fin inputs.length) :
      target (mapProfileIndex f.semantic.native.sorts inputs i) =
        some (reindexArguments f xs (mapProfileIndex f.semantic.native.sorts inputs i)) := by
    have accepted := collect_some _ _ checked i
    have rawAt : (args.map (raw f.semantic.native.sorts f.names)).get
        ⟨(mapProfileIndex f.semantic.native.sorts inputs i).val, by simpa only [List.length_map, arity] using (mapProfileIndex f.semantic.native.sorts inputs i).isLt⟩ =
        raw f.semantic.native.sorts f.names (args.get ⟨i.val, by omega⟩) := by
      simp [mapProfileIndex, List.get_eq_getElem]
    dsimp only [target]
    rw [rawAt]
    apply eq_of_heq
    exact (elaboratePackage_sort_heq B mi fuel
      (mapNames f.semantic.native.sorts sets) (mapNames f.semantic.native.sorts objects)
      (profileSort_map f.semantic.native.sorts inputs i) _).trans
      ((heq_of_eq (ih mi sets objects (inputs.get i) (args.get ⟨i.val, by omega⟩) (xs i) accepted)).trans
        (some_heq ((reindexPattern_heq f (xs i)).trans (reindexArguments_at_heq f xs i).symm)))
  apply collect_of_pointwise target (reindexArguments f xs)
  intro j
  let i : Fin inputs.length := Fin.cast (List.length_map _) j
  have back : mapProfileIndex f.semantic.native.sorts inputs i = j := Fin.ext rfl
  exact Eq.mp (congrArg (fun k => target k = some (reindexArguments f xs k)) back) (each i)

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
