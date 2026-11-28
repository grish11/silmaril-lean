module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Binders.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms
public import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Binders

open Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

theorem untuple_eq_some {arity : Nat} {value : Value.{u}} {xs : List Value.{u}} :
    value.untuple arity = some xs ↔ xs.length = arity ∧ Value.tuple xs = value := by
  have injective : Function.Injective
      (fun ys : {ys : List Value.{u} // ys.length = arity} => Value.tuple ys.val) :=
    fun _ _ h => Subtype.ext (Graph.tuple_injective (Value.function_injective h))
  simp only [Value.untuple, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨ys, hlen⟩, found, rfl⟩
    exact ⟨hlen, (decode_eq_some injective).mp found⟩
  · rintro ⟨hlen, eq⟩
    exact ⟨⟨xs, hlen⟩, (decode_eq_some injective).mpr eq, rfl⟩

theorem mem_cartesian {bounds : List SetData.{u}} {key : Value.{u}} :
    (SetData.cartesian bounds).mem key ↔
      ∃ xs, List.Forall₂ (fun x (s : SetData.{u}) => s.mem x) xs bounds ∧ Value.tuple xs = key := by
  rw [SetData.mem, SetData.cartesian, ZFSet.mem_range]
  constructor
  · rintro ⟨select, heq⟩
    refine ⟨List.ofFn (fun i => ⟨(select i).val⟩), List.forall₂_iff_get.mpr ⟨by simp, ?_⟩,
      Value.code_injective heq⟩
    intro i hi hb
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact (select ⟨i, hb⟩).property
  · rintro ⟨xs, hmem, rfl⟩
    let select (i : Fin bounds.length) : (bounds[i.val]).codes :=
      let hi : i.val < xs.length := hmem.length_eq.symm ▸ i.isLt
      ⟨xs[i.val].code, hmem.get hi i.isLt⟩
    refine ⟨select, congrArg (fun ys => (Value.tuple ys).code) ?_⟩
    apply List.ext_getElem (by simp [hmem.length_eq])
    intro i hi hb
    simp only [List.getElem_ofFn, select]

theorem cartesian_sets (bounds : List SetData.{u}) :
    Value.cartesian (bounds.map Value.set) = some (Value.set (SetData.cartesian bounds)) := by
  have decodeBounds (ss : List SetData.{u}) : (ss.map Value.set).mapM Value.asSet = some ss := by
    induction ss with
    | nil => rfl
    | cons s ss ih => simp [List.mapM_cons, ih]
  simp [Value.cartesian, decodeBounds]

end Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Binders
