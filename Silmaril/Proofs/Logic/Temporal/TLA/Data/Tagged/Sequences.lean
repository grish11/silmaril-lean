module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Sequences.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged.SequenceProofs

universe u

theorem tuple_of_domain {g : Graph.{u}} {n : Nat} (hd : g.domain = SetData.intRange 1 n) :
    ∃ xs : List Value.{u}, xs.length = n ∧ Graph.tuple xs = g := by
  let xs := List.ofFn fun i : Fin n =>
    (g.lookup (.integer (Int.ofNat (i.val + 1)))).getD (.set .empty)
  have hlen : xs.length = n := List.length_ofFn
  refine ⟨xs, hlen, Graph.ext_of_domain_lookup (by rw [Graph.domain_tuple, hlen, hd]) ?_⟩
  intro k hk
  rw [Graph.domain_tuple, hlen, SetData.mem_intRange] at hk
  obtain ⟨j, rfl, hj, hjn⟩ := hk
  let i := j.toNat - 1
  have hi : i < n := by omega
  have hkey : (i : Int) + 1 = j := by dsimp [i]; omega
  have hget : xs[i]'(by omega) = (g.lookup (.integer j)).getD (.set .empty) := by
    simp [xs, hkey]
  have ht := Graph.lookup_tuple xs (i := i) (by omega)
  rw [Int.natCast_add, Int.natCast_one, hkey, hget] at ht
  have hm : g.domain.mem (.integer j) := by
    rw [hd, SetData.mem_intRange]
    exact ⟨j, rfl, hj, hjn⟩
  cases h : g.lookup (.integer j) with
  | none => exact False.elim (Graph.lookup_eq_none.mp h hm)
  | some value => simpa [h] using ht

theorem mem_sequences {s : SetData.{u}} {v : Value.{u}} :
    s.sequences.mem v ↔ ∃ n : Nat, ((SetData.intRange 1 n).functionSet s).mem v := by
  change v.code ∈ (ZFSet.range fun n : Nat =>
    ((SetData.intRange 1 n).functionSet s).codes).sUnion ↔ _
  simp only [ZFSet.mem_sUnion, ZFSet.mem_range]
  exact ⟨fun ⟨_, ⟨n, rfl⟩, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨_, ⟨n, rfl⟩, h⟩⟩

theorem mem_sequences_iff_tuple {s : SetData.{u}} {v : Value.{u}} :
    s.sequences.mem v ↔ ∃ xs : List Value.{u}, Value.tuple xs = v ∧ ∀ x ∈ xs, s.mem x := by
  simp only [mem_sequences, SetData.mem_functionSet]
  constructor
  · rintro ⟨n, g, rfl, hd, hrange⟩
    obtain ⟨xs, _, rfl⟩ := tuple_of_domain hd
    refine ⟨xs, rfl, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact hrange _ _ (Graph.lookup_eq_some.mp (Graph.lookup_tuple xs hi))
  · rintro ⟨xs, rfl, hall⟩
    refine ⟨xs.length, Graph.tuple xs, rfl, Graph.domain_tuple xs, fun k x hk => ?_⟩
    have hd : (Graph.tuple xs).domain.mem k := Graph.mem_domain.mpr ⟨x, hk⟩
    rw [Graph.domain_tuple, SetData.mem_intRange] at hd
    obtain ⟨j, rfl, hj, hjn⟩ := hd
    let i := j.toNat - 1
    have hi : i < xs.length := by omega
    have hkey : (i : Int) + 1 = j := by dsimp [i]; omega
    have hlookup := Graph.lookup_tuple xs hi
    rw [Int.natCast_add, Int.natCast_one, hkey, Graph.lookup_eq_some.mpr hk] at hlookup
    rw [Option.some.inj hlookup]
    exact hall _ (List.getElem_mem hi)

theorem asSequence_eq_none {s : Value.{u}} :
    s.asSequence = none ↔ ¬ ∃ g : Graph.{u}, Value.function g = s ∧
      ∃ n : Nat, g.domain = SetData.intRange 1 n := by
  have injective : Function.Injective (Value.tuple.{u}) :=
    Value.function_injective.comp Graph.tuple_injective
  constructor
  · rintro h ⟨g, rfl, n, hd⟩
    obtain ⟨xs, _, rfl⟩ := tuple_of_domain hd
    have hsome : (Value.tuple xs).asSequence = some xs := (decode_eq_some injective).mpr rfl
    have impossible : none = some xs := h.symm.trans hsome
    cases impossible
  · intro h
    exact decode_eq_none (fun ⟨xs, eq⟩ =>
      h ⟨Graph.tuple xs, eq, xs.length, Graph.domain_tuple xs⟩)

end Silmaril.Logic.Temporal.TLA.Data.Tagged.SequenceProofs
