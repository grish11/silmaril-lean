module

public import Silmaril.Semantics.OrderedMap.Operations.Thms
public import Silmaril.Semantics.OrderedMap.Transport.Defs

public section

namespace Silmaril.Proofs.Semantics.OrderedMap.Transport

open Silmaril.Semantics Silmaril.Semantics.OrderedMap

variable {Key Next Payload Error : Type} [LinearOrder Key] [LinearOrder Next]

theorem lookup_rekey (map : OrderedMap Key Payload) (key : Key ↪o Next) (source : Key) :
    (map.rekey key).lookup? (key source) = map.lookup? source := by
  cases found : map.lookup? source with
  | some value =>
    apply (lookup_eq_some_iff _).mpr
    exact List.mem_map.mpr ⟨(source, value), map.lookup_eq_some_iff.mp found, rfl⟩
  | none =>
    cases hit : (map.rekey key).lookup? (key source) with
    | none => rfl
    | some value =>
      obtain ⟨⟨original, payload⟩, mem, same⟩ := List.mem_map.mp ((lookup_eq_some_iff _).mp hit)
      have equal : original = source := key.injective (congrArg Prod.fst same)
      subst original
      have res := map.lookup_eq_some_iff.mpr mem
      simp [found] at res

theorem lookup_rekey_outside (map : OrderedMap Key Payload) (key : Key ↪o Next) (target : Next)
    (outside : target ∉ Set.range key) : (map.rekey key).lookup? target = none := by
  cases found : (map.rekey key).lookup? target with
  | none => rfl
  | some value =>
    obtain ⟨entry, _, same⟩ := List.mem_map.mp ((lookup_eq_some_iff _).mp found)
    exact (outside ⟨entry.1, congrArg Prod.fst same⟩).elim

theorem rekey_combine_iff (key : Key ↪o Next) (kind : Combine)
    (overlap : Overlap Key Payload Error) (nextOverlap : Overlap Next Payload Error)
    (agrees : ∀ source left right, nextOverlap (key source) left right = overlap source left right)
    (left right result : OrderedMap Key Payload) :
    (left.rekey key).combine kind nextOverlap (right.rekey key) = .ok (result.rekey key) ↔
      left.combine kind overlap right = .ok result := by
  rw [combine_spec, combine_spec]
  have step (source : Key) (left right : Option Payload) :
      kind.atKey nextOverlap (key source) left right = kind.atKey overlap source left right := by
    cases left <;> cases right <;> simp [Combine.atKey, agrees]
  constructor
  · intro correct source
    simpa only [lookup_rekey, step] using correct (key source)
  · intro correct target
    by_cases inRange : target ∈ Set.range key
    · obtain ⟨source, rfl⟩ := inRange
      simpa only [lookup_rekey, step] using correct source
    · cases kind <;> simp [lookup_rekey_outside _ _ _ inRange, Combine.atKey]

end Silmaril.Proofs.Semantics.OrderedMap.Transport
