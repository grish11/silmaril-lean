module

public import Silmaril.Semantics.NondeterministicTrace.Finite.Thms

public section

namespace Silmaril.Proofs.Semantics.NondeterministicTrace.Maps

open Silmaril.Elgot
open Silmaril.Semantics.NondeterministicTrace Finite

universe u

variable {W V A B : Type u} [Monoid W] [Monoid V] (h : W →* V)

theorem mem_mapLog {p : Finite W A} {a : A} {v : V} :
    (a, v) ∈ (mapLog h p).outcomes ↔ ∃ w, (a, w) ∈ p.outcomes ∧ h w = v := by
  change (∃ q ∈ p.outcomes, Prod.map id h q = (a, v)) ↔ _
  constructor
  · rintro ⟨⟨a', w⟩, hp, eq⟩
    have ha : a' = a := congrArg Prod.fst eq
    exact ⟨w, ha ▸ hp, congrArg Prod.snd eq⟩
  · rintro ⟨w, hp, rfl⟩
    exact ⟨(a, w), hp, rfl⟩

theorem mapLog_pure (a : A) : mapLog h (pure a) = (pure a : Finite V A) := by
  apply outcomes_injective
  change Prod.map id h '' outcomes (pure a : Finite W A) = _
  simp [Set.image_singleton]

theorem mapLog_bind (p : Finite W A) (k : A → Finite W B) :
    mapLog h (p >>= k) = mapLog h p >>= fun a => mapLog h (k a) := by
  apply outcomes_injective
  ext ⟨b, v⟩
  simp only [mem_mapLog, mem_bind]
  constructor
  · rintro ⟨_, ⟨a, u, w, hp, hk, rfl⟩, rfl⟩
    exact ⟨a, h u, h w, ⟨u, hp, rfl⟩, ⟨w, hk, rfl⟩, (map_mul h _ _).symm⟩
  · rintro ⟨a, _, _, ⟨u, hp, rfl⟩, ⟨w, hk, rfl⟩, rfl⟩
    exact ⟨u * w, ⟨a, u, w, hp, hk, rfl⟩, map_mul h _ _⟩

private theorem runs_mapLog_forward {f : A → Finite W (B ⊕ A)} {a : A} {b : B} {w : W}
    (run : Runs f a b w) : Runs (fun x => mapLog h (f x)) a b (h w) := by
  induction run with
  | done edge => exact .done ((mem_mapLog h).2 ⟨_, edge, rfl⟩)
  | more edge tail ih =>
    rw [map_mul]
    exact .more ((mem_mapLog h).2 ⟨_, edge, rfl⟩) ih

private theorem runs_mapLog_reverse {f : A → Finite W (B ⊕ A)} {a : A} {b : B} {v : V}
    (run : Runs (fun x => mapLog h (f x)) a b v) : ∃ w, Runs f a b w ∧ h w = v := by
  induction run with
  | done edge =>
    obtain ⟨w, hw, eq⟩ := (mem_mapLog h).1 edge
    exact ⟨w, .done hw, eq⟩
  | more edge tail ih =>
    obtain ⟨u, hu, eq⟩ := (mem_mapLog h).1 edge
    obtain ⟨w, hw, eq'⟩ := ih
    exact ⟨u * w, .more hu hw, by rw [map_mul, eq, eq']⟩

theorem mapLog_iter (f : A → Finite W (B ⊕ A)) (a : A) :
    mapLog h (iter f a) = iter (fun next => mapLog h (f next)) a := by
  apply outcomes_injective
  ext ⟨b, v⟩
  simp only [mem_mapLog, mem_iter]
  exact ⟨fun ⟨w, hw, eq⟩ => eq ▸ runs_mapLog_forward h hw, runs_mapLog_reverse h⟩

theorem mapLog_injective (hh : Function.Injective h) :
    Function.Injective (mapLog h : Finite W A → Finite V A) := by
  intro p q eq
  apply outcomes_injective
  apply Set.image_injective.mpr (Function.Injective.prodMap Function.injective_id hh)
  exact congrArg outcomes eq

theorem mapLog_surjective (hh : Function.Surjective h) :
    Function.Surjective (mapLog h : Finite W A → Finite V A) := by
  intro p
  refine ⟨ofOutcomes (Prod.map id h ⁻¹' p.outcomes), outcomes_injective ?_⟩
  exact Set.image_preimage_eq _ (Function.Surjective.prodMap Function.surjective_id hh)

end Silmaril.Proofs.Semantics.NondeterministicTrace.Maps
