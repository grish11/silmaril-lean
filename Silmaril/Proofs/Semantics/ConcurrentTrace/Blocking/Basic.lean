module

public import Silmaril.Semantics.ConcurrentTrace.Blocking.Defs
import Mathlib.Data.Sum.Basic

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Blocking

open Silmaril.Semantics.ConcurrentTrace
open Silmaril.Semantics.ConcurrentTrace.Blocking

universe u v u' v'

variable {Name : Type u} {Ev : Type v} {Name' : Type u'} {Ev' : Type v'}
variable {T : Type u} {E : Type v} {T' : Type u'} {E' : Type v'}

theorem independent_map_iff (F : Footprint Name Ev) (G : Footprint Name' Ev')
    (r : Name → Name') (f : Ev → Ev') (hr : Function.Injective r)
    (howner : ∀ a, G.owner (f a) = r (F.owner a))
    (hblocks : ∀ a b, r (F.owner a) ∈ G.blocks (f b) ↔ F.owner a ∈ F.blocks b)
    (a b : Ev) : G.Independent (f a) (f b) ↔ F.Independent a b := by
  simp only [Footprint.Independent, howner, ne_eq, hr.eq_iff, hblocks]

theorem independent_encode_iff (a b : Letter T E) :
    (eventSync T E).Independent (encodeLetter a) (encodeLetter b) ↔ a.Independent b := by
  constructor
  · intro h
    cases a <;> cases b
    · exact .events (fun heq => h.1 (congrArg Sum.inl heq))
    · exact .eventSync h.2.1
    · exact .syncEvent h.2.2
    · exact (h.1 rfl).elim
  · intro h
    cases h with
    | events h => exact ⟨fun heq => h (Sum.inl.inj heq), id, id⟩
    | eventSync h => exact ⟨Sum.inl_ne_inr, h, id⟩
    | syncEvent h => exact ⟨Sum.inr_ne_inl, id, h⟩

theorem eventSync_map_independent_iff (f : T → T') (hf : Function.Injective f) (g : E → E')
    (a b : EventSyncLetter T E) :
    (eventSync T' E').Independent (mapEventSyncLetter f g a) (mapEventSyncLetter f g b) ↔
      (eventSync T E).Independent a b := by
  apply independent_map_iff (eventSync T E) (eventSync T' E') (Sum.map f id) _
    (hf.sumMap Function.injective_id) _ _ a b
  · rintro (⟨t, e⟩ | ts) <;> rfl
  · rintro (⟨t, e⟩ | ts) (⟨u, e'⟩ | us)
    · rfl
    · exact List.mem_map_of_injective hf
    · rfl
    · rfl

end Silmaril.Proofs.Semantics.ConcurrentTrace.Blocking
