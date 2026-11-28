module

public import Silmaril.Semantics.ConcurrentTrace.Blocking.Defs
public import Silmaril.Semantics.ConcurrentTrace.TraceMonoid.Thms
import Silmaril.Semantics.ConcurrentTrace.Thms
import Silmaril.Proofs.Semantics.ConcurrentTrace.Blocking.Basic

public section

namespace Silmaril.Semantics.ConcurrentTrace.Blocking

universe u v u' v'

variable {Name : Type u} {Ev : Type v} {Name' : Type u'} {Ev' : Type v'}
variable {T : Type u} {E : Type v} {T' : Type u'} {E' : Type v'}

theorem Footprint.independent_symm (F : Footprint Name Ev) : Std.Symm F.Independent :=
  ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩

theorem Footprint.independent_irrefl (F : Footprint Name Ev) : Std.Irrefl F.Independent :=
  ⟨fun _ h => h.1 rfl⟩

theorem Footprint.singleton_mul_comm_iff (F : Footprint Name Ev) (a b : Ev) :
    TraceMonoid.singleton F.Independent a * TraceMonoid.singleton F.Independent b =
      TraceMonoid.singleton F.Independent b * TraceMonoid.singleton F.Independent a ↔
      a = b ∨ F.Independent a b :=
  TraceMonoid.singleton_mul_comm_iff F.independent_symm a b

/-- An injective owner renaming and exact preservation of cross-block membership
suffice for a letter map to preserve and reflect independence. The letter map
may identify labels, for example by mapping different payloads to one value. -/
theorem Footprint.independent_map_iff (F : Footprint Name Ev) (G : Footprint Name' Ev')
    (r : Name → Name') (f : Ev → Ev') (hr : Function.Injective r)
    (howner : ∀ a, G.owner (f a) = r (F.owner a))
    (hblocks : ∀ a b, r (F.owner a) ∈ G.blocks (f b) ↔ F.owner a ∈ F.blocks b)
    (a b : Ev) : G.Independent (f a) (f b) ↔ F.Independent a b :=
  Proofs.Semantics.ConcurrentTrace.Blocking.independent_map_iff F G r f hr howner hblocks a b

/-- The blocking alphabet presents exactly the old independence relation. -/
theorem independent_encode_iff (a b : Letter T E) :
    (eventSync T E).Independent (encodeLetter a) (encodeLetter b) ↔ a.Independent b :=
  Proofs.Semantics.ConcurrentTrace.Blocking.independent_encode_iff a b

/-- Any two synchronization letters share the reserved owner. -/
theorem eventSync_syncs_dependent (ts us : List T) :
    ¬ (eventSync T E).Independent (.inr ts) (.inr us) :=
  fun h => h.1 rfl

/-- The alphabet equivalence descends in both directions to a monoid equivalence. -/
@[expose] def eventSyncEquiv : Trace T E ≃* (eventSync T E).Trace :=
  TraceMonoid.mapEquiv encodeLetter independent_encode_iff

@[simp] theorem eventSyncEquiv_ofWord (word : Word T E) :
    eventSyncEquiv (ofWord word) =
      TraceMonoid.ofWord (eventSync T E).Independent (word.map encodeLetter) :=
  TraceMonoid.mapEquiv_ofWord _ _ _

@[simp] theorem eventSyncEquiv_singleton (a : Letter T E) :
    eventSyncEquiv (singleton a) = TraceMonoid.singleton (eventSync T E).Independent (encodeLetter a) :=
  eventSyncEquiv_ofWord [a]

/-- Equality of encoded word classes reflects the old swap equivalence. -/
theorem eventSync_ofWord_eq_iff (x y : Word T E) :
    TraceMonoid.ofWord (eventSync T E).Independent (x.map encodeLetter) =
      TraceMonoid.ofWord (eventSync T E).Independent (y.map encodeLetter) ↔ Equivalent x y := by
  rw [← eventSyncEquiv_ofWord, ← eventSyncEquiv_ofWord, eventSyncEquiv.injective.eq_iff, ofWord_eq_iff]

theorem eventSync_map_independent_iff (f : T → T') (hf : Function.Injective f) (g : E → E')
    (a b : EventSyncLetter T E) :
    (eventSync T' E').Independent (mapEventSyncLetter f g a) (mapEventSyncLetter f g b) ↔
      (eventSync T E).Independent a b :=
  Proofs.Semantics.ConcurrentTrace.Blocking.eventSync_map_independent_iff f hf g a b

/-- Injective thread renaming and arbitrary payload mapping on the blocking presentation. -/
@[expose] def eventSyncMap (f : T → T') (hf : Function.Injective f) (g : E → E') :
    (eventSync T E).Trace →* (eventSync T' E').Trace :=
  TraceMonoid.map (mapEventSyncLetter f g) (fun {a b} => (eventSync_map_independent_iff f hf g a b).mpr)

@[simp] theorem encodeLetter_map (f : T → T') (g : E → E') (a : Letter T E) :
    encodeLetter (a.map f g) = mapEventSyncLetter f g (encodeLetter a) := by
  cases a <;> rfl

/-- The monoid equivalence commutes with thread and payload maps. -/
theorem eventSync_natural (f : T → T') (hf : Function.Injective f) (g : E → E') :
    (eventSyncMap f hf g).comp (eventSyncEquiv (T := T) (E := E)).toMonoidHom =
      (eventSyncEquiv (T := T') (E := E')).toMonoidHom.comp (mapTrace f hf g) := by
  apply hom_ext
  intro a
  simp [eventSyncMap]

end Silmaril.Semantics.ConcurrentTrace.Blocking
