module

public import Silmaril.Semantics.ConcurrentTrace.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.Finite

public section

namespace Silmaril.Semantics.ConcurrentTrace

open scoped Pointwise

universe u v u' v' u'' v'' w

variable {T : Type u} {E : Type v} {T' : Type u'} {E' : Type v'}
variable {T'' : Type u''} {E'' : Type v''}

@[simp] theorem ofWord_cons (a : Letter T E) (w : Word T E) :
    ofWord (a :: w) = singleton a * ofWord w :=
  Proofs.Semantics.ConcurrentTrace.ofWord_cons a w

namespace Equivalent

theorem refl (x : Word T E) : Equivalent x x := (congruence T E).refl _

theorem symm {x y : Word T E} (h : Equivalent x y) : Equivalent y x := (congruence T E).symm h

theorem trans {x y z : Word T E} (hxy : Equivalent x y) (hyz : Equivalent y z) : Equivalent x z :=
  (congruence T E).trans hxy hyz

theorem append {x x' y y' : Word T E} (hx : Equivalent x x') (hy : Equivalent y y') :
    Equivalent (x ++ y) (x' ++ y') :=
  (congruence T E).mul hx hy

/-- An independent pair may be swapped in any word context. -/
theorem swap_in_context {a b : Letter T E} (h : a.Independent b) (pre post : Word T E) :
    Equivalent (pre ++ [a, b] ++ post) (pre ++ [b, a] ++ post) :=
  ((refl pre).append ((ofWord_eq_iff [a, b] [b, a]).mp (swap h))).append (refl post)

end Equivalent

/-- Homomorphisms out of traces are determined by their values on letters. -/
theorem hom_ext {M : Type w} [Monoid M] {f g : Trace T E →* M}
    (h : ∀ a, f (singleton a) = g (singleton a)) : f = g :=
  Proofs.Semantics.ConcurrentTrace.hom_ext h

/-- Distinct letters commute exactly when they are independent. Equal letters trivially commute. -/
theorem swap_eq_iff (a b : Letter T E) :
    singleton a * singleton b = singleton b * singleton a ↔ a = b ∨ a.Independent b :=
  Proofs.Semantics.ConcurrentTrace.swap_eq_iff a b

@[simp] theorem mapTrace_singleton (f : T → T') (hf : Function.Injective f) (g : E → E')
    (a : Letter T E) : mapTrace f hf g (singleton a) = singleton (a.map f g) :=
  Proofs.Semantics.ConcurrentTrace.mapTrace_singleton f hf g a

@[simp] theorem mapTrace_ofWord (f : T → T') (hf : Function.Injective f) (g : E → E')
    (word : Word T E) : mapTrace f hf g (ofWord word) = ofWord (mapWord f g word) :=
  Proofs.Semantics.ConcurrentTrace.mapTrace_ofWord f hf g word

theorem mapTrace_id : mapTrace (E := E) (T := T) id Function.injective_id id = MonoidHom.id _ :=
  Proofs.Semantics.ConcurrentTrace.mapTrace_id

theorem mapTrace_comp (f : T → T') (hf : Function.Injective f) (g : E → E')
    (f' : T' → T'') (hf' : Function.Injective f') (g' : E' → E'') :
    (mapTrace f' hf' g').comp (mapTrace f hf g) = mapTrace (f' ∘ f) (hf'.comp hf) (g' ∘ g) :=
  Proofs.Semantics.ConcurrentTrace.mapTrace_comp f hf g f' hf' g'

theorem Equivalent.mapWord {x y : Word T E} (h : Equivalent x y)
    (f : T → T') (hf : Function.Injective f) (g : E → E') :
    Equivalent (mapWord f g x) (mapWord f g y) := by
  rw [← ofWord_eq_iff, ← mapTrace_ofWord f hf g, ← mapTrace_ofWord f hf g, (ofWord_eq_iff _ _).mpr h]

/-- On a whole alphabet with at least one event, identifying distinct thread IDs breaks
preservation of the congruence. An event and a formerly independent singleton sync witness it. -/
theorem injective_of_respects [Nonempty E] (f : T → T') (g : E → E')
    (h : ∀ ⦃x y⦄, Equivalent x y → Equivalent (mapWord f g x) (mapWord f g y)) :
    Function.Injective f :=
  Proofs.Semantics.ConcurrentTrace.injective_of_respects f g h

@[simp] theorem liftThread_of (t : T) (e : E) :
    liftThread t (FreeMonoid.of e) = singleton (Letter.event t e) :=
  Proofs.Semantics.ConcurrentTrace.liftThread_of t e

theorem liftThread_ofList (t : T) (word : List E) :
    liftThread t (FreeMonoid.ofList word) = ofWord (word.map (Letter.event t)) :=
  Proofs.Semantics.ConcurrentTrace.liftThread_ofList t word

theorem mapTrace_liftThread (f : T → T') (hf : Function.Injective f) (g : E → E') (t : T) :
    (mapTrace f hf g).comp (liftThread t) = (liftThread (f t)).comp (FreeMonoid.map g) :=
  Proofs.Semantics.ConcurrentTrace.mapTrace_liftThread f hf g t

@[simp] theorem observe_singleton [DecidableEq T] (t : T) (a : Letter T E) :
    observe t (singleton a) = observeLetter t a :=
  Proofs.Semantics.ConcurrentTrace.observe_singleton t a

@[simp] theorem syncs_singleton_event (t : T) (e : E) : syncs (singleton (Letter.event t e)) = 1 :=
  Proofs.Semantics.ConcurrentTrace.syncs_singleton_event t e

@[simp] theorem syncs_singleton_sync (ts : List T) :
    syncs (singleton (Letter.sync (Event := E) ts)) = FreeMonoid.of ts :=
  Proofs.Semantics.ConcurrentTrace.syncs_singleton_sync ts

theorem observe_liftThread [DecidableEq T] (t : T) :
    (observe t).comp (liftThread (E := E) t) = FreeMonoid.map LocalLetter.event :=
  Proofs.Semantics.ConcurrentTrace.observe_liftThread t

/-- Lifting into a thread is split by the event-only observation at that thread. -/
theorem events_liftThread [DecidableEq T] (t : T) :
    (events t).comp (liftThread (E := E) t) = MonoidHom.id _ :=
  Proofs.Semantics.ConcurrentTrace.events_liftThread t

theorem observe_mapTrace [DecidableEq T] [DecidableEq T']
    (f : T → T') (hf : Function.Injective f) (g : E → E') (t : T) :
    (observe (f t)).comp (mapTrace f hf g) =
      (FreeMonoid.map (LocalLetter.map f g)).comp (observe t) :=
  Proofs.Semantics.ConcurrentTrace.observe_mapTrace f hf g t

theorem events_mapTrace [DecidableEq T] [DecidableEq T']
    (f : T → T') (hf : Function.Injective f) (g : E → E') (t : T) :
    (events (f t)).comp (mapTrace f hf g) = (FreeMonoid.map g).comp (events t) :=
  Proofs.Semantics.ConcurrentTrace.events_mapTrace f hf g t

theorem syncs_mapTrace (f : T → T') (hf : Function.Injective f) (g : E → E') :
    syncs.comp (mapTrace f hf g) = (FreeMonoid.map (List.map f)).comp syncs :=
  Proofs.Semantics.ConcurrentTrace.syncs_mapTrace f hf g

theorem ofTraces_saturated (s : Set (Trace T E)) : Saturated (ofTraces s) :=
  Proofs.Semantics.ConcurrentTrace.ofTraces_saturated s

@[simp] theorem toTraces_ofTraces (s : Set (Trace T E)) : toTraces (ofTraces s) = s :=
  Proofs.Semantics.ConcurrentTrace.toTraces_ofTraces s

theorem mem_saturate (s : Set (Word T E)) (y : Word T E) :
    y ∈ saturate s ↔ ∃ x ∈ s, Equivalent x y :=
  Proofs.Semantics.ConcurrentTrace.mem_saturate s y

theorem saturate_eq_iff (s : Set (Word T E)) : saturate s = s ↔ Saturated s :=
  Proofs.Semantics.ConcurrentTrace.saturate_eq_iff s

theorem toTraces_subset_iff {s t : Set (Word T E)} (ht : Saturated t) :
    toTraces s ⊆ toTraces t ↔ s ⊆ t :=
  Proofs.Semantics.ConcurrentTrace.toTraces_subset_iff ht

/-- Quotient image and preimage identify saturated word languages with trace languages. -/
@[expose] def languageEquiv : {s : Set (Word T E) // Saturated s} ≃o Set (Trace T E) where
  toFun s := toTraces s.val
  invFun s := ⟨ofTraces s, ofTraces_saturated s⟩
  left_inv s := Subtype.ext ((saturate_eq_iff s.val).mpr s.property)
  right_inv := toTraces_ofTraces
  map_rel_iff' := toTraces_subset_iff (Subtype.property _)

@[simp] theorem languageEquiv_apply (s : {s : Set (Word T E) // Saturated s}) :
    languageEquiv s = toTraces s.val := rfl

@[simp] theorem languageEquiv_symm_apply (s : Set (Trace T E)) :
    (languageEquiv.symm s).val = ofTraces s := rfl

theorem concat_eq (s t : Set (Word T E)) : concat s t = ofTraces (toTraces s * toTraces t) :=
  Proofs.Semantics.ConcurrentTrace.concat_eq s t

theorem toTraces_concat (s t : Set (Word T E)) : toTraces (concat s t) = toTraces s * toTraces t :=
  Proofs.Semantics.ConcurrentTrace.toTraces_concat s t

theorem concat_assoc (r s t : Set (Word T E)) : concat (concat r s) t = concat r (concat s t) :=
  Proofs.Semantics.ConcurrentTrace.concat_assoc r s t

theorem concat_nil_left {s : Set (Word T E)} (h : Saturated s) : concat {[]} s = s :=
  Proofs.Semantics.ConcurrentTrace.concat_nil_left h

theorem concat_nil_right {s : Set (Word T E)} (h : Saturated s) : concat s {[]} = s :=
  Proofs.Semantics.ConcurrentTrace.concat_nil_right h

theorem toTraces_mapWord (f : T → T') (hf : Function.Injective f) (g : E → E') (s : Set (Word T E)) :
    toTraces (mapWord f g '' s) = mapTrace f hf g '' toTraces s :=
  Proofs.Semantics.ConcurrentTrace.toTraces_mapWord f hf g s

/-- A mapped word language can be closed after mapping to obtain all target representatives. -/
theorem saturate_mapWord_ofTraces (f : T → T') (hf : Function.Injective f) (g : E → E')
    (s : Set (Trace T E)) :
    saturate (mapWord f g '' ofTraces s) = ofTraces (mapTrace f hf g '' s) := by
  rw [saturate, toTraces_mapWord f hf g, toTraces_ofTraces]

end Silmaril.Semantics.ConcurrentTrace
