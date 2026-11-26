module

public import Silmaril.Semantics.ConcurrentTrace.EventSync.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.EventSync.Comparison

public section

namespace Silmaril.Semantics.ConcurrentTrace.EventSync

universe u v u' v' w

variable {T : Type u} {E : Type v} {T' : Type u'} {E' : Type v'} {R S : Type w}

@[simp] theorem length_ofWord (word : Word T E) :
    (lengthHom (ofWord word)).toAdd = word.length :=
  Proofs.Semantics.ConcurrentTrace.EventSync.length_ofWord word

/-- Finite traces are ordered by extension on the right. -/
instance : PartialOrder (Trace T E) where
  le := (· ∣ ·)
  le_refl := dvd_refl
  le_trans := fun _ _ _ => dvd_trans
  le_antisymm := by
    intro _ _
    exact Proofs.Semantics.ConcurrentTrace.EventSync.dvd_antisymm

theorem le_iff_dvd (x y : Trace T E) : x ≤ y ↔ x ∣ y := Iff.rfl

/-- A proper extension can only add letters. -/
@[expose] def lengthOrder : Trace T E →o Nat where
  toFun trace := (lengthHom trace).toAdd
  monotone' := by
    rintro x _ ⟨z, rfl⟩
    simpa only [map_mul, toAdd_mul] using
      Nat.le_add_right (lengthHom x).toAdd (lengthHom z).toAdd

/-- Interpret finite prefixes using the concrete event/sync trace quotient. -/
@[expose] def wordMap : Ideals.WordMap (Letter T E) (Trace T E) where
  toFun := ofWord
  preservesPrefix := by
    rintro w _ ⟨tail, rfl⟩
    exact ⟨ofWord tail, ofWord_append w tail⟩

/-- An ideal-prefix trace of the event/sync alphabet, retaining optional completion. -/
abbrev PrefixTrace (T : Type u) (E : Type v) (R : Type w) :=
  Ideals.Trace (wordMap (T := T) (E := E)) R

/-- On finite computations the observation is the principal ideal of the finite class. -/
@[expose] def includeFinite (trace : Trace T E) (result : Option R) : PrefixTrace T E R :=
  Quotient.liftOn trace
    (fun w => Ideals.Trace.ofSequence wordMap (.finite w.toList result))
    (fun x y h => (Ideals.Trace.ofSequence_finite_eq_iff wordMap x.toList y.toList result result).2
      ⟨(congruence T E).eq.mpr h, rfl⟩)

@[simp] theorem includeFinite_ofWord (word : Word T E) (result : Option R) :
    includeFinite (ofWord word) result = Ideals.Trace.ofSequence wordMap (.finite word result) :=
  rfl

@[simp] theorem observe_includeFinite (trace : Trace T E) (result : Option R) :
    (includeFinite trace result).observe = (Order.Ideal.principal trace, result) := by
  obtain ⟨word, rfl⟩ := ofWord_surjective trace
  rw [includeFinite_ofWord]
  exact Prod.ext (Ideals.prefixIdeal_finite wordMap word result) (PartialSequence.completion_finite _ _)

theorem includeFinite_injective :
    Function.Injective (fun p : Trace T E × Option R => includeFinite p.1 p.2) := by
  rintro ⟨x, r⟩ ⟨y, s⟩ h
  obtain ⟨w, rfl⟩ := ofWord_surjective x
  obtain ⟨v, rfl⟩ := ofWord_surjective y
  obtain ⟨hw, hr⟩ := (Ideals.Trace.ofSequence_finite_eq_iff wordMap w v r s).1 h
  exact Prod.ext hw hr

/-- An injective thread relabelling and arbitrary payload map preserve extension. -/
@[expose] def mapOrder (f : T → T') (hf : Function.Injective f) (g : E → E') :
    Trace T E →o Trace T' E' where
  toFun := mapTrace f hf g
  monotone' := by
    rintro x y ⟨z, rfl⟩
    exact ⟨mapTrace f hf g z, map_mul _ _ _⟩

/-- Relabel an ideal-prefix trace in both its observations and its result. -/
@[expose] def mapPrefix (f : T → T') (hf : Function.Injective f) (g : E → E') (r : R → S) :
    PrefixTrace T E R → PrefixTrace T' E' S :=
  Ideals.Trace.map wordMap wordMap (Letter.map f g) r (mapOrder f hf g)
    (fun word => (mapTrace_ofWord f hf g word).symm)

theorem observe_mapPrefix (f : T → T') (hf : Function.Injective f) (g : E → E') (r : R → S)
    (trace : PrefixTrace T E R) :
    (mapPrefix f hf g r trace).observe =
      (Ideals.lowerImage (mapOrder f hf g) trace.observe.1, trace.observe.2.map r) :=
  Ideals.Trace.observe_map _ _ _ _ _ _ trace

theorem mapPrefix_includeFinite (f : T → T') (hf : Function.Injective f)
    (g : E → E') (r : R → S) (trace : Trace T E) (result : Option R) :
    mapPrefix f hf g r (includeFinite trace result) =
      includeFinite (mapTrace f hf g trace) (result.map r) := by
  obtain ⟨word, rfl⟩ := ofWord_surjective trace
  rw [mapTrace_ofWord, includeFinite_ofWord, includeFinite_ofWord]
  cases result <;> rfl

section Threaded

variable {Thread Event A B : Type u}

/-- Quotienting the output of a pure computation leaves it pure. -/
theorem quotientOutput_pure (a : A) :
    ThreadTrace.Alloc.mapOutput quotientOutput
      (pure a : ThreadTrace.Alloc Thread (FreeMonoid (Letter Thread Event)) A) =
        (pure a : Alloc Thread Event A) :=
  ThreadTrace.Alloc.mapOutput_pure quotientOutput a

/-- Quotienting finite output commutes with branch-local sequencing. -/
theorem quotientOutput_bind
    (x : ThreadTrace.Alloc Thread (FreeMonoid (Letter Thread Event)) A)
    (k : A → ThreadTrace.Alloc Thread (FreeMonoid (Letter Thread Event)) B) :
    ThreadTrace.Alloc.mapOutput quotientOutput (x >>= k) =
      ThreadTrace.Alloc.mapOutput quotientOutput x >>= fun a =>
        ThreadTrace.Alloc.mapOutput quotientOutput (k a) :=
  ThreadTrace.Alloc.mapOutput_bind quotientOutput x k

/-- Class-complete raw computations and computations with finite trace output agree. -/
@[expose] def completeEquiv : Complete Thread Event A ≃ Alloc Thread Event A :=
  ThreadTrace.Complete.equiv quotientOutput (by exact Con.mk'_surjective)

/-- Quotienting raw output and relabelling its letters commute. The current thread and
the used-name state are held fixed along this output-only map. -/
theorem alloc_mapTrace {Thread' Event' : Type u}
    (f : Thread → Thread') (hf : Function.Injective f) (g : Event → Event')
    (x : ThreadTrace.Alloc Thread (FreeMonoid (Letter Thread Event)) A) :
    ThreadTrace.Alloc.mapOutput (mapTrace f hf g) (ThreadTrace.Alloc.mapOutput quotientOutput x) =
      ThreadTrace.Alloc.mapOutput quotientOutput
        (ThreadTrace.Alloc.mapOutput (FreeMonoid.map (Letter.map f g)) x) :=
  Proofs.Semantics.ConcurrentTrace.EventSync.alloc_mapTrace f hf g x

/-- Each completed raw branch gives the same observation via the direct prefix quotient
and via the finite trace quotient, retaining both its result and final used set. -/
theorem includeFinite_branch (branch : ThreadTrace.Branch Thread (FreeMonoid (Letter Thread Event)) A) :
    includeFinite (quotientOutput branch.2) (some branch.1) =
      Ideals.Trace.ofSequence wordMap (.done branch.2.toList branch.1) :=
  includeFinite_ofWord branch.2.toList (some branch.1)

end Threaded
end Silmaril.Semantics.ConcurrentTrace.EventSync
