module

public import Silmaril.Semantics.ConcurrentTrace.Defs

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace

open Silmaril.Semantics.ConcurrentTrace
open scoped Pointwise

universe u v u' v' u'' v'' w

variable {T : Type u} {E : Type v} {T' : Type u'} {E' : Type v'}
variable {T'' : Type u''} {E'' : Type v''}

@[simp] theorem ofWord_cons (a : Letter T E) (w : Word T E) :
    ofWord (a :: w) = singleton a * ofWord w :=
  ofWord_append [a] w

/-- Homomorphisms out of traces are determined by their values on letters. -/
theorem hom_ext {M : Type w} [Monoid M] {f g : Trace T E →* M}
    (h : ∀ a, f (singleton a) = g (singleton a)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨word, rfl⟩ := ofWord_surjective x
  induction word with
  | nil => simp
  | cons a word ih => simp [ofWord_cons, h a, ih]

@[simp] theorem mapTrace_singleton (f : T → T') (hf : Function.Injective f) (g : E → E')
    (a : Letter T E) : mapTrace f hf g (singleton a) = singleton (a.map f g) :=
  lift_singleton _ _ _

theorem mapTrace_ofWord (f : T → T') (hf : Function.Injective f) (g : E → E')
    (word : Word T E) : mapTrace f hf g (ofWord word) = ofWord (mapWord f g word) := by
  induction word with
  | nil => simp [mapWord]
  | cons a word ih =>
    rw [ofWord_cons, map_mul, mapTrace_singleton, ih]
    exact (ofWord_cons (a.map f g) (mapWord f g word)).symm

theorem mapTrace_id : mapTrace (E := E) (T := T) id Function.injective_id id = MonoidHom.id _ := by
  apply hom_ext
  intro a
  cases a <;> simp [Letter.map]

theorem mapTrace_comp (f : T → T') (hf : Function.Injective f) (g : E → E')
    (f' : T' → T'') (hf' : Function.Injective f') (g' : E' → E'') :
    (mapTrace f' hf' g').comp (mapTrace f hf g) = mapTrace (f' ∘ f) (hf'.comp hf) (g' ∘ g) := by
  apply hom_ext
  intro a
  cases a <;> simp [Letter.map, List.map_map]

@[simp] theorem liftThread_of (t : T) (e : E) :
    liftThread t (FreeMonoid.of e) = singleton (Letter.event t e) :=
  FreeMonoid.lift_eval_of _ _

theorem liftThread_ofList (t : T) (word : List E) :
    liftThread t (FreeMonoid.ofList word) = ofWord (word.map (Letter.event t)) := by
  induction word with
  | nil => simp
  | cons e word ih => rw [FreeMonoid.ofList_cons, map_mul, liftThread_of, ih, List.map_cons, ofWord_cons]

theorem mapTrace_liftThread (f : T → T') (hf : Function.Injective f) (g : E → E') (t : T) :
    (mapTrace f hf g).comp (liftThread t) = (liftThread (f t)).comp (FreeMonoid.map g) := by
  apply FreeMonoid.hom_eq
  intro e
  simp [Letter.map]

@[simp] theorem observe_singleton [DecidableEq T] (t : T) (a : Letter T E) :
    observe t (singleton a) = observeLetter t a :=
  lift_singleton _ _ _

@[simp] theorem syncs_singleton_event (t : T) (e : E) :
    syncs (singleton (.event t e)) = 1 :=
  lift_singleton _ _ _

@[simp] theorem syncs_singleton_sync (ts : List T) :
    syncs (singleton (Letter.sync (Event := E) ts)) = FreeMonoid.of ts :=
  lift_singleton _ _ _

theorem observe_liftThread [DecidableEq T] (t : T) :
    (observe t).comp (liftThread (E := E) t) = FreeMonoid.map LocalLetter.event := by
  apply FreeMonoid.hom_eq
  intro e
  simp [observeLetter]

theorem events_liftThread [DecidableEq T] (t : T) :
    (events t).comp (liftThread (E := E) t) = MonoidHom.id _ := by
  apply FreeMonoid.hom_eq
  intro e
  simp [events, observeLetter, FreeMonoid.lift_eval_of]

theorem observe_mapTrace [DecidableEq T] [DecidableEq T']
    (f : T → T') (hf : Function.Injective f) (g : E → E') (t : T) :
    (observe (f t)).comp (mapTrace f hf g) =
      (FreeMonoid.map (LocalLetter.map f g)).comp (observe t) := by
  apply hom_ext
  intro a
  cases a with
  | event u e =>
    by_cases h : u = t
    · simp [Letter.map, observeLetter, LocalLetter.map, h]
    · have hm : f u ≠ f t := hf.ne h
      simp [Letter.map, observeLetter, h, hm]
  | sync ts =>
    have hm : f t ∈ ts.map f ↔ t ∈ ts := List.mem_map_of_injective hf
    by_cases h : t ∈ ts <;> simp [Letter.map, observeLetter, LocalLetter.map, hm, h]

theorem events_mapTrace [DecidableEq T] [DecidableEq T']
    (f : T → T') (hf : Function.Injective f) (g : E → E') (t : T) :
    (events (f t)).comp (mapTrace f hf g) = (FreeMonoid.map g).comp (events t) := by
  apply hom_ext
  intro a
  have h : observe (f t) (mapTrace f hf g (singleton a)) =
      FreeMonoid.map (LocalLetter.map f g) (observeLetter t a) := by
    simpa only [MonoidHom.comp_apply, observe_singleton] using
      DFunLike.congr_fun (observe_mapTrace f hf g t) (singleton a)
  simp only [events, MonoidHom.comp_apply, h, observe_singleton]
  cases a with
  | event u e => by_cases hut : u = t <;>
      simp [observeLetter, hut, LocalLetter.map, FreeMonoid.lift_eval_of]
  | sync ts => by_cases ht : t ∈ ts <;>
      simp [observeLetter, ht, LocalLetter.map, FreeMonoid.lift_eval_of]

theorem syncs_mapTrace (f : T → T') (hf : Function.Injective f) (g : E → E') :
    syncs.comp (mapTrace f hf g) = (FreeMonoid.map (List.map f)).comp syncs := by
  apply hom_ext
  intro a
  cases a <;> simp [Letter.map]

/-- Distinct letters can swap in a two-letter trace exactly when independent. -/
theorem swap_eq_iff (a b : Letter T E) :
    singleton a * singleton b = singleton b * singleton a ↔ a = b ∨ a.Independent b := by
  classical
  refine ⟨?_, fun h => h.elim (fun h => h ▸ rfl) swap⟩
  intro h
  cases a with
  | event t e =>
    cases b with
    | event u f =>
      by_cases htu : t = u
      · subst u
        left
        have hobs := congrArg (fun x => (observe t x).toList) h
        simp [map_mul, observeLetter] at hobs
        exact congrArg (Letter.event t) hobs.1
      · exact Or.inr (.events htu)
    | sync ts =>
      right
      by_cases ht : t ∈ ts
      · have hobs := congrArg (fun x => (observe t x).toList) h
        simp [map_mul, observeLetter, ht] at hobs
      · exact .eventSync ht
  | sync ts =>
    cases b with
    | event t e =>
      right
      by_cases ht : t ∈ ts
      · have hobs := congrArg (fun x => (observe t x).toList) h
        simp [map_mul, observeLetter, ht] at hobs
      · exact .syncEvent ht
    | sync us =>
      left
      have hobs := congrArg (fun x => (syncs x).toList) h
      simp [map_mul] at hobs
      exact congrArg Letter.sync hobs.1

theorem injective_of_respects [Nonempty E] (f : T → T') (g : E → E')
    (h : ∀ ⦃x y⦄, Equivalent x y → Equivalent (mapWord f g x) (mapWord f g y)) :
    Function.Injective f := by
  intro t u heq
  by_contra hne
  obtain ⟨e⟩ := ‹Nonempty E›
  have hs := swap (Letter.Independent.eventSync (e := e) (ts := [u]) (by simpa using hne))
  have hraw : Equivalent [.event t e, .sync [u]] [.sync [u], .event t e] :=
    (ofWord_eq_iff _ _).mp hs
  have hm := (ofWord_eq_iff _ _).mpr (h hraw)
  have hpair := (swap_eq_iff (.event (f t) (g e)) (.sync [f u])).mp hm
  rcases hpair with hbad | hbad
  · cases hbad
  · cases hbad with
    | eventSync hbad => exact hbad (by simp [heq])

theorem ofTraces_saturated (s : Set (Trace T E)) : Saturated (ofTraces s) := by
  intro x y hx hxy
  change ofWord y ∈ s
  rw [← (ofWord_eq_iff _ _).mpr hxy]
  exact hx

theorem toTraces_ofTraces (s : Set (Trace T E)) : toTraces (ofTraces s) = s :=
  Set.image_preimage_eq s ofWord_surjective

theorem mem_saturate (s : Set (Word T E)) (y : Word T E) :
    y ∈ saturate s ↔ ∃ x ∈ s, Equivalent x y :=
  exists_congr fun x => and_congr_right fun _ => ofWord_eq_iff x y

theorem saturate_eq_iff (s : Set (Word T E)) : saturate s = s ↔ Saturated s := by
  constructor
  · intro h
    rw [← h]
    exact ofTraces_saturated _
  · intro h
    ext y
    exact (mem_saturate s y).trans
      ⟨fun ⟨_, hx, hxy⟩ => h hx hxy, fun hy => ⟨y, hy, (ofWord_eq_iff _ _).mp rfl⟩⟩

theorem toTraces_subset_iff {s t : Set (Word T E)} (ht : Saturated t) :
    toTraces s ⊆ toTraces t ↔ s ⊆ t := by
  refine ⟨fun h x hx => ?_, Set.image_mono⟩
  have hmem : x ∈ saturate t := h ⟨x, hx, rfl⟩
  rwa [(saturate_eq_iff _).mpr ht] at hmem

theorem concat_eq (s t : Set (Word T E)) : concat s t = ofTraces (toTraces s * toTraces t) := by
  apply congrArg ofTraces
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact Set.mem_mul.mpr ⟨ofWord x, ⟨x, hx, rfl⟩, ofWord y, ⟨y, hy, rfl⟩, (ofWord_append x y).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x ++ y, ⟨x, hx, y, hy, rfl⟩, ofWord_append x y⟩

theorem toTraces_concat (s t : Set (Word T E)) : toTraces (concat s t) = toTraces s * toTraces t := by
  rw [concat_eq, toTraces_ofTraces]

theorem concat_assoc (r s t : Set (Word T E)) : concat (concat r s) t = concat r (concat s t) := by
  rw [concat_eq (concat r s), concat_eq r (concat s t), toTraces_concat, toTraces_concat, mul_assoc]

theorem concat_nil_left {s : Set (Word T E)} (h : Saturated s) : concat {[]} s = s := by
  rw [concat, Set.image2_left_identity (f := List.append) List.nil_append, (saturate_eq_iff _).mpr h]

theorem concat_nil_right {s : Set (Word T E)} (h : Saturated s) : concat s {[]} = s := by
  rw [concat, Set.image2_right_identity (f := List.append) List.append_nil, (saturate_eq_iff _).mpr h]

theorem toTraces_mapWord (f : T → T') (hf : Function.Injective f) (g : E → E') (s : Set (Word T E)) :
    toTraces (mapWord f g '' s) = mapTrace f hf g '' toTraces s := by
  simp only [toTraces, Set.image_image, mapTrace_ofWord]

end Silmaril.Proofs.Semantics.ConcurrentTrace
