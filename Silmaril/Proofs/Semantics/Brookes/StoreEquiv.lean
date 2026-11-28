module

public import Silmaril.Semantics.Brookes.StoreEquiv.Defs
public import Silmaril.Semantics.Brookes.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.StoreEquiv

open Silmaril.Semantics.Brookes

variable {S T A B : Type*}

theorem mapStores_append (f : S → T) (left right : Trace S) :
    Trace.mapStores f (left ++ right) = Trace.mapStores f left ++ Trace.mapStores f right :=
  List.map_append

private theorem mapStores_cons (f : S → T) (s t : S) (word : Trace S) :
    Trace.mapStores f ((s, t) :: word) = (f s, f t) :: Trace.mapStores f word := rfl

theorem mapStores_inverse (e : S ≃ T) (word : Trace S) :
    Trace.mapStores e.symm (Trace.mapStores e word) = word := by
  induction word with
  | nil => rfl
  | cons pair word ih =>
    obtain ⟨s, t⟩ := pair
    simp only [mapStores_cons, Equiv.symm_apply_apply, ih]

private theorem mapStores_symm_inverse (e : S ≃ T) (word : Trace T) :
    Trace.mapStores e (Trace.mapStores e.symm word) = word := by
  simpa only [Equiv.symm_symm] using mapStores_inverse e.symm word

theorem reduces_mapStores (f : S → T) {source target : Trace S} (h : Reduces source target) :
    Reduces (Trace.mapStores f source) (Trace.mapStores f target) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih =>
    apply ih.tail
    cases step with
    | stutter pre post s =>
      simpa only [mapStores_append, mapStores_cons] using
        Rewrite.stutter (Trace.mapStores f pre) (Trace.mapStores f post) (f s)
    | mumble pre post s t u =>
      simpa only [mapStores_append, mapStores_cons] using
        Rewrite.mumble (Trace.mapStores f pre) (Trace.mapStores f post) (f s) (f t) (f u)

theorem transport_accepts_iff (e : S ≃ T) (b : Behavior S A) (word : Trace T) (result : A) :
    (b.transport e).accepts word result ↔ b.accepts (Trace.mapStores e.symm word) result := by
  constructor
  · rintro ⟨_, ⟨_, source, accepts, rfl⟩, reduces⟩
    have mapped := reduces_mapStores e.symm reduces
    rw [mapStores_inverse] at mapped
    exact b.stable accepts mapped
  · intro accepts
    apply Behavior.generate_accepts
    · rintro rfl
      exact b.nonempty accepts rfl
    · exact ⟨_, accepts, mapStores_symm_inverse e word⟩

theorem transport_atomic (e : S ≃ T) (step : S → S → A → Prop) :
    (Behavior.atomic step).transport e =
      Behavior.atomic (fun s t a => step (e.symm s) (e.symm t) a) := by
  apply Behavior.ext
  intro word result
  rw [transport_accepts_iff, Behavior.atomic_accepts_iff, Behavior.atomic_accepts_iff]
  constructor
  · rintro ⟨s, t, h, reduces⟩
    refine ⟨e s, e t, by simpa only [Equiv.symm_apply_apply], ?_⟩
    have mapped := reduces_mapStores e reduces
    rwa [mapStores_symm_inverse] at mapped
  · rintro ⟨s, t, h, reduces⟩
    exact ⟨e.symm s, e.symm t, h, reduces_mapStores e.symm reduces⟩

theorem transport_bind (e : S ≃ T) (first : Behavior S A) (next : A → Behavior S B) :
    (first.bind next).transport e =
      (first.transport e).bind (fun a => (next a).transport e) := by
  apply Behavior.ext
  intro word result
  rw [transport_accepts_iff, Behavior.bind_accepts_iff, Behavior.bind_accepts_iff]
  simp only [transport_accepts_iff]
  constructor
  · rintro ⟨left, right, reply, run, rest, reduces⟩
    refine ⟨Trace.mapStores e left, Trace.mapStores e right, reply, ?_, ?_, ?_⟩
    · rwa [mapStores_inverse]
    · rwa [mapStores_inverse]
    · have mapped := reduces_mapStores e reduces
      rwa [mapStores_append, mapStores_symm_inverse] at mapped
  · rintro ⟨left, right, reply, run, rest, reduces⟩
    refine ⟨_, _, reply, run, rest, ?_⟩
    have mapped := reduces_mapStores e.symm reduces
    rwa [mapStores_append] at mapped

end Silmaril.Proofs.Semantics.Brookes.StoreEquiv
