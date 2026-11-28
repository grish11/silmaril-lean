module

public import Silmaril.Semantics.NondeterministicTrace.Maps.Thms

public section

namespace Silmaril.Proofs.Semantics.NondeterministicTrace.Tagged

open Silmaril.Elgot
open Silmaril.Semantics.NondeterministicTrace Tagged

universe u

variable {W V T A B : Type u}

theorem outcomes_injective : Function.Injective (outcomes : Tagged W T A → Set (Except T A × W)) :=
  fun {_ _} h => _root_.ExceptT.ext (Finite.outcomes_injective h)

variable [Monoid W]

theorem mem_bind {p : Tagged W T A} {k : A → Tagged W T B} {r : Except T B} {w : W} :
    (r, w) ∈ outcomes (p >>= k) ↔
      (∃ t, r = .error t ∧ (.error t, w) ∈ p.outcomes) ∨
      ∃ a u v, (.ok a, u) ∈ p.outcomes ∧ (r, v) ∈ (k a).outcomes ∧ u * v = w := by
  change (r, w) ∈ Finite.outcomes ((p >>= k).run) ↔ _
  rw [_root_.ExceptT.run_bind, Finite.mem_bind]
  constructor
  · rintro ⟨s, u, v, hp, hk, he⟩
    cases s with
    | error t =>
      have heq : (r, v) = (.error t, 1) := hk
      cases heq
      rw [mul_one] at he
      exact Or.inl ⟨t, rfl, he ▸ hp⟩
    | ok a => exact Or.inr ⟨a, u, v, hp, hk, he⟩
  · rintro (⟨t, rfl, hp⟩ | ⟨a, u, v, hp, hk, he⟩)
    · exact ⟨.error t, w, 1, hp, rfl, mul_one _⟩
    · exact ⟨.ok a, u, v, hp, hk, he⟩

theorem unfold_eq_bind (f : A → Tagged W T (B ⊕ A)) (k : A → Set (Except T B × W)) (a : A) :
    Finite.unfoldLoop (Elgot.ExceptT.body f) k a =
      outcomes (f a >>= Sum.elim pure (fun next => ofOutcomes (k next))) := by
  rw [Finite.unfold_eq_bind]
  change Finite.outcomes (Elgot.ExceptT.body f a >>= _) = Finite.outcomes ((f a >>= _).run)
  congr 1
  simp only [Elgot.ExceptT.body, _root_.ExceptT.run_bind, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  rintro (tag | s)
  · rfl
  · cases s <;> rfl

theorem outcomes_includeResults (p : Finite W A) :
    outcomes (includeResults p : Tagged W T A) =
      Prod.map (Except.ok : A → Except T A) id '' p.outcomes :=
  Finite.outcomes_bind_pure p Except.ok

theorem includeResults_injective :
    Function.Injective (includeResults : Finite W A → Tagged W T A) := by
  intro p q h
  apply Finite.outcomes_injective
  have hi : Function.Injective (Except.ok : A → Except T A) := fun _ _ h => Except.ok.inj h
  apply Set.image_injective.mpr (hi.prodMap Function.injective_id)
  simpa only [outcomes_includeResults] using congrArg outcomes h

theorem includeResults_pure (a : A) : includeResults (pure a) = (pure a : Tagged W T A) := by
  apply _root_.ExceptT.ext
  simp only [includeResults, _root_.ExceptT.run_mk, _root_.ExceptT.run_pure, pure_bind,
    Function.comp_apply]

theorem includeResults_bind (p : Finite W A) (k : A → Finite W B) :
    includeResults (p >>= k) = (includeResults p >>= fun a => includeResults (k a) : Tagged W T B) := by
  apply _root_.ExceptT.ext
  simp only [includeResults, _root_.ExceptT.run_mk, _root_.ExceptT.run_bind,
    bind_assoc, Function.comp_apply, pure_bind]

theorem includeResults_iter (f : A → Finite W (B ⊕ A)) (a : A) :
    includeResults (iter f a) = (iter (fun next => includeResults (f next)) a : Tagged W T B) := by
  have eq : Elgot.ExceptT.body (fun next => includeResults (f next)) =
      mapReturn f (pure ∘ (Except.ok : B → Except T B)) := by
    funext x
    simp only [Elgot.ExceptT.body, includeResults, _root_.ExceptT.run_mk,
      bind_assoc, Function.comp_apply, pure_bind, mapReturn]
    apply bind_congr
    intro s
    cases s <;> simp [Elgot.ExceptT.distribute]
  apply _root_.ExceptT.ext
  rw [Elgot.ExceptT.run_iter, eq]
  exact congrFun (LawfulElgotMonad.naturality f (pure ∘ Except.ok)) a

variable [Monoid V] (h : W →* V)

theorem mapLog_pure (a : A) : mapLog h (pure a) = (pure a : Tagged V T A) := by
  apply _root_.ExceptT.ext
  exact Finite.mapLog_pure h (Except.ok a : Except T A)

theorem mapLog_bind (p : Tagged W T A) (k : A → Tagged W T B) :
    mapLog h (p >>= k) = mapLog h p >>= fun a => mapLog h (k a) := by
  apply _root_.ExceptT.ext
  simp only [mapLog, _root_.ExceptT.run_mk, _root_.ExceptT.run_bind, Finite.mapLog_bind]
  apply bind_congr
  rintro (tag | value)
  · exact Finite.mapLog_pure h (Except.error tag : Except T B)
  · rfl

theorem mapLog_iter (f : A → Tagged W T (B ⊕ A)) (a : A) :
    mapLog h (iter f a) = iter (fun next => mapLog h (f next)) a := by
  have eq : (fun x => Finite.mapLog h (Elgot.ExceptT.body f x)) =
      Elgot.ExceptT.body (fun x => mapLog h (f x)) := by
    funext x
    simp only [Elgot.ExceptT.body, mapLog, _root_.ExceptT.run_mk, Finite.mapLog_bind,
      Function.comp_apply, Finite.mapLog_pure]
    rfl
  apply _root_.ExceptT.ext
  simp only [mapLog, _root_.ExceptT.run_mk, Elgot.ExceptT.run_iter, Finite.mapLog_iter]
  exact congrFun (congrArg iter eq) a

theorem mapLog_injective (hh : Function.Injective h) :
    Function.Injective (mapLog h : Tagged W T A → Tagged V T A) :=
  fun {_ _} eq => _root_.ExceptT.ext (Finite.mapLog_injective h hh (congrArg _root_.ExceptT.run eq))

theorem mapLog_surjective (hh : Function.Surjective h) :
    Function.Surjective (mapLog h : Tagged W T A → Tagged V T A) := by
  intro p
  obtain ⟨q, hq⟩ := Finite.mapLog_surjective h hh p.run
  exact ⟨_root_.ExceptT.mk q, _root_.ExceptT.ext hq⟩

end Silmaril.Proofs.Semantics.NondeterministicTrace.Tagged
