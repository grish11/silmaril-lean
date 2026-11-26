module

public import Silmaril.Semantics.ThreadTrace.Defs
import Silmaril.Proofs.Semantics.ThreadTrace.Monads

public section

namespace Silmaril.Proofs.Semantics.ThreadTrace

open Silmaril.ThreadTrace

universe u

variable {T W V A B : Type u} [Monoid W] [Monoid V] (q : W →* V)

theorem memSaturate (x : Alloc T W A) (t : T) (used final : Set T) (a : A) (w : W) :
    ((a, final), w) ∈ (Alloc.saturate q x).run t used ↔
      ∃ w', ((a, final), w') ∈ x.run t used ∧ q w' = q w :=
  memMapOutput q x t used final a (q w)

theorem mapSaturate (x : Alloc T W A) :
    Alloc.mapOutput q (Alloc.saturate q x) = Alloc.mapOutput q x := by
  apply allocExt
  intro t used
  ext ⟨⟨a, final⟩, v⟩
  simp only [memMapOutput, memSaturate]
  exact ⟨fun ⟨w, ⟨w', hw', he⟩, hv⟩ => ⟨w', hw', he.trans hv⟩,
    fun ⟨w, hw, hv⟩ => ⟨w, ⟨w, hw, rfl⟩, hv⟩⟩

theorem saturateIdem (x : Alloc T W A) :
    Alloc.saturate q (Alloc.saturate q x) = Alloc.saturate q x :=
  congrArg (Alloc.represent q) (mapSaturate q x)

theorem mapRepresent (hq : Function.Surjective q) (x : Alloc T V A) :
    Alloc.mapOutput q (Alloc.represent q x) = x := by
  apply allocExt
  intro t used
  ext ⟨⟨a, final⟩, v⟩
  rw [memMapOutput]
  change (∃ w, ((a, final), q w) ∈ x.run t used ∧ q w = v) ↔ ((a, final), v) ∈ x.run t used
  exact ⟨fun ⟨_, hw, hv⟩ => hv ▸ hw, fun hv => by obtain ⟨w, rfl⟩ := hq v; exact ⟨w, hv, rfl⟩⟩

theorem saturateRepresent (x : Alloc T V A) :
    Alloc.saturate q (Alloc.represent q x) = Alloc.represent q x := by
  apply allocExt
  intro t used
  ext ⟨⟨a, final⟩, w⟩
  rw [memSaturate]
  change (∃ w', ((a, final), q w') ∈ x.run t used ∧ q w' = q w) ↔ ((a, final), q w) ∈ x.run t used
  exact ⟨fun ⟨_, hw, he⟩ => he ▸ hw, fun hw => ⟨w, hw, rfl⟩⟩

theorem saturateRespectsUsed {resultSupport : A → Set T} {outputSupport : W → Set T}
    (hSupport : ∀ w w', q w = q w' → outputSupport w = outputSupport w')
    {x : Alloc T W A} (hx : x.RespectsUsed resultSupport outputSupport) :
    (Alloc.saturate q x).RespectsUsed resultSupport outputSupport := by
  intro t used a final w ht hw
  obtain ⟨w', hw', he⟩ := (memSaturate q x t used final a w).mp hw
  rw [← hSupport w' w he]
  exact hx ht hw'

theorem projectInjective : Function.Injective (Complete.project (T := T) (A := A) q) := by
  intro x y h
  apply Subtype.ext
  exact x.2.symm.trans ((congrArg (Alloc.represent q) h).trans y.2)

@[expose, instance_reducible] def completeMonad (T : Type u) : Monad (Complete T q) where
  pure a := ⟨Alloc.saturate q (pure a), saturateIdem q _⟩
  bind x k := ⟨Alloc.saturate q (x.1 >>= fun a => (k a).1), saturateIdem q _⟩

local instance : Monad (Complete T q) := completeMonad q T

theorem completePureVal (a : A) : (pure a : Complete T q A).1 = Alloc.saturate q (pure a) := rfl

theorem completeBindVal (x : Complete T q A) (k : A → Complete T q B) :
    (x >>= k).1 = Alloc.saturate q (x.1 >>= fun a => (k a).1) := rfl

theorem projectPure (a : A) : Complete.project q (pure a : Complete T q A) = pure a :=
  (mapSaturate q _).trans (allocMapPure q a)

theorem projectBind (x : Complete T q A) (k : A → Complete T q B) :
    Complete.project q (x >>= k) = Complete.project q x >>= fun a => Complete.project q (k a) :=
  (mapSaturate q _).trans (allocMapBind q _ _)

theorem completeLawful (T : Type u) : LawfulMonad (Complete T q) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · intro A x
    apply projectInjective q
    change Complete.project q (x >>= fun a => pure a) = Complete.project q x
    simp only [projectBind, projectPure, bind_pure]
  · intro A B a k
    apply projectInjective q
    simp only [projectBind, projectPure, pure_bind]
  · intro A B C x k f
    apply projectInjective q
    simp only [projectBind, bind_assoc]

end Silmaril.Proofs.Semantics.ThreadTrace
