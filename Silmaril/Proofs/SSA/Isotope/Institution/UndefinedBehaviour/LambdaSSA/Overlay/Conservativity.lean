module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Institution.Observational

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {Γ L : List τ}

theorem observe_native (r : UB.Typed (Φ := Φ) Γ L) (M : Model.{u,w,x} Φ Γ.length) :
    observe (.native r) M = UB.observe M r := by
  ext o
  constructor
  · rintro ⟨_, x, hx, rfl⟩
    simpa only [denote, Behaviour.possible, WithTop.untopD_coe, nativeOutcomes, Set.mem_ofPred_eq] using hx
  · intro ho
    cases o with
    | ret s result s' =>
      obtain ⟨label, value⟩ := result
      have inside := r.property.scoped.eval_label_lt (ret_mem_ssaBeh.mp ho)
      exact ⟨s, .ret ⟨label, inside⟩ value s', ho, rfl⟩
    | fault s s' => exact ⟨s, .fault s', ho, rfl⟩
    | diverge s => exact ⟨s, .diverge, ho, rfl⟩

theorem native_observe_subset_iff (M : Model.{u,w,x} Φ Γ.length)
    (r t : UB.Typed (Φ := Φ) Γ L) :
    UB.observe M r ⊆ UB.observe M t ↔ ∀ s, denote (.native r) M s ≤ denote (.native t) M s := by
  constructor
  · intro h s
    exact WithTop.coe_le_coe.mpr (fun _ hx => h hx)
  · intro h o ho
    rw [← observe_native r M] at ho
    rw [← observe_native t M]
    obtain ⟨s, x, hx, rfl⟩ := ho
    exact ⟨s, x, WithTop.coe_le_coe.mp (h s) hx, rfl⟩

theorem native_refines_iff (r t : UB.Typed (Φ := Φ) Γ L) :
    Refines.{u,v,w,x} (.native r) (.native t) ↔ UB.Refines.{u,v,w,x} r t := by
  rw [UB.refines_iff]
  exact forall_congr' fun M => (native_observe_subset_iff M r t).symm

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay
