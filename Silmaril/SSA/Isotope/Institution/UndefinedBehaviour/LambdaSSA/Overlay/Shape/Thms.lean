module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Laws
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Preservation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Transfers

/-! # Preservation and two native rewrite laws in shape-respecting models -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape

open Morphism.SSAIter (envOfBound)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}

/-- The positional environment agrees with exact typing at every in-scope slot. -/
theorem env_typed (M : Model.{u,v,w,x} Φ Γ) : EnvTyped M.atomType Γ (envOfBound M.raw.bound) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.env_typed M

/-- Successful evaluation of any exactly typed expression yields its declared type. -/
theorem term_eval_typed (M : Model.{u,v,w,x} Φ Γ)
    {a : Tm Φ} {A : Ty κ} {s t : M.raw.σ} {b : Value M.raw.α}
    (ha : a.HasType Γ A) (run : Semantics.Tm.Eval M.raw.instr (envOfBound M.raw.bound) a s b t) :
    ValueTyped M.atomType b A :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.term_eval_typed M ha run

/-- A successful native region transfer, including through recursive CFGs,
carries a value matching the exit label at the exact interface. -/
theorem region_eval_typed (M : Model.{u,v,w,x} Φ Γ)
    {r : LambdaSSA.Region Φ} {s t : M.raw.σ} {i : Nat} {a : Value M.raw.α}
    (hr : r.HasType Γ L) (run : Semantics.Region.Eval M.raw.instr (envOfBound M.raw.bound) r s i a t) :
    ∃ A, At L i A ∧ ValueTyped M.atomType a A :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.region_eval_typed M hr run

/-- Label substitution and feedback only bind reachable ordinary payloads of
the declared type. Every ordinary exit of the resulting overlay is typed. -/
theorem returns_typed (r : Region Φ Γ L) (M : Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    ReturnsTyped M.atomType (denote r M s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.returns_typed r M s

/-- For a common source, comparison on exactly typed continuation inputs
suffices for directed label substitution. -/
theorem lsubst_mono_typed {Γ K : List (Ty κ)} (r : Region Φ Γ L)
    (k h : (i : Fin L.length) → Region Φ (L.get i :: Γ) K)
    (M : Model.{u,v,w,x} Φ Γ) (s : M.raw.σ)
    (next : ∀ i {a} (ha : ValueTyped M.atomType a (L.get i)) t,
      denote (k i) (M.extend ha) t ≤ denote (h i) (M.extend ha) t) :
    denote (.lsubst r k) M s ≤ denote (.lsubst r h) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.lsubst_mono_typed r k h M s next

/-- The installed variable product η generator preserves the full lifted
behaviour, including final states, faults and may-divergence. -/
theorem product_eta {r t : LambdaSSA.Region Φ} (h : LambdaSSA.Region.ProductEta.Step Γ r t L)
    (M : Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    denote (.native ⟨r, h.typed.1⟩) M s = denote (.native ⟨t, h.typed.2⟩) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.product_eta h M s

/-- The constructor-valued premise of native initiality cannot be realized
in a shaped environment. -/
theorem no_model_of_empty_branchValue {a : Tm Φ} (ha : a.BranchValue Γ (.empty : Ty κ))
    (M : Model.{u,v,w,x} Φ Γ) : False :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.no_model_of_empty_branchValue ha M

/-- Soundness of the initiality generator of `SubstitutionEquiv` at its
exact constructor-valued premise. -/
theorem initial {a : Tm Φ} (ha : a.BranchValue Γ (.empty : Ty κ))
    (r t : UB.Typed (Φ := Φ) Γ L) (M : Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    denote (.native r) M s = denote (.native t) M s :=
  (no_model_of_empty_branchValue ha M).elim

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
