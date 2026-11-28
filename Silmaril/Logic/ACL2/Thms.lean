module

public import Silmaril.Logic.ACL2.Defs
import Silmaril.Proofs.Logic.ACL2.Core

@[expose] public section

namespace Silmaril.Logic.ACL2

open CategoryTheory Institution Institution.Metatheory

variable {S T U : Signature} {n m : Nat}

@[simp] theorem Term.map_id (t : Term S n) : t.map (𝟙 S) = t :=
  Proofs.Logic.ACL2.map_id t

theorem Term.map_comp (σ : S ⟶ T) (τ : T ⟶ U) (t : Term S n) :
    t.map (σ ≫ τ) = (t.map σ).map τ := Proofs.Logic.ACL2.map_comp σ τ t

theorem Term.map_subst (σ : S ⟶ T) (s : Fin n → Term S m) (t : Term S n) :
    (t.subst s).map σ = (t.map σ).subst (fun i => (s i).map σ) :=
  Proofs.Logic.ACL2.map_subst σ s t

theorem Term.eval_map (σ : S ⟶ T) (M : Model T) (env : Fin n → M.primitives.Value) (t : Term S n) :
    (t.map σ).eval M env = t.eval (M.reduct σ) env := Proofs.Logic.ACL2.eval_map σ M env t

theorem Term.eval_subst (M : Model S) (env : Fin m → M.primitives.Value) (s : Fin n → Term S m)
    (t : Term S n) : (t.subst s).eval M env = t.eval M (fun i => (s i).eval M env) :=
  Proofs.Logic.ACL2.eval_subst M env s t

@[simp] theorem Sentence.map_id (p : Sentence S) : p.map (𝟙 S) = p := by
  cases p
  simp [Sentence.map]

theorem Sentence.map_comp (σ : S ⟶ T) (τ : T ⟶ U) (p : Sentence S) :
    p.map (σ ≫ τ) = (p.map σ).map τ := by
  cases p
  simp [Sentence.map, Term.map_comp]

theorem Sentence.holds_map (σ : S ⟶ T) (M : Model T) (p : Sentence S) :
    (p.map σ).Holds M ↔ p.Holds (M.reduct σ) := by
  simp only [Sentence.Holds, Sentence.map, Term.eval_map]
  rfl

theorem Sentence.holds_eq (M : Model S) (x y : Term S n) :
    (Sentence.eq x y).Holds M ↔ ∀ env, x.eval M env = y.eval M env :=
  Proofs.Logic.ACL2.holds_eq M x y

theorem Derives.bind {Γ Δ : Set (Sentence S)} {p : Sentence S}
    (h : Derives Γ p) (f : ∀ q ∈ Γ, Derives Δ q) : Derives Δ p :=
  Proofs.Logic.ACL2.bind h f

theorem Derives.weaken {Γ Δ : Set (Sentence S)} {p : Sentence S}
    (h : Derives Γ p) (sub : Γ ⊆ Δ) : Derives Δ p := h.bind fun _ hq => .hyp (sub hq)

theorem Derives.map (σ : S ⟶ T) {Γ : Set (Sentence S)} {p : Sentence S}
    (h : Derives Γ p) : Derives (Sentence.map σ '' Γ) (p.map σ) :=
  Proofs.Logic.ACL2.map_derives σ h

theorem Derives.sound {Γ : Set (Sentence S)} {p : Sentence S} (h : Derives Γ p) (M : Model S)
    (hΓ : ∀ q ∈ Γ, q.Holds M) : p.Holds M := Proofs.Logic.ACL2.sound h M hΓ

/-- The corridor along a named signature inclusion. -/
def corridor (σ : S ⟶ T) : room S ⟶ room T :=
  ⟨Sentence.map σ, Model.functor (Model.reduct σ),
    fun M p => p.holds_map σ M⟩

theorem corridor_id (S : Signature) : corridor (𝟙 S) = 𝟙 (room S) :=
  Room.hom_ext (funext Sentence.map_id) (Proofs.Logic.ACL2.reduct_id S)

theorem corridor_comp (σ : S ⟶ T) (τ : T ⟶ U) :
    corridor (σ ≫ τ) = corridor σ ≫ corridor τ :=
  Room.hom_ext (funext (Sentence.map_comp σ τ)) (Proofs.Logic.ACL2.reduct_comp σ τ)

def institution : Signature ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

def logic : LogicalSystem Signature where
  I := institution
  Derives _ := Derives
  refl _ p := .hyp (Set.mem_singleton p)
  mono := fun _ {_ _ _} sub h => Derives.weaken h sub
  trans := fun _ {_ _ _} cut h => Derives.bind h fun p hp => hp.elim Derives.hyp (cut p)
  map_derives := fun {_ _} σ {_ _} h => Derives.map σ h

/-- The ordinary institution of the ACL2 fragment. -/
def inst : Inst.{0, 0, 0, 0, 1} := logic.toInst

theorem logic_sound : logic.Sound := fun _ _ _ h M hΓ => h.sound M hΓ

end Silmaril.Logic.ACL2
