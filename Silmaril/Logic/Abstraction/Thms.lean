module

public import Silmaril.Logic.Abstraction.Defs
public import Silmaril.Logic.Inst.Builders.Core.Defs
import Silmaril.Proofs.Logic.Abstraction.Core

@[expose] public section

namespace Silmaril.Logic.Abstraction

open CategoryTheory Silmaril.Logic.Institution

variable {S T U : Signature}

@[simp]
theorem Term.map_id {k : Nat} (t : Term S k) : t.map (𝟙 S) = t :=
  Proofs.Logic.Abstraction.map_id t

theorem Term.map_comp (f : S ⟶ T) (g : T ⟶ U) {k : Nat} (t : Term S k) :
    t.map (f ≫ g) = (t.map f).map g :=
  Proofs.Logic.Abstraction.map_comp f g t

/-- Evaluation commutes with shape-preserving symbol translation at every local scope. -/
theorem Term.eval_map (f : S ⟶ T) (A : Algebra T) (ν : Valuation A.Carrier)
    {k : Nat} (t : Term S k) (env : Fin k → A.Carrier) :
    (t.map f).eval A ν env = t.eval (A.reduct f) ν env :=
  Proofs.Logic.Abstraction.eval_map f A ν t env

theorem Algebra.substValuation_map (f : S ⟶ T) (A : Algebra T) (ν : Valuation A.Carrier)
    (σ : Substitution S) :
    A.substValuation ν (σ.map f) = (A.reduct f).substValuation ν σ :=
  Proofs.Logic.Abstraction.substValuation_map f A ν σ

theorem Term.eval_rename (A : Algebra S) (ν : Valuation A.Carrier)
    {k l : Nat} (t : Term S k) (ρ : Fin k → Fin l) (env : Fin l → A.Carrier) :
    (t.rename ρ).eval A ν env = t.eval A ν (env ∘ ρ) :=
  Proofs.Logic.Abstraction.eval_rename A ν t ρ env

/-- Local instantiation evaluates a template at the values of its replacement terms. -/
theorem Term.eval_instantiate (A : Algebra S) (ν : Valuation A.Carrier)
    {k l : Nat} (t : Term S k) (σ : Fin k → Term S l) (env : Fin l → A.Carrier) :
    (t.instantiate σ).eval A ν env = t.eval A ν (fun i => (σ i).eval A ν env) :=
  Proofs.Logic.Abstraction.eval_instantiate A ν t σ env

/-- The substitution/evaluation law for terms and templates (Primer, Theorem 14). -/
theorem Term.eval_subst (A : Algebra S) (ν : Valuation A.Carrier) (σ : Substitution S)
    {k : Nat} (t : Term S k) (env : Fin k → A.Carrier) :
    (t.subst σ).eval A ν env = t.eval A (A.substValuation ν σ) env :=
  Proofs.Logic.Abstraction.eval_subst A ν σ t env

@[simp]
theorem Rule.map_id (r : Rule S) : r.map (𝟙 S) = r :=
  Proofs.Logic.Abstraction.rule_map_id r

theorem Rule.map_comp (f : S ⟶ T) (g : T ⟶ U) (r : Rule S) :
    r.map (f ≫ g) = (r.map f).map g :=
  Proofs.Logic.Abstraction.rule_map_comp f g r

theorem Rule.holdsAt_map (f : S ⟶ T) (A : Algebra T) (O : LogicalOrder A.Carrier)
    (ν : Valuation A.Carrier) (r : Rule S) :
    (r.map f).HoldsAt A O ν ↔ r.HoldsAt (A.reduct f) O ν :=
  Proofs.Logic.Abstraction.holdsAt_map f A O ν r

/-- The target's admissible valuations also form a valuation space of the reduct.
A substitution over the source can be transported along the signature map. -/
def ValuationSpace.reduct (f : S ⟶ T) {A : Algebra T} (V : ValuationSpace A) :
    ValuationSpace (A.reduct f) where
  admissible := V.admissible
  nonempty := V.nonempty
  update_closed := V.update_closed
  subst_closed h σ := (A.substValuation_map f _ σ) ▸ V.subst_closed h (σ.map f)

/-- Reducts preserve the logical order and the admissible valuations. -/
def Model.reduct (f : S ⟶ T) (M : Model T) : Model S :=
  ⟨M.algebra.reduct f, M.truth, M.space.reduct f⟩

/-- The institution satisfaction condition. -/
theorem Model.satisfaction (f : S ⟶ T) (M : Model T) (r : Sentence S) :
    M.Sat (r.map f) ↔ (M.reduct f).Sat r :=
  forall_congr' fun ν => forall_congr' fun _ => Rule.holdsAt_map f M.algebra M.truth ν r

/-- The substitution/evaluation law lifts to the entire rule inequality. -/
theorem Rule.holdsAt_subst (A : Algebra S) (O : LogicalOrder A.Carrier)
    (ν : Valuation A.Carrier) (σ : Substitution S) (r : Rule S) :
    (r.subst σ).HoldsAt A O ν ↔ r.HoldsAt A O (A.substValuation ν σ) :=
  Proofs.Logic.Abstraction.holdsAt_subst A O ν σ r

/-- A model that satisfies a rule satisfies its schematic instances. -/
theorem Model.sat_subst {M : Model S} {r : Rule S} (h : M.Sat r) (σ : Substitution S) :
    M.Sat (r.subst σ) :=
  fun ν hν => (Rule.holdsAt_subst M.algebra M.truth ν σ r).2
    (h _ (M.space.subst_closed hν σ))

/-- The institution's data and laws, using equality arrows between models. -/
def plain : Silmaril.Inst.Plain Signature where
  Sen := Sentence
  map := Rule.map
  map_id _ := Rule.map_id
  map_comp := Rule.map_comp
  Mod := Model
  reduct := Model.reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat := Model.Sat
  sat_map f M := M.satisfaction f

/-- The room of abstraction-logic rules and models over one signature. -/
def room (S : Signature) : Room.{0, 0, 1} := plain.room S

/-- The abstraction-logic institution, with full-shape symbol maps. -/
def institution : Signature ⥤ Room.{0, 0, 1} := plain.functor

/-- The bundled abstraction-logic institution for use in the logic graph. -/
def inst : Inst.{1, 0, 0, 0, 1} := ⟨Signature, institution⟩

end Silmaril.Logic.Abstraction
