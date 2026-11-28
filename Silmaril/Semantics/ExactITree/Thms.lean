module

public import Silmaril.Semantics.ExactITree.Defs
import Silmaril.Proofs.Semantics.ExactITree.Lowering
import Silmaril.Proofs.Semantics.ExactITree.Execution

/-! Functoriality and the operational satisfaction square for exact lowering. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Exact

open CategoryTheory

universe u v

variable {S T U : Signature.{u}} {P : Profile.{v}} {A B : Type v}

namespace Signature.Hom

@[simp] theorem lower_ret (f : S ⟶ T) (a : A) : f.lower (ret a) = ret a :=
  Proofs.lower_ret f a

@[simp] theorem lower_diverge (f : S ⟶ T) : f.lower (diverge : Tree S.Event A) = diverge :=
  Proofs.lower_diverge f

@[simp] theorem lower_vis (f : S ⟶ T) {R : Type u} (e : S.Event R) (k : R → Tree S.Event A) :
    f.lower (vis e k) = vis (f.exchange e).event (fun r => f.lower (k ((f.exchange e).project r))) :=
  Proofs.lower_vis f e k

@[simp] theorem lower_id (t : Tree S.Event A) : lower (𝟙 S) t = t :=
  Proofs.lower_id t

theorem lower_comp (f : S ⟶ T) (g : T ⟶ U) (t : Tree S.Event A) :
    (f ≫ g).lower t = g.lower (f.lower t) :=
  Proofs.lower_comp f g t

theorem lower_bind (f : S ⟶ T) (t : Tree S.Event A) (k : A → Tree S.Event B) :
    f.lower (t >>= k) = f.lower t >>= fun a => f.lower (k a) :=
  Proofs.lower_bind f t k

end Signature.Hom

@[simp] theorem Kernel.reduct_id (K : Kernel P S) : Kernel.reduct (𝟙 S) K = K :=
  Proofs.reduct_id K

theorem Kernel.reduct_comp (f : S ⟶ T) (g : T ⟶ U) (K : Kernel P U) :
    Kernel.reduct (f ≫ g) K = Kernel.reduct f (Kernel.reduct g K) :=
  Proofs.reduct_comp f g K

variable (f : S ⟶ T) (K : Kernel P T) (env : P.Env)

/-- Target successors are exactly the image of reduct successors at the same store. -/
theorem step_lower (s : Config P S A) (batch : List P.Output) (t : Config P T A) :
    Step K env (s.lower f) batch t ↔
      ∃ next, Step (Kernel.reduct f K) env s batch next ∧ next.lower f = t :=
  Proofs.step_lower f K env s batch t

theorem finish_lower (s : Config P S A) (batch : List P.Output) (last : End P A) :
    Finish K env (s.lower f) batch last ↔ Finish (Kernel.reduct f K) env s batch last :=
  Proofs.finish_lower f K env s batch last

theorem path_lower (s : Config P S A) (log : List P.Output) (t : Config P T A) :
    Path K env (s.lower f) log t ↔
      ∃ next, Path (Kernel.reduct f K) env s log next ∧ next.lower f = t :=
  Proofs.path_lower f K env s log t

theorem infinite_lower (s : Config P S A) (batches : Nat → List P.Output) :
    Infinite K env (s.lower f) batches ↔ Infinite (Kernel.reduct f K) env s batches :=
  Proofs.infinite_lower f K env s batches

/-- Observation equality at each fixed environment and initial store. -/
theorem observes_lower (s : Config P S A) (obs : Observation P A) :
    Observes K env (s.lower f) obs ↔ Observes (Kernel.reduct f K) env s obs :=
  Proofs.observes_lower f K env s obs

/-- The union of the selected trees' observations is left adjoint to the set of
trees whose every observation belongs to the supplied language. -/
theorem flatten_gc (store : P.Store) :
    GaloisConnection (observationRelation (A := A) K env store).image
      (observationRelation (A := A) K env store).core :=
  (observationRelation K env store).image_core_gc

@[simp] theorem Sentence.lower_id (φ : Sentence P S) : φ.lower (𝟙 S) = φ := by
  cases φ
  simp [Sentence.lower]

theorem Sentence.lower_comp (g : T ⟶ U) (φ : Sentence P S) :
    φ.lower (f ≫ g) = (φ.lower f).lower g := by
  cases φ
  simp [Sentence.lower, Signature.Hom.lower_comp]

/-- Translation leaves context assumptions and the observation predicate fixed. -/
theorem satisfies_lower (φ : Sentence P S) :
    Satisfies K (φ.lower f) ↔ Satisfies (Kernel.reduct f K) φ := by
  unfold Satisfies Sentence.lower
  simp only [← observes_lower f K, Config.lower]

end Silmaril.Elgot.ITree.Exact
