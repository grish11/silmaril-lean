module

public import Silmaril.Logic.ITree.Institution.Trace.Policy.Defs
import Silmaril.Proofs.Logic.ITree.Institution.Trace.Policy

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree Opposite
open Silmaril.Logic.Institution

universe u v w

variable {S T U : Signature.{u}} {X : Type w}

namespace Policy

theorem reduct_mono (f : S ⟶ T) : Monotone (reduct (X := X) f) :=
  fun _ _ admits q x _r y ⟨reply, projects, step⟩ =>
    ⟨reply, projects, admits (f.request q) x reply y step⟩

@[simp] theorem reduct_id (p : Policy S X) : p.reduct (𝟙 S) = p :=
  eq_of_heq (Model.mk.inj (Model.reduct_id (p.toModel fun _ => True))).2.2

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (p : Policy U X) :
    p.reduct (f ≫ g) = (p.reduct g).reduct f :=
  eq_of_heq (Model.mk.inj (Model.reduct_comp f g (p.toModel fun _ => True))).2.2

/-- Allowing more reply transitions can add handled observations. -/
theorem handledTrace_mono {p q : Policy S X} (admits : p ≤ q) {A : Type v}
    (x : X) (t : Tree S.Event A) (trace : Trace S.Event A) :
    HandledTrace p x t trace → HandledTrace q x t trace :=
  fun seen => ⟨seen.1, Silmaril.Proofs.Logic.ITree.TraceInstitution.replay_mono admits trace x seen.2⟩

/-- Satisfaction is downward closed in allowed replies at fixed initial states. -/
theorem sat_antitone (initial : X → Prop) {S : TraceSignature.{u}} (φ : Sentence.{u, v} S) :
    Antitone (fun p : Policy S.toSignature X => Sat (p.toModel initial) φ) :=
  fun _ _ admits holds x start trace seen =>
    holds x start trace (handledTrace_mono admits x φ.program trace seen)

end Policy

/-- Contravariant reducts between the pointwise policy posets. -/
def policyModels (X : Type w) : TraceSignature.{u}ᵒᵖ ⥤ Cat.{max (u + 1) w, max (u + 1) w} where
  obj S := @Cat.of (Policy S.unop.toSignature X) (Preorder.smallCategory _)
  map f := Cat.Hom.ofFunctor (Policy.reduct_mono (X := X) f.unop.hom).functor
  map_id S := Cat.Hom.ext (Functor.ext fun p => Policy.reduct_id (S := S.unop.toSignature) p)
  map_comp _ _ := Cat.Hom.ext (Functor.ext fun p => Policy.reduct_comp _ _ p)

/-- The same handled-trace sentences with a non-discrete policy fiber at
a fixed state carrier and fixed initial states. -/
noncomputable def policyInstitution (X : Type w) (initial : X → Prop) :
    ClassicInstitution.{u + 1, u + 1, max (u + 1) (v + 1), max (u + 1) w, max (u + 1) w}
      TraceSignature.{u} where
  Sen := sentences.{u, v}
  Mod := policyModels X
  Sat _ policy φ := Sat (policy.toModel initial) φ
  satisfaction f policy φ := satisfaction f (policy.toModel initial) φ

end Silmaril.Logic.ITree.TraceInstitution
