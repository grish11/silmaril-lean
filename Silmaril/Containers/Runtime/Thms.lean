module

public import Silmaril.Containers.Runtime.Defs
public import Silmaril.Containers.Behaviour.Thms
import Silmaril.Proofs.Containers.Runtime.Basic

/-!
# Runtime models: theorems

PROVED (standard axioms). Proofs longer than a few lines are in
`Silmaril.Proofs.Containers.Runtime` and only pointed at from here.

**Unfolding.** `Runtime.beh_error`, `Runtime.beh_ok`: the runs of a refused image, and of a
loaded one.

**Comparing models.**

* `Runtime.Le.refl`, `Runtime.Le.trans`: a preorder on models over the same images, whatever
  their programs and semantics;
* `Runtime.sat_of_le`: what holds of every run of a larger model holds of a smaller one;
* `Runtime.restrict_le`: **strengthening an assumption** gives a smaller model;
* `Runtime.le_mayKill`: **admitting runtime kills** gives a larger model.

**Extra runtime behaviours.**

* `Runtime.safe_mayKill`, `Runtime.partialCorrect_mayKill`: safety and partial correctness
  survive runtime kills;
* `Runtime.totalCorrect_not_mayKill`: total correctness does not.

**Enforcement.**

* `Runtime.enforce_confined`: under an enforcing runtime every run is confined to the profile;
* `Runtime.enforce_eq_of_confined`: for a program whose runs are confined, enforcement changes
  nothing.

**Prefixes.** `Beh.prefix_of_prefix`: a prefix of a prefix of a run is a prefix of it.
-/

public section

namespace Silmaril.Containers

open Silmaril.Proofs.Containers.Runtime

variable {I P P' P'' E : Type}

theorem Beh.prefix_of_prefix {b : Beh E} {t u : List E} (h : b.Prefix t) (hu : u <+: t) :
    b.Prefix u :=
  Silmaril.Proofs.Containers.Runtime.prefix_of_prefix h hu

namespace Runtime

theorem beh_error {R : Runtime I P E} {i : I} {r : Refusal} (hl : R.load i = .error r)
    (b : Beh E) : R.beh i b ↔ b = .done [] (.refused r) :=
  Silmaril.Proofs.Containers.Runtime.beh_error hl b

theorem beh_ok {R : Runtime I P E} {i : I} {p : P} (hl : R.load i = .ok p) (b : Beh E) :
    R.beh i b ↔ ∃ b₀, R.sem p b₀ ∧ R.obs b₀ b :=
  Silmaril.Proofs.Containers.Runtime.beh_ok hl b

theorem Le.refl (R : Runtime I P E) : R.Le R := fun _ _ h => h

theorem Le.trans {R : Runtime I P E} {R' : Runtime I P' E} {R'' : Runtime I P'' E}
    (h₁ : R.Le R') (h₂ : R'.Le R'') : R.Le R'' := fun i b h => h₂ i b (h₁ i b h)

theorem sat_of_le {R : Runtime I P E} {R' : Runtime I P' E} (h : R.Le R') {i : I}
    {φ : Spec E} (h' : (R'.beh i).Sat φ) : (R.beh i).Sat φ :=
  Model.Refines.sat (h i) h'

theorem restrict_le (R : Runtime I P E) (A : Spec E) : (R.restrict A).Le R :=
  Silmaril.Proofs.Containers.Runtime.restrict_le R A

theorem le_mayKill (R : Runtime I P E) (ks : Kill → Prop) : R.Le (R.mayKill ks) :=
  Silmaril.Proofs.Containers.Runtime.le_mayKill R ks

theorem safe_mayKill {R : Runtime I P E} {ks : Kill → Prop} {i : I} {S : List E → Prop}
    (h : (R.beh i).Sat (Spec.safe S)) : ((R.mayKill ks).beh i).Sat (Spec.safe S) :=
  Silmaril.Proofs.Containers.Runtime.safe_mayKill h

theorem partialCorrect_mayKill {R : Runtime I P E} {ks : Kill → Prop} {i : I}
    {post : List E → UInt8 → Prop} (h : (R.beh i).Sat (Spec.partialCorrect post)) :
    ((R.mayKill ks).beh i).Sat (Spec.partialCorrect post) :=
  Silmaril.Proofs.Containers.Runtime.partialCorrect_mayKill h

/-- A model whose only run exits at once is totally correct; the same model with possible
out-of-memory kills is not. -/
theorem totalCorrect_not_mayKill :
    ∃ R : Runtime Unit Unit Unit,
      (R.beh ()).Sat (Spec.totalCorrect fun _ _ => True) ∧
        ¬ ((R.mayKill (· = .oom)).beh ()).Sat (Spec.totalCorrect fun _ _ => True) :=
  Silmaril.Proofs.Containers.Runtime.totalCorrect_not_mayKill

theorem enforce_confined {R : Runtime I P Ev} {Pr : Profile} {i : I} :
    ((R.enforce Pr).beh i).Sat (Spec.always fun e => Pr e.cap = true) :=
  Silmaril.Proofs.Containers.Runtime.enforce_confined

theorem enforce_eq_of_confined {R : Runtime I P Ev} {Pr : Profile} {i : I}
    (h : (R.beh i).Sat (Spec.always fun e => Pr e.cap = true)) (b : Beh Ev) :
    (R.enforce Pr).beh i b ↔ R.beh i b :=
  Silmaril.Proofs.Containers.Runtime.enforce_eq_of_confined h b

end Runtime

end Silmaril.Containers
