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

**Runtime additions never hide undefined behaviour.**

* `Runtime.obsKeepsUB_eq`, `ObsKeepsUB.restrict`, `ObsKeepsUB.mayKill`: adding nothing keeps
  every program run with undefined behaviour, and so do assumptions and kills;
* `Runtime.preservesUB_restrict`, `preservesUB_mayKill`: each keeps every run of the model it
  starts from that has undefined behaviour; `Runtime.noUB_of_preservesUB`: so no undefined
  behaviour after them implies none before;
* `Runtime.noUB_restrict_iff`, `noUB_mayKill_iff`: no undefined behaviour is exactly the same
  property before and after an assumption or kills: they neither create nor hide it (so
  `restrict Spec.noUB` is not a way to assume it);
* `Runtime.enforce_keeps_reached_ub`: enforcement keeps every run that reaches undefined
  behaviour through allowed events; `ub_preempted_of_enforce`: it removes undefined behaviour
  only where a disallowed event comes first (pre-emption, under faithful enforcement);
  `noUB_enforce_of`: it creates none;
* `Runtime.withObs_can_hide_ub`: an arbitrary account of what the runtime adds can hide undefined
  behaviour, which is why verification over a runtime model needs `ObsKeepsUB`;
* `Runtime.beh_of_sem_undefined`: a program run with undefined behaviour is a run the environment
  sees under any runtime whose additions keep undefined behaviour.

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

/-! ## Runtime additions keep undefined behaviour -/

theorem obsKeepsUB_eq : ObsKeepsUB (E := E) Eq := fun _ _ => rfl

theorem ObsKeepsUB.restrict {R : Runtime I P E} (h : ObsKeepsUB R.obs) (A : Spec E) :
    ObsKeepsUB (R.restrict A).obs := fun b₀ hu => ⟨h b₀ hu, .inr hu⟩

theorem ObsKeepsUB.mayKill {R : Runtime I P E} (h : ObsKeepsUB R.obs) (ks : Kill → Prop) :
    ObsKeepsUB (R.mayKill ks).obs := fun b₀ hu => ⟨b₀, h b₀ hu, .inl rfl⟩

theorem preservesUB_restrict (R : Runtime I P E) (A : Spec E) : (R.restrict A).PreservesUB R :=
  Silmaril.Proofs.Containers.Runtime.preservesUB_restrict R A

theorem preservesUB_mayKill (R : Runtime I P E) (ks : Kill → Prop) :
    (R.mayKill ks).PreservesUB R :=
  Silmaril.Proofs.Containers.Runtime.preservesUB_mayKill R ks

theorem enforce_keeps_reached_ub {R : Runtime I P Ev} {Pr : Profile} {i : I} {b : Beh Ev}
    (hb : R.beh i b) (ha : Spec.always (fun e => Pr e.cap = true) b) :
    (R.enforce Pr).beh i b :=
  Silmaril.Proofs.Containers.Runtime.enforce_keeps_reached_ub hb ha

theorem ub_preempted_of_enforce {R : Runtime I P Ev} {Pr : Profile} {i : I}
    (h : ((R.enforce Pr).beh i).Sat Spec.noUB) {b : Beh Ev} (hb : R.beh i b)
    (hu : ¬ Spec.noUB b) : ¬ Spec.always (fun e => Pr e.cap = true) b :=
  Silmaril.Proofs.Containers.Runtime.ub_preempted_of_enforce h hb hu

theorem withObs_can_hide_ub :
    ∃ (R : Runtime Unit Unit Unit) (o : Beh Unit → Beh Unit → Prop),
      ¬ (R.beh ()).Sat Spec.noUB ∧ ((R.withObs o).beh ()).Sat Spec.noUB :=
  Silmaril.Proofs.Containers.Runtime.withObs_can_hide_ub

theorem noUB_of_preservesUB {R' : Runtime I P' E} {R : Runtime I P E} (h : R'.PreservesUB R)
    {i : I} (h' : (R'.beh i).Sat Spec.noUB) : (R.beh i).Sat Spec.noUB :=
  Silmaril.Proofs.Containers.Runtime.noUB_of_preservesUB h h'

theorem noUB_restrict_iff (R : Runtime I P E) (A : Spec E) (i : I) :
    ((R.restrict A).beh i).Sat Spec.noUB ↔ (R.beh i).Sat Spec.noUB :=
  ⟨noUB_of_preservesUB (preservesUB_restrict R A), sat_of_le (restrict_le R A)⟩

theorem noUB_mayKill_iff (R : Runtime I P E) (ks : Kill → Prop) (i : I) :
    ((R.mayKill ks).beh i).Sat Spec.noUB ↔ (R.beh i).Sat Spec.noUB :=
  ⟨noUB_of_preservesUB (preservesUB_mayKill R ks), fun h =>
    Silmaril.Proofs.Containers.Runtime.noUB_of_runs (fun _ hb =>
      (Silmaril.Proofs.Containers.Runtime.beh_mayKill hb).imp id
        fun ⟨_, t, k, _, _, _, he⟩ => ⟨t, k, he⟩) h⟩

theorem noUB_enforce_of (R : Runtime I P Ev) (Pr : Profile) (i : I)
    (h : (R.beh i).Sat Spec.noUB) : ((R.enforce Pr).beh i).Sat Spec.noUB :=
  Silmaril.Proofs.Containers.Runtime.noUB_of_runs
    (fun _ hb => Silmaril.Proofs.Containers.Runtime.enforce_runs hb) h

/-- A program run with undefined behaviour is seen by the environment, when what the runtime adds
keeps undefined behaviour. -/
theorem beh_of_sem_undefined {R : Runtime I P E} (hobs : ObsKeepsUB R.obs) {i : I} {p : P}
    (hl : R.load i = .ok p) {b : Beh E} (hs : R.sem p b) (hu : ¬ Spec.noUB b) : R.beh i b :=
  Silmaril.Proofs.Containers.Runtime.beh_of_sem_undefined hobs hl hs hu

end Runtime

end Silmaril.Containers
