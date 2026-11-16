module

public import Silmaril.Containers.Behaviour.Defs

/-!
# Runtime models: loading, process semantics and what the runtime adds

A **runtime model** (`Runtime I P E`) says what happens when an image `I` is started:

* `load`: the loader. It turns the image into a program `P`, or refuses (`Refusal`). For a
  flat image this is a shape (`Runtime.ofShape`); for a layered image it first flattens it
  from content stores (`Runtime.layered`);
* `sem`: **the process semantics** (`ProcSem P E`), the runs of each program over all
  environments. It is a parameter. It may be given directly (the tiny language of
  `Silmaril.Containers.Fixtures`) or built from a **pluggable machine semantics**
  (`Silmaril.Containers.Mach.MachineSem`, `Runtime.ofMachine`): states with whatever memory,
  concurrency and scheduling model the machine has, labelled steps, and undefined behaviour as
  explicit runs. A sequential x86-64 machine with thread creation as undefined behaviour, the
  Linux process semantics of `Silmaril.Process`, a Wasm host, and later a parallel x86-64
  machine are instances;
* `obs`: **what the runtime adds**: `obs b₀ b` when the runtime turns a run `b₀` of the program
  into the run `b` its environment sees. `Eq` adds nothing (`Runtime.exact`).

A model is compared with another on the same images by inclusion of runs (`Runtime.Le`); the
programs and their semantics may differ. Two ways of changing a model must not be confused:

* **Strengthening an assumption** removes runs (`Runtime.restrict A`: "assume no runtime kill",
  "assume the host never runs out of memory"). Everything proved of the larger model holds of
  the smaller one (`Thms.Runtime.sat_of_le`), but only under the assumption: the theorem is
  about fewer runs.
* **Admitting extra runtime behaviours** adds runs (`Runtime.mayKill`: the runtime may stop the
  process at any point, for a reason in `ks`). Safety and partial correctness survive
  (`Thms.Runtime.safe_mayKill`, `Thms.Runtime.partialCorrect_mayKill`); total correctness does
  not (`Thms.Runtime.totalCorrect_not_mayKill`).

**Enforcement.** `Runtime.enforce P` is a runtime that stops a process with `killed .policy` at
its first event outside the profile `P` (seccomp, a network namespace, a VM's devices). Its runs
without undefined behaviour are confined (`Thms.Runtime.enforce_confined`), and on a confined run
it changes nothing (`Thms.Runtime.enforce_eq_of_confined`).

**Undefined behaviour under runtime-added behaviours.** "No undefined behaviour" quantifies over
the runs the environment sees, that is, program runs transformed by what the runtime adds. The
runtime may add runs (a kill truncates a program run; the truncated run ends in `killed`, not in
undefined behaviour), but it must not remove a program run that has undefined behaviour:
`ObsKeepsUB` for what a runtime adds, `PreservesUB` between models. `restrict`, `mayKill` and
`enforce` all preserve the undefined behaviour of the model they start from
(`Thms.Runtime.preservesUB_restrict`, `preservesUB_mayKill`, `preservesUB_enforce`), so none of
them can make an image with reachable undefined behaviour satisfy a verification precondition
(`Thms.Runtime.pre_noUB_restrict_iff` and its siblings). Undefined behaviour of the runtime
itself (a container runtime bug) is outside these models: it is an assumption about the
runtime.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers

/-- **A process semantics**: the runs of each program, over all environments. -/
abbrev ProcSem (P E : Type) : Type := P → Model E

/-- **A runtime model**: a loader, a process semantics, and what the runtime adds to runs. -/
structure Runtime (I P E : Type) where
  load : I → Except Refusal P
  sem : ProcSem P E
  obs : Beh E → Beh E → Prop

namespace Runtime

variable {I P P' P'' E : Type}

/-- **The runs of an image** under a runtime model. -/
def beh (R : Runtime I P E) (i : I) : Model E := fun b =>
  match R.load i with
  | .error r => b = .done [] (.refused r)
  | .ok p => ∃ b₀, R.sem p b₀ ∧ R.obs b₀ b

/-- `R ≤ R'`: on every image, every run of `R` is a run of `R'`. -/
def Le (R : Runtime I P E) (R' : Runtime I P' E) : Prop := ∀ i, (R.beh i).Refines (R'.beh i)

/-- The same loader and semantics with another account of what the runtime adds. -/
def withObs (R : Runtime I P E) (o : Beh E → Beh E → Prop) : Runtime I P E :=
  { R with obs := o }

/-- **A runtime that adds nothing.** -/
def exact (load : I → Except Refusal P) (sem : ProcSem P E) : Runtime I P E :=
  ⟨load, sem, Eq⟩

/-- **What the runtime adds keeps undefined behaviour**: a program run that ends in undefined
behaviour is also a run the environment sees. Runtime-added behaviours may add runs (kills),
but may not replace a run with undefined behaviour by one without. -/
def ObsKeepsUB (o : Beh E → Beh E → Prop) : Prop := ∀ b₀, ¬ Spec.noUB b₀ → o b₀ b₀

/-- **`R'` preserves the undefined behaviour of `R`**: every run of `R` with undefined
behaviour is a run of `R'`. Then `R'` cannot certify an image that `R` does not
(`Thms.Runtime.noUB_of_preservesUB`). -/
def PreservesUB {P' : Type} (R' : Runtime I P' E) (R : Runtime I P E) : Prop :=
  ∀ i b, R.beh i b → ¬ Spec.noUB b → R'.beh i b

/-- **Strengthening an assumption**: keep only the runs satisfying `A`, **and every run with
undefined behaviour**. An assumption is about the environment and the runtime (no
out-of-memory kill, a live environment); it never excuses the program's own undefined
behaviour, so `A` cannot remove a run that has it. -/
def restrict (R : Runtime I P E) (A : Spec E) : Runtime I P E :=
  R.withObs fun b₀ b => R.obs b₀ b ∧ (A b ∨ ¬ Spec.noUB b)

/-- **The runtime may stop the process** at any point, for a reason in `ks`. -/
def killObs (ks : Kill → Prop) (b₀ b : Beh E) : Prop :=
  b = b₀ ∨ ∃ t k, ks k ∧ b₀.Prefix t ∧ b = .done t (.killed k)

/-- A runtime that adds nothing, except that it may stop the process for a reason in `ks`. -/
def mayKill (R : Runtime I P E) (ks : Kill → Prop) : Runtime I P E :=
  R.withObs fun b₀ b => ∃ b₁, R.obs b₀ b₁ ∧ killObs ks b₁ b

/-- **Enforcing a profile**: a run whose events are allowed is unchanged; otherwise the runtime
stops the process just before its first event outside the profile. **A run with undefined
behaviour is kept as it is**, even when the runtime would stop it earlier: verification of an
image never relies on enforcement to hide the program's undefined behaviour (and a run with
undefined behaviour may do things the profile filter does not observe). -/
def enforceObs (Pr : Profile) (b₀ b : Beh Ev) : Prop :=
  (Spec.always (fun e => Pr e.cap = true) b₀ ∧ b = b₀) ∨
    (¬ Spec.noUB b₀ ∧ b = b₀) ∨
    ∃ t e, b₀.Prefix (t ++ [e]) ∧ Confined Pr t ∧ Pr e.cap = false ∧
      b = .done t (.killed .policy)

/-- A runtime that enforces the profile `Pr` on the runs of `R`. -/
def enforce {I P : Type} (R : Runtime I P Ev) (Pr : Profile) : Runtime I P Ev :=
  R.withObs fun b₀ b => ∃ b₁, R.obs b₀ b₁ ∧ enforceObs Pr b₁ b

end Runtime

/-- **A runtime model for flat images of a shape**: the shape finds the program, or the runtime
refuses the image (`noShape`). -/
def Runtime.ofShape {C P E : Type} (sh : Shape C P) (sem : ProcSem P E)
    (obs : Beh E → Beh E → Prop := Eq) : Runtime (Flat C) P E where
  load img := match sh.program img with
    | some p => .ok p
    | none => .error .noShape
  sem := sem
  obs := obs

/-- **A runtime model for layered images**: flatten from the stores, then start the flat image;
a missing configuration or layer is a refusal (`missingBlob`). -/
def Runtime.layered {D C P E : Type} (S : Stores D C) (R : Runtime (Flat C) P E) :
    Runtime (Layered D) P E where
  load m := match m.flatten S with
    | some img => R.load img
    | none => .error .missingBlob
  sem := R.sem
  obs := R.obs

end Silmaril.Containers
