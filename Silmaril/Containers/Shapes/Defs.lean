module

public import Silmaril.Project.Defs
public import Silmaril.Containers.Check.Defs
public import Silmaril.Containers.Machine.Defs
public import Silmaril.Containers.Mini.Defs

/-!
# Standard problem shapes: containers

The obligations a container problem asks, as registered shapes (`@[problem]`, the project
registry of `docs/projects/silmaril-projects.md`). Every behavioural shape is a **verified**
obligation: it includes "no undefined behaviour" (`vpre`), never raw satisfaction (`pre`).

| name | statement |
| --- | --- |
| `silmaril.shapes.containers.vpre` | `vpre R φ i`: every run of `i` under `R` has no undefined behaviour and satisfies `φ` |
| `silmaril.shapes.containers.wlp` | `wlp R post i`: no undefined behaviour, partial correctness |
| `silmaril.shapes.containers.wp` | `wp R post i`: no undefined behaviour, total correctness |
| `silmaril.shapes.containers.vsufficient` | `VSufficient R Q φ`: `Q` implies the verification precondition |
| `silmaril.shapes.containers.checker_sound` | `Accept.Sound check (vset R φ)`: a decidable checker accepts only images satisfying `vpre R φ` |
| `silmaril.shapes.containers.preserves_ub` | `R'.PreservesUB R`: a runtime transformer keeps every run with undefined behaviour |
| `silmaril.shapes.containers.seq_agrees` | `SeqAgrees R₁ R₂ i`: the transfer obligation between machines |
| `silmaril.shapes.containers.monitor_correct` | `vmonitor ok` is correct for `vlang ok` (interleaved protocol) |

**Obligation kinds** (`ObligationKind`) name what a claim is about, so that a table of
obligations for an image keeps them apart: trust (digests, integrity, binding), format (decoding
octets), shape (where the program is), loader, machine (including the clone policy), resource,
security (profile, enforcement), behaviour (`vpre`). `catalogue` lists the registered instances
with their kind.

`Thms` registers the consequence systems of the minimal machine and the problem instances, with
their answers.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Shapes

open Silmaril.Containers Silmaril.Containers.Check Silmaril.Containers.Mach

/-- **The verification precondition.** -/
@[problem "silmaril.shapes.containers.vpre"
  (title := "Every run of an image under a runtime model has no undefined behaviour and meets a specification")]
def VPre {I P E : Type} (R : Runtime I P E) (φ : Spec E) (i : I) : Prop := vpre R φ i

/-- **The weakest liberal precondition** (no undefined behaviour, partial correctness). -/
@[problem "silmaril.shapes.containers.wlp"
  (title := "An image has no undefined behaviour and is partially correct under a runtime model")]
def Wlp {I P E : Type} (R : Runtime I P E) (post : List E → UInt8 → Prop) (i : I) : Prop :=
  wlp R post i

/-- **The weakest precondition** (no undefined behaviour, total correctness). -/
@[problem "silmaril.shapes.containers.wp"
  (title := "An image has no undefined behaviour and is totally correct under a runtime model")]
def Wp {I P E : Type} (R : Runtime I P E) (post : List E → UInt8 → Prop) (i : I) : Prop :=
  wp R post i

/-- **A verified sufficient precondition.** -/
@[problem "silmaril.shapes.containers.vsufficient"
  (title := "A predicate on images implies the verification precondition")]
def VSufficientShape {I P E : Type} (R : Runtime I P E) (Q : I → Prop) (φ : Spec E) : Prop :=
  VSufficient R Q φ

/-- **A sound checker** for the verification precondition. -/
@[problem "silmaril.shapes.containers.checker_sound"
  (title := "A decidable checker accepts only images meeting the verification precondition")]
def CheckerSound {I P E : Type} (R : Runtime I P E) (check : I → Bool) (φ : Spec E) : Prop :=
  Silmaril.Accept.Sound check (vset R φ)

/-- **A runtime transformer preserves undefined behaviour.** -/
@[problem "silmaril.shapes.containers.preserves_ub"
  (title := "A runtime model keeps every run with undefined behaviour of another")]
def PreservesUBShape {I P P' E : Type} (R' : Runtime I P' E) (R : Runtime I P E) : Prop :=
  R'.PreservesUB R

/-- **Agreement between machines** on an image. -/
@[problem "silmaril.shapes.containers.seq_agrees"
  (title := "Every run of an image under one runtime model is a run under another")]
def SeqAgreesShape {I P P' E : Type} (R₁ : Runtime I P' E) (R₂ : Runtime I P E) (i : I) :
    Prop :=
  SeqAgrees R₁ R₂ i

/-- **The no-undefined-behaviour monitor is correct.** -/
@[problem "silmaril.shapes.containers.monitor_correct"
  (title := "The observation monitor is correct for its language in the interleaved protocol")]
def MonitorCorrect {E : Type} (ok : E → Bool) : Prop :=
  (vmonitor ok).CorrectInterleaved (vlang ok)

/-! ## Obligation kinds -/

/-- **What an obligation is about.** -/
inductive ObligationKind where
  | trust
  | format
  | shape
  | loader
  | machine
  | resource
  | security
  | behaviour
  deriving DecidableEq, Repr

/-! ## Named systems and data of the minimal machine -/

/-- The verified consequence system of the minimal machine. -/
def miniVsys : Silmaril.Consequence.System (Flat (List Mini.Instr)) (Spec Ev) := vsys Mini.machRT

/-- The raw system of the minimal machine (a comparison). -/
def miniRawsys : Silmaril.Consequence.System (Flat (List Mini.Instr)) (Spec Ev) :=
  rawsys Mini.machRT

/-- The checker system of `noUBCheck`. -/
def miniCheckSys : Silmaril.Consequence.System (Flat (List Mini.Instr)) (Spec Ev) :=
  checkSys Mini.noUBCheck (Spec.partialCorrect fun _ _ => True)

/-- The postcondition of `hello`. -/
def helloPost (t : List Ev) (c : UInt8) : Prop := t = [.stdout (Fixtures.ascii "hi")] ∧ c = 0

/-- The trivial postcondition: only "no undefined behaviour" remains. -/
def anyPost (_ : List Ev) (_ : UInt8) : Prop := True

/-- The allowed events of a profile, as the monitor reads them. -/
def allowed (Pr : Profile) (e : Ev) : Bool := Pr e.cap

end Silmaril.Containers.Shapes
