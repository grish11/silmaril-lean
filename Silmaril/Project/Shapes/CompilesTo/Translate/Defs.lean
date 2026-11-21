module

public import Silmaril.Project.Shapes.CompilesTo.Defs

/-!
# C ⇒ C translations of a function, read from canonical entries

A C ⇒ C problem relates two C functions of the same signature, each as Cerberus Core (`CFn`):
the source and its translation (an optimiser's output, a refactoring, a hand edit).

* `CFn.HaltsWith F s o`: some Core run of `F` from `s` halts with the outcome `o`.
* `CanonicalRefines F G`: for every argument tuple on which the source's canonical entry is safe,
  every outcome the target's canonical entry halts with is one the source's canonical entry
  halts with. `CanonicalEquivalent` is refinement both ways.

The statements read the canonical entries only (`CFn.canonicalEntry`: the arguments allocated in
order from an empty memory), as the `c.compiles_to.canonical_entry` rows do; they say nothing about
calls from other memories, environments or caller continuations. A refutation
(`¬ CanonicalRefines F G`) is the strong direction: one tuple from the canonical entry where the
target halts with an outcome the source cannot reach.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C (CFn)
open Silmaril.X86.SystemV.CApi (Signature)

/-- Some Core run of `F` from `s` halts with the outcome `o`. -/
def _root_.Silmaril.Project.Shapes.C.CFn.HaltsWith {sig : Signature} (F : CFn sig) (s : State)
    (o : Outcome) : Prop :=
  ∃ t, Relation.ReflTransGen (fun a b => ∃ act, Step F.file F.labels a act b) s t ∧
    t.control = .halt o

/-- **The translation `G` refines the source `F`** from the canonical entries: wherever the
source is safe, every outcome of the target is an outcome of the source. -/
@[problem "silmaril.shapes.c.translates.canonical_refines"
  (title := "A C function refines another from their canonical entries")]
def CanonicalRefines {sig : Signature} (F G : CFn sig) : Prop :=
  ∀ a, (F.source []).Safe (F.canonicalEntry a) →
    ∀ o, G.HaltsWith (G.canonicalEntry a) o → F.HaltsWith (F.canonicalEntry a) o

/-- **The two functions are equivalent** from the canonical entries: refinement both ways. -/
@[problem "silmaril.shapes.c.translates.canonical_equivalent"
  (title := "Two C functions are equivalent from their canonical entries")]
def CanonicalEquivalent {sig : Signature} (F G : CFn sig) : Prop :=
  CanonicalRefines F G ∧ CanonicalRefines G F

/-- **A checker's view of one run**: the state halted with the defined integer `n`. Evaluated on
`forcedRun …` (by `cbv`, checked by the kernel) it pins down a canonical run's outcome. -/
def endsInt (n : Int) : Option State → Bool
  | some h => match h.control with
    | .halt (.defined (.loaded (.specified (.integer m)))) => m == n
    | _ => false
  | none => false

end Silmaril.Project.Shapes.CompilesTo

end
