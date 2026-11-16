module

public import Silmaril.Project.Core.Defs
public import Silmaril.Logic.Consequence.Defs

/-!
# Consequence systems of interpreted artifacts

`artifactSystem X I` is the consequence system an **interpreted artifact** denotes: `X` is a
project value (CID-pinned bytes read under a format), `I : V → System Ax C` reads the decoded
value as a system, and `Γ ⊢ φ` holds when the bytes decode to some `v` with `I v Γ φ`. It is
the analogue for systems of `Silmaril.Project.Languages.artifactLang`.

**Decode failure is not a verified empty system.** If the bytes do not parse, `artifactSystem X I`
is `⊥` because there is nothing to interpret, not because a checker rejects everything. The
value's `.is` problem (a kernel-checked decode certificate) is what ties the system to a Lean
module: with `X.Is v`, `artifactSystem X I = I v` (`artifactSystem_of_is`).
-/

@[expose] public section

namespace Silmaril.Project.ConsequenceSystems

open Silmaril.Consequence (System)

/-- **The system of an interpreted artifact**: `Γ ⊢ φ` iff the bytes of `X` decode to some `v`
with `I v Γ φ` (`⊥` when they do not decode). -/
def artifactSystem {V Ax C : Type} (X : Silmaril.Project.Value V) (I : V → System Ax C) :
    System Ax C :=
  fun Γ φ => ∃ v, X.parse = some v ∧ I v Γ φ

/-- With a decode certificate `X.Is v`, the artifact's system is the interpretation of `v`. -/
theorem artifactSystem_of_is {V Ax C : Type} {X : Silmaril.Project.Value V} {v : V}
    {I : V → System Ax C} (h : X.Is v) : artifactSystem X I = I v :=
  funext fun _ => funext fun _ => propext ⟨fun ⟨_, hv, hI⟩ => (Option.some.inj (h.symm.trans hv)) ▸ hI,
    fun hI => ⟨v, h, hI⟩⟩

end Silmaril.Project.ConsequenceSystems
