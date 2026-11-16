module

public import Silmaril.Logic.Kore.Modules.Semantics.Thms
public import Silmaril.Logic.Kore.Modules.Theory.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Semantics
open Checking
variable {ambient : Scope}

/-- A source module model satisfies the direct raw interpretation of every
retained local/transitively imported source axiom, each at its recorded fuel. -/
def Models (m : CheckedModule ambient) (M : Matching.FirstOrder.Model ambient.signature) : Prop :=
  ∀ d ∈ m.axioms, Satisfies M d.fuel d.raw

/-- Consequence for an actual retained source claim, using raw axiom/claim truth.
The definition never mentions typed sentence satisfaction. -/
def Proves (m : CheckedModule ambient) (claim : CheckedSentence ambient) : Prop :=
  ∀ M : Matching.FirstOrder.Model ambient.signature, Models m M → Satisfies M claim.fuel claim.raw
end Silmaril.Logic.Kore.Modules.Semantics
