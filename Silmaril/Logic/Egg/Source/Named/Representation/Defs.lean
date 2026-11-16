module

public import Silmaril.Logic.Egg.Source.Named.Accepted.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.Task
open CategoryTheory

/-- Anti-subset completion gate: every finite ordered collection of arbitrary
ambient guarded equations has actual accepted complete inferred bytes and an
actual interpretation recovering that exact ordered list. Full unused contexts
are part of Rule equality. No ambient naming or nonempty model is assumed. -/
def finiteProgramRepresentation : Prop :=
  ∀ (S : Core.Signature) (rules : List (Core.Rule S)),
    ∃ (p : AcceptedInferredProgram) (symbols : p.declarations.signature ⟶ S),
      p.program.resolved.map (Core.Rule.map symbols) = rules

/-- Inferred admission must be complete relative to any genuine supplied
admission, retaining original bytes and every ordered rule. This is stronger
than producing a convenient alternate source spelling for one fixture. -/
def inferredAdmissionComplete : Prop :=
  ∀ (D : Declarations) (p : AcceptedProgram D),
    ∃ (q : AcceptedInferredProgram) (symbols : q.declarations.signature ⟶ D.signature),
      q.program.bytes = p.bytes ∧ q.program.raw = p.raw ∧
      q.program.resolved.map (Core.Rule.map symbols) = p.resolved

end Silmaril.Logic.Egg.Source.Named.Task
