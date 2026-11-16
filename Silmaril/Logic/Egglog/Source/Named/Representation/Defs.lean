module

public import Silmaril.Logic.Egglog.Source.Named.Accepted.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Task
open CategoryTheory

/-- Final anti-subset gate: every sentence of every arbitrary Core signature has
finite checked declaration support and actual accepted complete bytes. The theorem
`finiteSupportRepresentation_task` discharges this proposition unconditionally. -/
def finiteSupportRepresentation : Prop :=
  ∀ (S : Core.Signature) (sentence : Core.Sentence S),
    ∃ (unit : AcceptedUnit) (symbols : unit.declarations.signature ⟶ S),
      unit.resolved.map symbols = sentence

end Silmaril.Logic.Egglog.Source.Named.Task
