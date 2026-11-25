module

public import Silmaril.Wasm.Institution.Operational.Blocks.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

theorem enter (result : Option NumType) (body : Locals.State) :
    Edge (.block result body) (.label result body) :=
  Derives.apply (RuleInstance.enter result body) (fun _ h => nomatch h)

theorem reduce (result : Option NumType) {a b : Locals.State} (step : Locals.Edge a b) :
    Edge (.label result a) (.label result b) := Proofs.reduce result step

theorem exit (result : Option NumType) (ls vs : List Value) :
    Edge (.label result ⟨ls, Locals.values vs⟩) (.done ls vs) :=
  Derives.apply (RuleInstance.exit result ls vs) (fun _ h => nomatch h)

theorem invert {a b : State} (step : Edge a b) :
    (∃ result body, a = .block result body ∧ b = .label result body) ∨
    (∃ result before after, a = .label result before ∧ b = .label result after ∧
      Locals.Edge before after) ∨
    (∃ result ls vs, a = .label result ⟨ls, Locals.values vs⟩ ∧ b = .done ls vs) :=
  Proofs.invert step

theorem closed {types : List NumType} {result : Option NumType} {a b : State}
    (guard : Admitted types result a) (step : Edge a b) : Admitted types result b :=
  Proofs.closed guard step

end Silmaril.Wasm.Institution.Operational.Blocks
