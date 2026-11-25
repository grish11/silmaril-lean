module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime

variable {I : Type} {S : Syntax I}

theorem derives_induction {R : List (AdminInstr I) → List (AdminInstr I) → Prop}
    (redex : ∀ {before after}, Redex S before after → R before after)
    (context : ∀ saved {before after tail}, R before after → Admitted S tail →
      R (S.values saved ++ before ++ tail) (S.values saved ++ after ++ tail))
    {before after : List (AdminInstr I)} (h : DerivesEdge S before after) : R before after :=
  Derives.least (M := fun j => R j.1 j.2) h (by
    intro r member ih
    change RuleInstance S r at member
    cases member with
    | redex h => exact redex h
    | context saved before after tail tailOk => exact context saved (ih (before, after) (List.Mem.head _)) tailOk)

end Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs
