module

public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs

/-!
# Linked sessions, specification to reference: definitions

**Scope.** `Linked2` only (the import-free exporter A answering every import of the importer B),
under `Linked2.Adequate`; the sessions are those of `Linked2.SessSpec` and `Linked2.sessObs`
(`LinkedSessionRef.Defs`).

`Linked2.IRToSpec P l` is the one direction of linked session adequacy that is not proved: every
typed IR session play of `l.toComp.den (impSem P)` (`Linked2.sessMoves`, one outcome per call) is
the play of a `Linked2.SessSpec` session from the instances' stores. It reads the plays of the
linked composition back into importer rounds and an `ExpRunT` of the exporter, i.e. it inverts
the composition of the two threaded session strategies. It waits on the H2 owner's
`comp_threadS` (requested on #207,
`DivComp.comp (threadS tA sA) (threadS tB sB) = threadS (linkS tA tB) (sA, sB)`). It is a named
hypothesis of the conditional theorems (`Linked2.sessAdequacy_of`), not an axiom, and no theorem
assumes it outright.

Not covered: divergence and host observations of linked sessions (a later step; they are not
assumed vacuous: `SessCalls` records terminating outcomes only, and a parent passing host imports
to B lets B call the host). The parser from bytes to these components, and F6, are pending.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **The IR to specification direction of linked sessions** (a hypothesis, pending the H2
owner's `comp_threadS`): for the instances `Ie`, `Ii` of the exporter's and the importer's core
modules, every typed session play of `l.toComp.den (impSem P)` with one outcome per call is the
play of a `Linked2.SessSpec` session from their stores. -/
def Linked2.IRToSpec (P : Profile) (l : Linked2) : Prop :=
  ∀ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance), l.exp.mod.IsInst Ie → l.imp.mod.IsInst Ii →
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      SimpleI.TypedCalls l.imp calls → calls.length = outs.length →
      Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) →
      ∃ u' π' : Silmaril.Wasm.Execution.Core.Store Nat,
        Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π'

end Silmaril.Wasm.Component.Reference
