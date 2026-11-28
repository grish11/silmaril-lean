module

public import Silmaril.Wasm.V1.Execution.Callout

/-!
# One checked direct V1 host call

The site starts at a direct call in the active caller frame. Its ordered
arguments are a suffix above saved operands in a native sequence context.
The embedding supplies the returning stores, results, traps, and divergence.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.V1

open Execution.Runtime (Callout Frame FuncAddr Result Value)
open Wasm.V1.Execution

structure Site (H : Type) where
  index : FuncIdx
  address : FuncAddr
  signature : Wasm.V1.FuncType
  target : H

def Site.source {H : Type} (site : Site H) (s : Store H) (caller : Frame)
    (saved args : List Value) (tail : List Admin) : Config H :=
  ⟨s, caller, values (saved ++ args) ++ .source (.call site.index) :: tail⟩

def Site.pending {H : Type} (site : Site H) (s : Store H) (caller : Frame)
    (saved args : List Value) (tail : List Admin) : Config H :=
  ⟨s, caller, values (saved ++ args) ++ .invoke site.address :: tail⟩

def Site.callout {H : Type} (site : Site H) (saved args : List Value) (tail : List Admin) :
    Callout H Wasm.V1.Instr :=
  ⟨.seq saved .hole tail, site.address, site.signature, site.target, args⟩

def resumed {H : Type} (s' : Store H) (caller : Frame)
    (saved : List Value) (tail : List Admin) (r : Result) : Config H :=
  ⟨s', caller, values saved ++ result r ++ tail⟩

structure Site.Checked {H : Type} (site : Site H) (s : Store H) (caller : Frame)
    (args : List Value) : Prop where
  resolved : caller.module.funcs[site.index.toNat]? = some site.address
  allocated : s.funcs[site.address.value]? = some (.host site.signature site.target)
  arguments : args.map Value.type = site.signature.params
  scalar : site.signature.results.length ≤ 1

def ResultTyped (types : List NumType) : Result → Prop
  | .values payload => payload.map Value.type = types
  | .trap => True

/-- Obligations for all returning outcomes at these actual inputs. A trap
also returns a store. The relation on stores is supplied by the embedding. -/
def Site.ReturnContract {H : Type} (site : Site H) (host : HostSemantics H)
    (preserves : Store H → Store H → Prop) (s : Store H) (args : List Value) : Prop :=
  ∀ s' r, host site.target s args (.returned s' r) →
    ResultTyped site.signature.results r ∧ preserves s s'

end Silmaril.Wasm.Institution.Operational.HostCall.V1
