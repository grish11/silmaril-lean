module

public import Silmaril.Wasm.Component.InstSem.Defs

/-!
# The export phase of an instantiable strategy

`Comp.denI C c` (`Silmaril.Wasm.Component.InstSem`) is a strategy over the instantiable
interface `sigUI`: its plays begin with the instantiation `inst`, the import calls the start
functions make, and the answer `ready` or `fail ()`. Statements made over start-free strategies
(`Strategy sigU sigU`, e.g. the WASI views and acceptors of `Silmaril.Wasi.Component`) need the
**export phase**: what the component does after a successful instantiation.

* `exportPhase σ : Strategy E F`: the plays `p` such that `instPlay cs .ready ++ p` (lifted to
  export calls by `Wasm.Game.liftMove`) is a play of `σ` for **some** instantiation calls `cs`
  (each import call of the start functions with an answer of the environment), closed under
  the strategy laws (`Strategy.generate`). So the export phase is the union, over every
  successful instantiation, of what follows it. A strategy whose instantiation never succeeds
  has an export phase that never answers. The import calls made *during* instantiation are not
  moves of the export phase: an observation of them is an observation of `σ` itself.
* `Comp.denX C c = exportPhase (c.denI C)`: the export phase of a component.
* `Comp.AllCore P c`: every core module of `c` (nested components included) satisfies `P`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.Game (liftMove)

/-- **The export phase of an instantiable strategy**: the plays after some successful
instantiation (`[inst] ++ cs ++ [ready]`, for any calls `cs`), as plays of `E ↠ F`. -/
def exportPhase {E F : Sig.{0}} {R : Type} (σ : Strategy E (F.withInst R)) : Strategy E F :=
  Strategy.generate {p | ∃ cs : List (Σ m : E.Op, E.Ar m),
    instPlay (F := F) cs .ready ++ p.map liftMove ∈ σ}

variable {M : Type} [CoreModule M]

/-- **The export phase of a component**: its plays after a successful instantiation. -/
def Comp.denX (C : CoreSemI M) (c : Comp M) : Strategy sigU sigU := exportPhase (c.denI C)

mutual
/-- Every core module of the component satisfies `P`. -/
def Comp.AllCore (P : M → Prop) : Comp M → Prop
  | .mk _ ns _ => nodesAllCore P ns

/-- Every core module of the nodes satisfies `P`. -/
def nodesAllCore (P : M → Prop) : List (Node M) → Prop
  | [] => True
  | n :: ns => Node.AllCore P n ∧ nodesAllCore P ns

/-- Every core module of the node satisfies `P`. -/
def Node.AllCore (P : M → Prop) : Node M → Prop
  | .core m _ => P m
  | .inst c _ => Comp.AllCore P c
end

end Silmaril.Wasm.Component
