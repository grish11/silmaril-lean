module

public import Silmaril.Wasm.Component.InstSem.Defs
public import Silmaril.Wasm.Component.InstEngine.Defs

/-!
# Instantiation of components whose core instances call only the imports

`Comp.denI C c` (`Silmaril.Wasm.Component.InstSem`) instantiates the nodes of `c` in program
order through nested environments (`extI`). This module names the fragment in which that
nesting carries no interaction between core instances during instantiation, and the
node-by-node description of an instantiation play there:

* `coreNodes ps`: the core nodes `.core m args` for `(m, args) ∈ ps`;
* `ImportWired n ps`: every import of every core node is wired (`ScopedList n`) to one of the
  first `n` functions of the environment, i.e. to an import of a component with `n` imports, or
  traps: no core instance calls another core instance;
* `NodesInst C n ps w a`: **the instantiation of the nodes `ps`, node by node**, making the calls
  `w` (to the component's imports, each with its answer) and answering `a`: the nodes before a
  failure are instantiated in order, each node's instantiation play (`coreNodeI C n m args`, its
  import calls wired over the `n` imports) contributing its calls; a failure of a node is the
  answer, and the later nodes are not asked.

For an engine semantics (`Param.engineSemI`), a node's instantiation is a run of its engine
instance (`EngineInst`):

* `EngineInst E I imps cs a`: the engine instance `I` (before its start function) answers `inst`
  with `a` after the import calls `cs`: `ready` when it has an instance and either no start
  function (and no call) or a start run (`Param.StartRunI`) with the calls `cs` returning values;
  `fail` when it has no instance (and no call) or a start run with the calls `cs` trapping.

`InstWired.Thms`: in the fragment, an instantiation play of `Comp.denI C (Comp.mk I (coreNodes
ps) xs)` is exactly `NodesInst C I.length ps` (both directions, every core semantics `C`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Inst

variable {M : Type} [CoreModule M]

/-- The core nodes `.core m args` for `(m, args) ∈ ps`. -/
def coreNodes (ps : List (M × List Impl)) : List (Node M) := ps.map fun p => .core p.1 p.2

/-- **Import-wired nodes**: every import of every core node is wired to one of the first `n`
functions of the environment (the imports of a component with `n` imports) or traps. -/
def ImportWired (n : Nat) (ps : List (M × List Impl)) : Prop := ∀ p ∈ ps, ScopedList n p.2

/-- **The instantiation of import-wired nodes, node by node**, with the calls `w` to the `n`
imports and the answer `a`: no node is ready at once; a node is asked only after the nodes
before it are ready, and its instantiation play (its import calls wired over the imports)
contributes its calls; the first failure is the answer, and later nodes are not asked. -/
inductive NodesInst (C : CoreSemI M) (n : Nat) :
    List (M × List Impl) → List (Σ _ : sigU.Op, Option Payload) → InstAns Unit → Prop
  /-- No node: ready, no call. -/
  | nil : NodesInst C n [] [] .ready
  /-- After a failure, a later node is not asked. -/
  | failed {pre : List (M × List Impl)} {x : M × List Impl}
      {w : List (Σ _ : sigU.Op, Option Payload)} {r : Unit} :
      NodesInst C n pre w (.fail r) → NodesInst C n (pre ++ [x]) w (.fail r)
  /-- After the nodes before it are ready, a node instantiates with the calls `w'`. -/
  | step {pre : List (M × List Impl)} {x : M × List Impl}
      {w w' : List (Σ _ : sigU.Op, Option Payload)} {a : InstAns Unit} :
      NodesInst C n pre w .ready → instPlay (F := sigU) w' a ∈ coreNodeI C n x.1 x.2 →
      NodesInst C n (pre ++ [x]) (w ++ w') a

/-- **The instantiation of an engine instance**: `I` answers `inst` with `a` after the import
calls `cs` (each with its answer). -/
def EngineInst (E : Reference.Engine) (I : Option (Param.IInstance E)) (imps : CoreIface)
    (cs : List (Σ _ : (sigN imps.length).Op, Option Payload)) : InstAns Unit → Prop
  | .ready => ∃ J, I = some J ∧ ((J.start = none ∧ cs = []) ∨
      ∃ f c' ys, J.start = some f ∧ Param.StartRunI E imps (J.store, E.invoke f []) cs c' ∧
        E.status c'.1 c'.2 = Engine.Status.returned (.values ys))
  | .fail _ => (I = none ∧ cs = []) ∨
      ∃ J f c', I = some J ∧ J.start = some f ∧
        Param.StartRunI E imps (J.store, E.invoke f []) cs c' ∧
        E.status c'.1 c'.2 = Engine.Status.returned .trap

end Silmaril.Wasm.Component
