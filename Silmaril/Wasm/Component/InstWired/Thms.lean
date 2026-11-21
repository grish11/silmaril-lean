module

public import Silmaril.Wasm.Component.InstWired.Defs
import Silmaril.Proofs.Wasm.Component.InstSem.WiredEngine

/-!
# Instantiation of import-wired components, node by node: theorems

All proved, for every core semantics with an instantiation phase `C`. Proofs in
`Silmaril.Proofs.Wasm.Component.InstSem.{Unzip,Wired,WiredEngine}` (the converse of the
instantiation lemmas of `InstSem.Run`: complete rounds of composites, handlers, pairings and
copycat taken apart).

* `nodesInst_of_denI`: **in an import-wired component** (`ImportWired I.length ps`: no core
  instance calls another), every instantiation play `instPlay cs a` of
  `Comp.denI C (Comp.mk I (coreNodes ps) xs)` is `NodesInst C I.length ps cs a`: the nodes are
  instantiated in order, each node's own instantiation play (its import calls wired over the
  imports) contributing its calls to `cs`, and the first failure is the answer;
* `NodesInst.fail_nil`: a failed instantiation without calls fails at one node `k`: the nodes
  before `k` are ready and node `k` fails, each without a call;
* `coreNodeI_engine_nil`: at an engine semantics (`Param.engineSemI`, e.g. `Binary.coreModSemI`),
  a node's instantiation play without calls is a run of its engine instance (`EngineInst`: no
  instance, no start function, or a start run returning or trapping), whose import calls the
  wiring answers at once (a trap of an argument transformation).

**Scope.** Instantiation plays only (no export call after `ready`); core nodes only (no nested
component), each wired to the imports alone. Nothing here concerns the reference machine.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Inst

variable {M : Type} [CoreModule M]

/-- **The instantiation plays of an import-wired component, node by node.** -/
theorem nodesInst_of_denI {C : CoreSemI M} {I : Iface} {ps : List (M × List Impl)}
    {xs : List Export} (hw : ImportWired I.length ps)
    {cs : List (Σ _ : sigU.Op, Option Payload)} {a : InstAns Unit}
    (h : instPlay (F := sigU) cs a ∈ (Comp.mk I (coreNodes ps) xs).denI C) :
    NodesInst C I.length ps cs a :=
  Silmaril.Proofs.Wasm.Component.InstSem.nodesInst_of_denI hw h

/-- **A failed instantiation without calls fails at one node**, the nodes before it ready, each
without a call. -/
theorem NodesInst.fail_nil {C : CoreSemI M} {n : Nat} {ps : List (M × List Impl)}
    (h : NodesInst C n ps [] (.fail ())) :
    ∃ k, ∃ hk : k < ps.length,
      (∀ j (hj : j < k), instPlay (F := sigU) [] .ready ∈
        coreNodeI C n (ps[j]'(by omega)).1 (ps[j]'(by omega)).2) ∧
      instPlay (F := sigU) [] (.fail ()) ∈ coreNodeI C n ps[k].1 ps[k].2 :=
  (Silmaril.Proofs.Wasm.Component.InstSem.nodesInst_fail_nil h rfl).2 rfl

/-- **A node's instantiation without calls, at an engine semantics**, is a run of its engine
instance whose import calls the wiring answers at once. -/
theorem coreNodeI_engine_nil {E : Reference.Engine} {emb : M → E.Module} {n : Nat} {m : M}
    {args : List Impl} {a : InstAns Unit}
    (h : instPlay (F := sigU) [] a ∈ coreNodeI (Param.engineSemI E M emb) n m args) :
    ∃ ys : List (Σ _ : (sigN (CoreModule.imports m).length).Op, Option Payload),
      EngineInst E (Param.instOfI E (emb m) (CoreModule.imports m) (CoreModule.exports m))
        (CoreModule.imports m) ys a ∧
      ∀ y ∈ ys, implsN n args (CoreModule.imports m).length y.1 = .pure y.2 :=
  Silmaril.Proofs.Wasm.Component.InstSem.coreNodeI_engine_nil h

end Silmaril.Wasm.Component
