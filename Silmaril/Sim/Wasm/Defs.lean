module

public import Silmaril.Sim.Core.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs

/-!
# Wasm simulators: the bridge interface (header)

A simulator given as a real Core 3 module in a silmaril-lean store, run by
`Silmaril.Wasm.Execution.Core.Steps` in a profile `P` and a host relation `host` (the opaque
imports `mem.*`, `sys.syscall`, `nd.undef`), as a `Silmaril.Sim.Machine` (`ExportSim.toMachine`).
This is the one simulator interface of the bridge: a certificate `ExportSim.Cert K B` gives a
`Silmaril.Sim.Simulation K.toMachine B` (`Cert.simulation`), and from there the transfer theorems
of `Silmaril.Sim` (`Simulation.sem`, `Simulation.angelic`, `Simulation.reaches`), the institution's
`Silmaril.Sim.Institution.transfer` and the reduction layer (`Silmaril.Sim.Reduce.SoundSim.ofExportCert`)
apply with no further glue.

* `ExportSim C L V H`: profile, host relation, the view `get` of a store, and for every command
  `c` the export address `addr c` with its arguments `args c` (operands of `i_<form>`; `[]`
  for `step`) and the accepted results `ok c` (e.g. status `[i32 0]`).
* `ExportSim.call c s s'`: `$invoke` of `addr c` on `args c` from `s` returns accepted results
  in `s'`. **This is the one call relation** of a Wasm simulator: `toMachine`, `MethodOK` and
  the certificates all speak of it.
* `MethodOK K B R c`: every such call from a store related to a reference state `b` is backed
  by a reference step of `c` (the per-method soundness problem). Its Hoare-logic forms are
  `methodSpec` (ghost reference state) and `methodSpecU` (ghost-free); `Thms` proves
  `methodOK_of_fspecValid`, `methodOK_of_fspecValidU` and the same-module accessor form
  `methodOK_of_ctxSat`.
* `Cert K B`: relation, view and loading conditions, and `MethodOK` for every command.

Adapters with heavier imports live in sibling modules: `Silmaril.Sim.Wasm.Open` (open modules and
game-semantic import environments: `methodOK_of_moduleSat`, `methodOK_of_core`) and
`Silmaril.Sim.Wasm.FnSpec` (the store-level `Silmaril.Wasm.Verify.FnSpec`: `methodFnSpec`,
`methodOK_of_vc`). This header imports only `Silmaril.Sim.Core` and `Silmaril.Wasm.Logic.Hoare`.
-/

@[expose] public section

namespace Silmaril.Sim.Wasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)
open Silmaril.Wasm.Logic.Core (Outcome)

/-- A simulator as a Core 3 module: one export per command. -/
structure ExportSim (C L V H : Type) where
  /-- The numeric profile. -/
  P : Profile
  /-- The host relation (opaque imports). -/
  host : HostSemantics H
  /-- The view of a store (the meaning of the `get`/`modelled` exports). -/
  get : Store H → PState L V
  /-- The address of the export implementing each command. -/
  addr : C → Nat
  /-- The arguments of the call (operands). -/
  args : C → List Val
  /-- The results that count as a successful step (status codes). -/
  ok : C → List Val → Prop

namespace ExportSim

variable {C L V H : Type}

/-- A call of the export of `c` from `s` returns accepted results, leaving `s'`. -/
def call (K : ExportSim C L V H) (c : C) (s s' : Store H) : Prop :=
  ∃ (f' : Frame) (res : List Val), K.ok c res ∧
    Steps K.P K.host (invoke s (K.addr c) (K.args c)) ⟨s', f', vals res⟩

/-- **The simulator as a `Machine`**: stores, the view `get`, and the call relation. -/
def toMachine (K : ExportSim C L V H) : Machine C L V := ⟨Store H, K.get, K.call⟩

/-- The simulator as a `WasmSim` (derived; `K.toWasmSim.toMachine` is `K.toMachine` by `rfl`).
Prefer `toMachine`. -/
def toWasmSim (K : ExportSim C L V H) : WasmSim C L V := ⟨Store H, K.get, K.call⟩

/-- **Per-method soundness**: every successful call of the export of `c` from a store related
to `b` is backed by a reference step of `c` to a state related to the result. -/
def MethodOK (K : ExportSim C L V H) (B : Machine C L V) (R : Store H → B.St → Prop)
    (c : C) : Prop :=
  ∀ b s s' (f' : Frame) res, R s b → K.ok c res →
    Steps K.P K.host (invoke s (K.addr c) (K.args c)) ⟨s', f', vals res⟩ →
    ∃ b', B.step c b b' ∧ R s' b'

/-- The every-run specification of the export of `c`, with the reference state `b` as a
ghost. -/
def methodSpec (K : ExportSim C L V H) (B : Machine C L V) (R : Store H → B.St → Prop)
    (c : C) (b : B.St) : FSpec H where
  pre s args := args = K.args c ∧ R s b
  post _ _ s' o := ∀ res, o = .normal res → K.ok c res → ∃ b', B.step c b b' ∧ R s' b'

/-- The ghost-free specification (one per address, for spec contexts `Ctx`). -/
def methodSpecU (K : ExportSim C L V H) (B : Machine C L V) (R : Store H → B.St → Prop)
    (c : C) : FSpec H where
  pre s args := args = K.args c ∧ ∃ b, R s b
  post s _ s' o := ∀ res, o = .normal res → K.ok c res →
    ∀ b, R s b → ∃ b', B.step c b b' ∧ R s' b'

/-- **A certified Wasm simulator**: a relation, the view and loading conditions, and
per-method soundness (`MethodOK`) for every command. It gives `Simulation K.toMachine B`
(`Cert.simulation`, in `Thms`). -/
structure Cert (K : ExportSim C L V H) (B : Machine C L V) where
  /-- The relation (store, reference state). -/
  R : Store H → B.St → Prop
  /-- The view shows only true values. -/
  view_le : ∀ {a b}, R a b → K.get a ⊑ B.view b
  /-- Every reference state can be loaded into a store. -/
  load : ∀ b, ∃ a, R a b ∧ K.get a = B.view b
  /-- Per-method soundness. -/
  method : ∀ c, K.MethodOK B R c

end ExportSim

end Silmaril.Sim.Wasm

end
