module

public import Silmaril.Project.Defs
public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs
public import Silmaril.Wasm.Component.InstExport.Defs
public import Silmaril.Wasm.SingleThreaded.Interface

/-!
# Standard problem shapes: component tests (instantiation-time behaviour)

Test shapes about one component binary `b : ByteArray`. Each says that `b` lowers to a component
`c : Comp Binary.CoreMod` (`Binary.parseComponent`: the verified parser, then the partial
lowering of the format `wasm.component.ir`; it rejects async functions, resources, streams and
futures, so none occur), and something about `c` read by the instantiating denotation `Comp.denI` over `Binary.coreModSemI P`: each core module runs on the
Core 3.0 engine at profile `P`, its start function at instantiation; core instances are
instantiated in program order (`Silmaril.Wasm.Component.InstSem`). This is the reading of the
binary entry point `Silmaril.Wasi.Accept.componentBytesSystemCore3I P`.

Plays are over `sigU ↠ sigUI` (component values at the interface): `askInst`/`ansInst a` are the
instantiation question and its answer (`ready`, or `fail ()` for a trap), `.inl` moves are calls of
the component's imports, `askEx q`/`ansEx q r` export calls. An instantiation trace is a list of
import calls with their answers, `Call := Σ _ : sigU.Op, Option Payload`; `instPlay tr a` is
`[inst] ++ tr ++ [a]`. A host is a function `host : sigU.Op → Option Payload` answering each
import call (a *typed* host answers with values of the import's result types).

| name | Lean | statement |
|---|---|---|
| `silmaril.shapes.component.test.instantiates` | `Instantiates b host tr` | instantiation makes the import calls `tr` in order, answered by `host`, and is `ready`; at deterministic profiles this is the only complete instantiation under `host`, and every play's import calls are a prefix of `tr`'s |
| `silmaril.shapes.component.test.inst_traps` | `InstTraps b host tr` | instantiation makes the calls `tr` and then fails as a whole (`fail ()`); at deterministic profiles, every play's import calls are a prefix of `tr`'s and, under `host`, no play is `ready` or answers an export |
| `silmaril.shapes.component.test.export_returns_after_inst` | `ExportReturnsAfterInst b host tr q v` | after the instantiation `tr`, `ready`, the export call `q` is answered `v`; at deterministic profiles every answer to `q` under `host` is `v` |

**What is quantified.** Existence: one play at **every** profile `P`. Exclusion: **every** play at
**every deterministic profile** `profile o` (every `GrowOracle o`). Plays are finite: a start
function or export call that never returns makes no move, so **divergence is not observed** by
these shapes (an exclusion statement is about the moves that do happen). The exclusion clauses
about outcomes assume the host answers as `host` does (`HostAnswers`); the clauses about which
import calls are made do not.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.ComponentTest

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- An import call of an instantiation trace: the call at the component's interface, with the
host's answer. -/
abbrev Call : Type := Σ _ : sigU.Op, Option Payload

/-- Every import call of the play `p` is answered as `host` answers it. -/
def HostAnswers (host : sigU.Op → Option Payload) (p : List (Move sigU sigUI)) : Prop :=
  ∀ m r, (.inl (.ans m r) : Move sigU sigUI) ∈ p → r = host m

/-- The trace `tr` is answered by `host`. -/
def TraceOf (host : sigU.Op → Option Payload) (tr : List Call) : Prop :=
  ∀ x ∈ tr, x.2 = host x.1

/-- **Instantiation succeeds with the ordered import trace `tr`.** `b` lowers to `c`; at every
profile,
`[inst] ++ tr ++ [ready]` is a play (with `tr` answered by `host`). At every deterministic
profile, the import calls of every play are a prefix of those of `tr`, and a complete
instantiation answered by `host` is `tr` followed by `ready`. -/
@[problem "silmaril.shapes.component.test.instantiates"
  (title := "A component instantiates, making a given ordered trace of import calls")]
def Instantiates (b : ByteArray) (host : sigU.Op → Option Payload) (tr : List Call) : Prop :=
  ∃ c, Binary.parseComponent b = .ok c ∧ TraceOf host tr ∧
  (∀ P : Profile, instPlay (F := sigU) tr .ready ∈ c.denI (Binary.coreModSemI P)) ∧
  ∀ o : GrowOracle,
    (∀ p ∈ c.denI (Binary.coreModSemI (profile o)), lowerAsks p <+: tr.map Sigma.fst) ∧
    ∀ (cs : List Call) (a : InstAns Unit),
      instPlay (F := sigU) cs a ∈ c.denI (Binary.coreModSemI (profile o)) →
        TraceOf host cs → cs = tr ∧ a = .ready

/-- **The whole instantiation traps after the import trace `tr`.** `b` lowers to `c`; at every
profile,
`[inst] ++ tr ++ [fail ()]` is a play. At every deterministic profile, the import calls of every
play are a prefix of those of `tr`, and no play answered by `host` is `ready` or answers an
export call. -/
@[problem "silmaril.shapes.component.test.inst_traps"
  (title := "A component's instantiation traps as a whole")]
def InstTraps (b : ByteArray) (host : sigU.Op → Option Payload) (tr : List Call) : Prop :=
  ∃ c, Binary.parseComponent b = .ok c ∧ TraceOf host tr ∧
  (∀ P : Profile, instPlay (F := sigU) tr (.fail ()) ∈ c.denI (Binary.coreModSemI P)) ∧
  ∀ o : GrowOracle, ∀ p ∈ c.denI (Binary.coreModSemI (profile o)),
    lowerAsks p <+: tr.map Sigma.fst ∧
      (HostAnswers host p → ansInst .ready ∉ p ∧ ∀ q r, ansEx q r ∉ p)

/-- **After the instantiation `tr`, the export call `q` returns `v`.** `b` lowers to `c`; at
every profile,
`[inst] ++ tr ++ [ready, q, v]` is a play. At every deterministic profile, every answer to `q`
in a play answered by `host` is `v`. -/
@[problem "silmaril.shapes.component.test.export_returns_after_inst"
  (title := "A component export returns a given value after instantiation")]
def ExportReturnsAfterInst (b : ByteArray) (host : sigU.Op → Option Payload)
    (tr : List Call) (q : sigU.Op) (v : Option Payload) : Prop :=
  ∃ c, Binary.parseComponent b = .ok c ∧ TraceOf host tr ∧
  (∀ P : Profile, instPlay (F := sigU) tr .ready ++ [askEx q, ansEx q v] ∈
    c.denI (Binary.coreModSemI P)) ∧
  ∀ o : GrowOracle, ∀ p ∈ c.denI (Binary.coreModSemI (profile o)), HostAnswers host p →
    ∀ r, ansEx q r ∈ p → r = v

end Silmaril.Project.Shapes.ComponentTest

end
