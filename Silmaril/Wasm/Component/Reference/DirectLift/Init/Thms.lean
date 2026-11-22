module

public import Silmaril.Wasm.Component.Reference.DirectLift.Init.Defs
import Silmaril.Proofs.Wasm.Component.Reference.DirectLift.Init
import Silmaril.Proofs.Wasm.Component.Reference.DirectLift.Forward

public section

namespace Silmaril.Wasm.Component.Reference.DirectLift

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- When the two start-free Core preparations, direct wire and Core export lookup succeed,
the stock reference instantiation exists and has exactly this ready configuration. Only
one component owner is allocated; the two Core instances are local to the definition frame.
No comparison with the executable engine or fuel bound is needed. -/
theorem DirectWire.instantiates_iff {w : DirectWire} {P : Profile} {shared : Store (CanonHost (core3P P))}
    {addr : Nat} {prof : ProfileKind} {cfg : Machine.Config (core3P P) Unit} {owner : InstId}
    {exports : List (String × FuncId)} (data : w.Prepared P shared addr) :
    Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports ↔
      cfg = w.ready shared addr ∧ owner = ⟨0⟩ ∧ exports = w.exportMap :=
  Silmaril.Proofs.Wasm.Component.Reference.DirectLift.instantiates_iff data

/-- Read back any stock terminal named call after a stock direct-wire instantiation. The
wire derives the ready configuration and lift address; the `Boundary` still requires scalar
store well-formedness, a host-free typed entry, and the flat ABI restrictions. `Reports`
preserves the distinction between a Core trap/throw and an ABI rejection of a Core return. -/
theorem DirectWire.terminalReadbackOfInstantiation {w : DirectWire} {P : Profile} {I : ScalarInstance}
    {shared : Store (CanonHost (core3P P))} {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val}
    {question : I.F.Op} {prof : ProfileKind} {cfg final : Machine.Config (core3P P) Unit}
    {owner : InstId} {exports : List (String × FuncId)} {func : FuncId} {call : Nat} {out : CallOutcome}
    (data : w.Prepared P shared (I.addr question.1)) (abi : Boundary I shared x args question)
    (signature : w.liftType = liftedFt x)
    (init : Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports)
    (named : exports.lookup x.name = some func)
    (ran : Calls prof (refHost P).hr (D P) cfg ⟨call⟩ func (args.map toRefVal) final out) :
    ∃ (core : Execution.Core.Config Nat) (result : Result) (answer : I.F.Ar question),
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
      answer.toResult = result ∧ Reports x out result ∧
      core.store = Store.mapH (fun _ => 0) final.store.core ∧
      I.Activation P (Store.mapH (fun _ => 0) shared)
        [.inr (.ask question), .inr (.ans question answer)] core.store :=
  Silmaril.Proofs.Wasm.Component.Reference.DirectLift.terminalReadbackOfInstantiation
    data abi signature init named ran

/-- Construct a stock reference call at the named lift after stock instantiation, by
following the given finite Core reduction. The lifted result or specification trap is
described by `Reports`; the canonical ABI suffix leaves the final Core store intact. -/
theorem DirectWire.terminalForwardOfInstantiation {w : DirectWire} {P : Profile} {I : ScalarInstance}
    {shared : Store (CanonHost (core3P P))} {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val}
    {question : I.F.Op} {prof : ProfileKind} {cfg : Machine.Config (core3P P) Unit}
    {owner : InstId} {exports : List (String × FuncId)} {func : FuncId} {call : Nat}
    {core : Execution.Core.Config Nat} {result : Result}
    (data : w.Prepared P shared (I.addr question.1)) (abi : Boundary I shared x args question)
    (signature : w.liftType = liftedFt x)
    (init : Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports)
    (named : exports.lookup x.name = some func)
    (run : Entry.Finishes P Det.noHost
      (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result) :
    ∃ final out, Calls prof (refHost P).hr (D P) cfg ⟨call⟩ func (args.map toRefVal) final out ∧
      Reports x out result ∧ core.store = Store.mapH (fun _ => 0) final.store.core :=
  Silmaril.Proofs.Wasm.Component.Reference.DirectLift.terminalForwardOfInstantiation
    data abi signature init named run

/-- Exactly the same *terminal observations* (reported ABI outcome and mapped final
Core store) are reachable on both sides of the initialized direct wire. This is not an
equivalence of traces, divergence, or full component configurations. -/
theorem DirectWire.terminalObservationIff {w : DirectWire} {P : Profile} {I : ScalarInstance}
    {shared : Store (CanonHost (core3P P))} {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val}
    {question : I.F.Op} {prof : ProfileKind} {cfg : Machine.Config (core3P P) Unit}
    {owner : InstId} {exports : List (String × FuncId)} {func : FuncId} {call : Nat}
    {out : CallOutcome} {store : Store Nat}
    (data : w.Prepared P shared (I.addr question.1)) (abi : Boundary I shared x args question)
    (signature : w.liftType = liftedFt x)
    (init : Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports)
    (named : exports.lookup x.name = some func) :
    (∃ final, Calls prof (refHost P).hr (D P) cfg ⟨call⟩ func (args.map toRefVal) final out ∧
      store = Store.mapH (fun _ => 0) final.store.core) ↔
    (∃ (core : Execution.Core.Config Nat) (result : Result),
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
      Reports x out result ∧ store = core.store) :=
  Silmaril.Proofs.Wasm.Component.Reference.DirectLift.terminalObservationIff data abi signature init named

end Silmaril.Wasm.Component.Reference.DirectLift
