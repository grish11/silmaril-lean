module

public import Silmaril.Wasm.Component.Reference.DirectLift.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.DirectLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- A flat root: the consumer receives the provider instance under one Core import-module
name. The root directly lifts one named consumer function, with default canonical options.
The component function type uses only primitive syntax (no type indices or resources). -/
structure DirectWire where
  provider : Silmaril.Wasm.Module
  consumer : Silmaril.Wasm.Module
  importModule : String
  coreName : String
  exportName : String
  params : List (String × Syntax.Prim)
  result : Option Syntax.Prim

def DirectWire.signature (w : DirectWire) : Syntax.FuncType :=
  { params := w.params.map fun (name, ty) => (name, .prim ty), result := w.result.map .prim }

def DirectWire.component (w : DirectWire) : Core3Component :=
  [.coreModule w.provider, .coreInstance (.instantiate 0 []),
   .coreModule w.consumer, .coreInstance (.instantiate 1 [(w.importModule, 0)]),
   .alias (.coreExport 1 w.coreName .func), .type (.func w.signature),
   .canon (.lift 0 [] 0), .export_ { name := w.exportName } ⟨.func, 0⟩ none]

def DirectWire.liftType (w : DirectWire) : Types.FuncType RtId :=
  ⟨w.params.map fun (name, ty) => (name, primType ty), w.result.map primType, false⟩

def DirectWire.exportMap (w : DirectWire) : List (String × FuncId) := [(w.exportName, ⟨0⟩)]

noncomputable def DirectWire.providerFrame (w : DirectWire) {P : Profile} (providerInst : (core3P P).Inst) :
    Frame (core3P P) :=
  { (Frame.empty : Frame (core3P P)) with
    coreModules := [w.provider, w.consumer]
    coreInstances := [(core3P P).exports providerInst] }

/-- The individual Core preparations and the reference import/export lookups succeed.
`none` in each preparation ensures it allocates without running a start activation.
This is not a premise about a ready component configuration. -/
structure DirectWire.Prepared (w : DirectWire) (P : Profile)
    (shared : Store (CanonHost (core3P P))) (addr : Nat) where
  providerStore : Store (CanonHost (core3P P))
  providerInst : (core3P P).Inst
  consumerInst : (core3P P).Inst
  resolvedImports : List (core3P P).ExternVal
  providerImports : (core3P P).importTypes w.provider = []
  provide : (core3P P).prepare? ((core3P P).empty _) w.provider [] =
    some (providerStore, providerInst, none)
  resolve : coreImportsFor? providerStore w.consumer [(w.importModule, 0)]
    (w.providerFrame providerInst) = some resolvedImports
  consume : (core3P P).prepare? providerStore w.consumer resolvedImports =
    some (shared, consumerInst, none)
  lookup : lookupExport? ((core3P P).exports consumerInst) w.coreName = some (.func addr)

def emptyGarb (P : Profile) : Garb P := ⟨[], [], [], [], [], [], []⟩

def DirectWire.ready (w : DirectWire) {P : Profile} (shared : Store (CanonHost (core3P P)))
    (addr : Nat) : Machine.Config (core3P P) Unit :=
  readyCfg shared {} [.lifted addr w.liftType {} ⟨0⟩] (emptyGarb P)

end Silmaril.Wasm.Component.Reference.DirectLift
