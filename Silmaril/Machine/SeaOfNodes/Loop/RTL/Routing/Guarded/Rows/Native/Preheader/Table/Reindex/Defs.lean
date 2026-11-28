module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Defs

/-! Typed capture maps for checked dependent preheaders. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}

/-- Reindex capture reads in each producer's typed prefix. -/
def mapCaptureFlow (mapping : InputMap arity) : {past sigs : List (List PortTy)} →
    Dataflow WordOp (wordPorts arity) past sigs → Dataflow WordOp (wordPorts arity) past sigs
  | _, _, .nil => .nil
  | _, _, .cons op args rest => .cons op (mapping.column args) (mapCaptureFlow mapping rest)

/-- Map capture reads in the preheader and entry column. The checked
header reads its bank and local producers. Its backedge and exit stay in
their original scope and occurrence. -/
def mapCaptures (mapping : InputMap arity) (g : SourceWithEntry arity entrySigs sigs) :
    SourceWithEntry arity entrySigs sigs :=
  { g with
    preheader := mapCaptureFlow mapping g.preheader
    phiInputs
      | .entry => mapping.column (g.phiInputs .entry)
      | .backedge => g.phiInputs .backedge }

abbrev reindexFlow (perm : InputPermutation arity) {past sigs : List (List PortTy)}
    (flow : Dataflow WordOp (wordPorts arity) past sigs) : Dataflow WordOp (wordPorts arity) past sigs :=
  mapCaptureFlow (fun i => perm i) flow

abbrev reindexCaptures (perm : InputPermutation arity) (g : SourceWithEntry arity entrySigs sigs) :
    SourceWithEntry arity entrySigs sigs :=
  mapCaptures (fun i => perm i) g

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
