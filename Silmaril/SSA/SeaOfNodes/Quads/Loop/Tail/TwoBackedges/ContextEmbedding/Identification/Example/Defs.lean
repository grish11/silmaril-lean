module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

/-! Fold two read-only i8 captures into one, while keeping the output register writable. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (word width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

abbrev old : EntrySignature := { regs := [.predicate, .predicate, word, word, word] }
abbrev new : EntrySignature := { regs := [.predicate, .predicate, word, word] }

def identify : PortMap old new := fun _ => fun
  | .head => .head
  | .tail .head => .tail .head
  | .tail (.tail .head) => .tail (.tail .head)
  | .tail (.tail (.tail .head)) => .tail (.tail .head)
  | .tail (.tail (.tail (.tail .head))) => .tail (.tail (.tail .head))

def aliasesWrite : PortMap old new := fun t => fun
  | .tail (.tail (.tail (.tail .head))) => .tail (.tail .head)
  | p => identify t p

def lhs : Port (dataPorts old.regs) (.value word) := .tail (.tail .head)
def rhs : Port (dataPorts old.regs) (.value word) := .tail (.tail (.tail .head))
def output : Port (dataPorts old.regs) (.value word) := .tail (.tail (.tail (.tail .head)))

def originalProgram : Program Op old.regs word where
  preheader := [⟨_, _, output, .arithmetic (.binary .addi), .cons lhs (.cons rhs .nil)⟩]
  header := []
  again := .head
  select := .tail .head
  result := output
  feedback side :=
    let stop : Quad Op old.regs := ⟨_, _, .head, .ult width, .cons lhs (.cons lhs .nil)⟩
    if side then [stop, ⟨_, _, output, .arithmetic (.constant 99), .nil⟩] else [stop]

def contract (right : Fact Word (.value word)) : EntryFacts old.regs :=
  .cons .overdefined (.cons (.constant ⟨true⟩) (.cons (.constant (7 : Word width))
    (.cons right (.cons .overdefined .nil))))

def original : Except SCCP.Dispatch.Refusal (AdmittedAt old width) :=
  @admit _ _ old.bankEq originalProgram (contract .overdefined)

def conflicting : Except SCCP.Dispatch.Refusal (AdmittedAt old width) :=
  @admit _ _ old.bankEq originalProgram (contract (.constant (8 : Word width)))

/-- Once the two captures are identified, the contracted SCCP solution can
prove this header exits. The existing singleton checker then refuses. -/
def changesAdmission : Except SCCP.Dispatch.Refusal (AdmittedAt old width) :=
  let source := { originalProgram with
    header := [⟨_, _, .head, .ult width, .cons lhs (.cons rhs .nil)⟩] }
  @admit _ _ old.bankEq source (contract .overdefined)

def input (value : Word width) (side : Bool) : Valuation new :=
  .cons ⟨true⟩ (.cons ⟨side⟩ (.cons value (.cons (0 : Word width) .nil)))

def refusal (map : PortMap old new) (admission : Except SCCP.Dispatch.Refusal (AdmittedAt old width)) :
    Option Refusal :=
  admission.toOption.bind fun p =>
    match compile map p with
    | .error reason => some reason
    | .ok _ => none

/-- Native runs at the pulled-back input, alongside the actual emitted CF and numbered runs. -/
def run (side : Bool) : Option (Option Nat × Option Nat × Option Nat) := do
  let admitted ← original.toOption
  let program ← (compile identify admitted).toOption
  let values := input 7 side
  let source := @Admitted.source _ _ old.bankEq admitted
  return ((source.source.runFrom model 5 0 (reduct identify values)).map BitVec.toNat,
    (program.artifacts.cf.run evalOp (if side then 6 else 7) (encodeValues values)).map
      (fun env => (env.get .here).toNat),
    (program.artifacts.numbered.2.run (Join.model model) 1 values).map
      (fun packet => (packet.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example
