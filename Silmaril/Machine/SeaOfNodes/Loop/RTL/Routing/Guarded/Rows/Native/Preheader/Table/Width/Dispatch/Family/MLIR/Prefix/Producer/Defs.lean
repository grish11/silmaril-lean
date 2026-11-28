module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Defs

/-! Translate the typed producer schedule of the checked RTL word family to the CF bank dialect. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Port Origin Wires extend)
open Silmaril.MLIR.Arith (Width)

def sort : ValueSort Unit → ValueSort Width
  | .data _ => .data i64
  | .predicate => .predicate

def portType : PortTy → Diamond.Ty Width
  | .value s => .value (sort s)
  | .control k => .control k
  | .state s => nomatch s

abbrev ports (types : List PortTy) := types.map portType
abbrev table (types : List (List PortTy)) := types.map ports

theorem ports_data (types : List (ValueSort Unit)) :
    ports (dataPorts types) = dataPorts (types.map sort) := by
  simp only [List.map_map]; rfl

theorem wordPorts_eq (n : Nat) : ports (wordPorts n) = dataPorts (Loop.MLIR.CF.inputSorts (wordsTy n)) := by
  simp [Loop.MLIR.CF.inputSorts, portType, sort, List.map_replicate]

theorem headerPorts_eq (captures bank : Nat) :
    ports (wordPorts captures ++ wordPorts bank) =
      Loop.headerPorts (Loop.MLIR.CF.inputSorts (wordsTy captures)) (Loop.MLIR.CF.inputSorts (wordsTy bank)) := by
  change (wordPorts captures ++ wordPorts bank).map portType = _
  rw [List.map_append]
  exact congrArg₂ List.append (wordPorts_eq captures) (wordPorts_eq bank)

theorem table_snoc (past : List (List PortTy)) (row : List PortTy) :
    table (past ++ [row]) = table past ++ [ports row] :=
  List.map_append

theorem table_extend (past sigs : List (List PortTy)) :
    table (extend past sigs) = extend (table past) (table sigs) := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    change table (extend (past ++ [head]) tail) = extend (table past ++ [ports head]) (table tail)
    rw [ih, table_snoc]

def port {ps : List PortTy} {t : PortTy} : Port ps t → Port (ports ps) (portType t)
  | .head => .head
  | .tail p => .tail (port p)

abbrev index {past : List (List PortTy)} (i : Fin past.length) : Fin (table past).length :=
  i.cast (List.length_map ..).symm

def resultPort {past : List (List PortTy)} {t : PortTy} (i : Fin past.length) (p : Port past[i] t) :
    Port (table past)[index i] (portType t) :=
  (List.getElem_map (f := ports) (l := past) (i := i.val) (h := (index i).isLt)).symm ▸ port p

def origin {args : List PortTy} {past : List (List PortTy)} {t : PortTy} :
    Origin args past t → Origin (ports args) (table past) (portType t)
  | .arg p => .arg (port p)
  | .output i p => .output (index i) (resultPort i p)

def column {args outs : List PortTy} {past : List (List PortTy)} :
    Wires args past outs → Wires (ports args) (table past) (ports outs)
  | .nil => .nil
  | .cons wire rest => .cons (origin wire) (column rest)

/-- Use the existing CF symbols for the common word profile. The target
predicate is i1 and the two arithmetic operands keep their original order. -/
def opcode {ins : List (ValueSort Unit)} {out : ValueSort Unit} :
    WordOp ins out → Option (Loop.MLIR.CF.Op (ins.map sort) (sort out))
  | .const bits => some (.arithmetic (.constant bits))
  | .add => some (.arithmetic (.binary .addi))
  | .sub => some (.arithmetic (.binary .subi))
  | .slt => some (.slt i64)
  | .eq | .ne => none

/-- Translate in producer order, retaining all argument and output positions. -/
def flow {args : List PortTy} : {past sigs : List (List PortTy)} →
    Dataflow WordOp args past sigs →
    Option (Dataflow Loop.MLIR.CF.Op (ports args) (table past) (table sigs))
  | _, _, .nil => some .nil
  | past, _, .cons (ins := ins) (out := out) op args next => do
    let target ← opcode op
    let tail ← flow next
    let suffix : Dataflow Loop.MLIR.CF.Op _ (table past ++ [[.value (sort out)]]) _ :=
      table_snoc past [.value out] ▸ tail
    pure (.cons target (ports_data ins ▸ column args) suffix)

variable {captures bank : Nat} {entrySigs sigs : List (List PortTy)}

def entryFlow (g : Width.Source captures bank entrySigs sigs) :
    Option (Dataflow Loop.MLIR.CF.Op (dataPorts (Loop.MLIR.CF.inputSorts (wordsTy captures))) [] (table entrySigs)) :=
  (flow g.preheader).map fun target => wordPorts_eq captures ▸ target

def headerFlow (g : Width.Source captures bank entrySigs sigs) :
    Option (Dataflow Loop.MLIR.CF.Op
      (Loop.headerPorts (Loop.MLIR.CF.inputSorts (wordsTy captures)) (Loop.MLIR.CF.inputSorts (wordsTy bank)))
      [] (table sigs)) :=
  (flow g.header).map fun target => headerPorts_eq captures bank ▸ target

def headerOrigin {t : PortTy}
    (wire : Origin (wordPorts captures ++ wordPorts bank) (extend [] sigs) t) :
    Origin (Loop.headerPorts (Loop.MLIR.CF.inputSorts (wordsTy captures)) (Loop.MLIR.CF.inputSorts (wordsTy bank)))
      (extend [] (table sigs)) (portType t) :=
  headerPorts_eq captures bank ▸ table_extend [] sigs ▸ origin wire

def graph (g : Width.Source captures bank entrySigs sigs) :
    Option (MLIR.Program captures bank (table entrySigs) (table sigs)) := do
  let pre ← entryFlow g
  let head ← headerFlow g
  let initial := wordPorts_eq captures ▸ table_extend [] entrySigs ▸ wordPorts_eq bank ▸
    column (g.phiInputs .entry)
  let feedback := headerPorts_eq captures bank ▸ table_extend [] sigs ▸ wordPorts_eq bank ▸
    column (g.phiInputs .backedge)
  pure { preheader := pre, header := head
         phiInputs := fun edge => match edge with | .entry => initial | .backedge => feedback
         predicate := headerOrigin g.predicate, result := headerOrigin g.result }

/-- Translate the declared live origins once, retaining their order and identity. -/
def live (words : List (HeaderWord captures bank sigs)) : Live captures bank (table sigs) :=
  words.map headerOrigin

def liveOrigin (origins : List (HeaderWord captures bank sigs))
    (i : Fin (liveRegs (live origins)).length) : HeaderWord captures bank sigs :=
  origins[i.val]'(by
    have bound := i.isLt
    change i.val < ((origins.map headerOrigin).map (fun wire => register wire.address)).length at bound
    simpa only [List.length_map] using bound)

variable {old new tests : Nat}

/-- Successful translation ties the checked RTL program, the actual CF lowering
and the extracted explicit-Φ columns to a single native schedule. -/
structure Compiled (mapping : InputMap old new) (source : Family.Source old old entrySigs sigs tests)
    (origins : List (HeaderWord new old sigs)) where
  program : MLIR.Program new old (table entrySigs) (table sigs)
  translated : graph (mapCaptures mapping source).primary = some program
  rtl : Silmaril.Machine.RTL.SSA.Prog Reg
  accepted : Family.lowerChecked mapping source = some rtl
  plan : Plan (lowerFunc (mapCaptures mapping source)) (liveRegs (live origins)) old tests
  phi : Phi.Checked (lowerFunc (mapCaptures mapping source)) tests

/-- A prefix of native feedback transfers from a carried bank. -/
inductive Feedbacks (source : Family.Source captures bank entrySigs sigs tests) (input : WordTuple captures) :
    List (Fin (tests + 1)) → WordTuple bank → WordTuple bank → Prop
  | stop (carried) : Feedbacks source input [] carried carried
  | visit {slot slots carried next finish} (taken : source.step input carried = .inr (slot, next))
      (rest : Feedbacks source input slots next finish) :
      Feedbacks source input (slot :: slots) carried finish

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer
