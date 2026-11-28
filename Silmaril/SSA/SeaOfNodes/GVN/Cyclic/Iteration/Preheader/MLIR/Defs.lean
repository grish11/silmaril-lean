module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.Defs

/-! Retarget the admitted native wrapping-word loop to the typed mixed CF emitter. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR

open Builder.Preheader (Native)
open Diamond (Dataflow Val ValueSort dataPorts)
open Pure.SubZero (Opcode model word)
open RVSDG (Locals Origin Port Tuple Wires extend)
open SeaOfNodes.MLIR (Word)
open Loop.MLIR.CF.Mixed (Widths)
open Silmaril.MLIR.Arith (Width)

def i64 : Width := ⟨64, by decide⟩

def retargetSort : ValueSort Unit → ValueSort Width
  | .predicate => .predicate
  | .data _ => .data i64

def retargetTy : Diamond.Ty Unit → Diamond.Ty Width
  | .value s => .value (retargetSort s)
  | .control n => .control n
  | .state impossible => nomatch impossible

abbrev ports (ps : List (Diamond.Ty Unit)) := ps.map retargetTy
abbrev bindings (ps : List (List (Diamond.Ty Unit))) := ps.map ports

theorem ports_data (sorts : List (ValueSort Unit)) :
    ports (dataPorts sorts) = dataPorts (sorts.map retargetSort) := by
  simp only [ports, dataPorts, List.map_map]
  rfl

theorem bindings_extend (past sigs : List (List (Diamond.Ty Unit))) :
    bindings (extend past sigs) = extend (bindings past) (bindings sigs) := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    simp only [extend, bindings, List.map_cons] at *
    simpa only [List.map_append, List.map_singleton] using ih (past ++ [head])

def port {ps : List (Diamond.Ty Unit)} {t : Diamond.Ty Unit} :
    Port ps t → Port (ports ps) (retargetTy t)
  | .head => .head
  | .tail inner => .tail (port inner)

def index {past : List (List (Diamond.Ty Unit))} (i : Fin past.length) :
    Fin (bindings past).length :=
  ⟨i.val, by simpa only [bindings, List.length_map] using i.isLt⟩

theorem slot_eq {past : List (List (Diamond.Ty Unit))} (i : Fin past.length) :
    ports past[i] = (bindings past)[index i] := by
  exact (List.getElem_map (f := ports) (l := past)).symm

def origin {args : List (Diamond.Ty Unit)} {past : List (List (Diamond.Ty Unit))} {t : Diamond.Ty Unit} :
    Origin args past t → Origin (ports args) (bindings past) (retargetTy t)
  | .arg p => .arg (port p)
  | .output i p => .output (index i) (slot_eq i ▸ port p)

def wires {args packet : List (Diamond.Ty Unit)} {past : List (List (Diamond.Ty Unit))} :
    Wires args past packet → Wires (ports args) (bindings past) (ports packet)
  | .nil => .nil
  | .cons head tail => .cons (origin head) (wires tail)

def value {t : Diamond.Ty Unit} : Val model.value t → Val Word (retargetTy t) :=
  match t with
  | .value .predicate => id
  | .value (.data ()) => id
  | .control _ => id
  | .state impossible => nomatch impossible

def values {ps : List (Diamond.Ty Unit)} :
    Tuple (Val model.value) ps → Tuple (Val Word) (ports ps)
  | .nil => .nil
  | .cons head tail => .cons (value head) (values tail)

def sourceInput {sorts : List (ValueSort Unit)} (input : Tuple (Val model.value) (dataPorts sorts)) :
    Tuple (Val Word) (dataPorts (sorts.map retargetSort)) :=
  ports_data sorts ▸ values input

/-- The existing CF arithmetic model has constants, addition and
multiplication. Refuse subtraction at its actual binding. -/
def opcode? {ins : List (ValueSort Unit)} {out : ValueSort Unit} :
    Opcode ins out → Option (Loop.MLIR.CF.Op (ins.map retargetSort) (retargetSort out))
  | .literal bits => some (.arithmetic (.constant bits))
  | .add => some (.arithmetic (.binary .addi))
  | .mul => some (.arithmetic (.binary .muli))
  | .sub => none

def flow? {args : List (Diamond.Ty Unit)} :
    {past sigs : List (List (Diamond.Ty Unit))} → Dataflow Opcode args past sigs →
    Option (Dataflow Loop.MLIR.CF.Op (ports args) (bindings past) (bindings sigs))
  | _, _, .nil => some .nil
  | past, _, .cons (ins := ins) (out := out) op operands rest => do
    let mapped ← opcode? op
    let tail ← flow? rest
    have scope : bindings (past ++ [[.value out]]) = bindings past ++ [[.value (retargetSort out)]] :=
      List.map_append ..
    pure (.cons mapped (ports_data ins ▸ wires operands) (scope ▸ tail))

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Diamond.Ty Unit))}

abbrev InputWidths (inputs : List (ValueSort Unit)) := Widths (inputs.map retargetSort)

/-- Encode captures in their original order, with predicates as i1. -/
def inputEnv (input : Tuple (Val model.value) (dataPorts inputs)) :
    Silmaril.MLIR.Arith.Env (InputWidths inputs) :=
  SeaOfNodes.MLIR.Lowering.encodeValues (sourceInput input)

abbrev Retargeted (inputs carried : List (ValueSort Unit)) (entrySigs headerSigs : List (List (Diamond.Ty Unit))) :=
  Loop.MLIR.CF.Mixed.Program (inputs.map retargetSort) (carried.map retargetSort) i64
    (bindings entrySigs) (bindings headerSigs)

theorem header_ports (inputs carried : List (ValueSort Unit)) :
    ports (Loop.headerPorts inputs carried) =
      Loop.headerPorts (inputs.map retargetSort) (carried.map retargetSort) := by
  simp only [Loop.headerPorts, ports, List.map_append]
  rw [← ports_data, ← ports_data]

/-- Retarget all primitive and observation ports. The Φ occurrence order
and absolute producer numbers remain the original ones. -/
def retarget? (g : Native inputs carried entrySigs headerSigs word) :
    Option (Retargeted inputs carried entrySigs headerSigs) := do
  let preheader ← flow? g.preheader
  let header ← flow? g.header
  pure {
    preheader := ports_data inputs ▸ preheader
    header := header_ports inputs carried ▸ header
    phiInputs
      | .entry => ports_data inputs ▸ bindings_extend [] entrySigs ▸ ports_data carried ▸ wires (g.phiInputs .entry)
      | .backedge =>
        header_ports inputs carried ▸ bindings_extend [] headerSigs ▸ ports_data carried ▸ wires (g.phiInputs .backedge)
    predicate := header_ports inputs carried ▸ bindings_extend [] headerSigs ▸ origin g.predicate
    result := header_ports inputs carried ▸ bindings_extend [] headerSigs ▸ origin g.result }

abbrev Artifact (inputs carried : List (ValueSort Unit)) :=
  Silmaril.MLIR.CF.Cfg Loop.MLIR.CF.TargetOp (Loop.MLIR.CF.Mixed.Label (carried.map retargetSort) i64)
    (InputWidths inputs) [i64]

def emit? (g : Native inputs carried entrySigs headerSigs word) :
    Option (Artifact inputs carried) :=
  (retarget? g).map Loop.MLIR.CF.Mixed.lower

def emitNormalized? (g : Native inputs carried entrySigs headerSigs word) :
    Option (Artifact inputs carried) :=
  emit? (normalize g).rewrite.graph

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR
