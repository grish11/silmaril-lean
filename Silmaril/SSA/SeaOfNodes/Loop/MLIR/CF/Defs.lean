module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.MLIR.Defs
public import Silmaril.SSA.MLIR.SCF.For.Defs

/-! Lower a ranked pure single loop with a bank of word latches to typed MLIR CF. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF

open Diamond (Val ValueSort dataPorts)
open RVSDG (Tuple Wires extend)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (Names Scope OpcodeMap inputNames lowerCode weaken)
open Silmaril.MLIR.Arith (BinOp Env Width)
open Silmaril.MLIR.Pure (Eval Operands OpSignature)
open Silmaril.MLIR.CF (Cfg Terminator)
open Silmaril.MLIR.SCF (For)

/-- Reuse the source arithmetic operations with typed unsigned and signed comparisons. -/
inductive Op : Diamond.Signature Width where
  | arithmetic {ins out} : SeaOfNodes.MLIR.Op ins out → Op ins out
  | ult (w : Width) : Op [.data w, .data w] .predicate
  | slt (w : Width) : Op [.data w, .data w] .predicate

abbrev model : Diamond.Model Op where
  value := Word
  run
    | .arithmetic op, args => SeaOfNodes.MLIR.model.run op args
    | .ult _, .cons x (.cons y .nil) => ⟨x.ult y⟩
    | .slt _, .cons x (.cons y .nil) => ⟨x.slt y⟩

/-- The constant and flag-free arithmetic symbols used in the emitted code. -/
inductive WordOp : OpSignature where
  | constant {w : Width} (bits : Word w) : WordOp [] w
  | binary (w : Width) (op : BinOp) : WordOp [w, w] w

def evalWord : Eval WordOp
  | _, _, .constant bits, .nil => bits
  | _, _, .binary _ op, .cons x (.cons y .nil) => op.denote x y

/-- Reuse the scalar CF Arith interpreter, including one-bit comparison results. -/
abbrev TargetOp := For.LowerOp WordOp

def evalOp : Eval TargetOp := For.lowerEval evalWord

def opcode : OpcodeMap Op TargetOp
  | _, _, .arithmetic (.constant bits) => .original (.constant bits)
  | _, _, .arithmetic (.binary (w := w) op) => .original (.binary w op)
  | _, _, .ult w => .ult w
  | _, _, .slt w => .slt w

abbrev inputSorts (Γ : List Width) : List (ValueSort Width) :=
  Γ.map ValueSort.data

def entryScope (Γ : List Width) : Scope (dataPorts (inputSorts Γ)) [] Γ :=
  ⟨inputNames Γ, PUnit.unit⟩

namespace Bank

abbrev Program (Γ carried : List Width) (result : Width)
    (entrySigs headerSigs : List (List (Diamond.Ty Width))) :=
  Loop.Graph Op (inputSorts Γ) (inputSorts carried) entrySigs headerSigs (.data result)

inductive Label (carried : List Width) (result : Width) : List Width → Type where
  | header : Label carried result carried
  | exit : Label carried result [result]

abbrev Values (widths : List Width) := Tuple (Val Word) (dataPorts (inputSorts widths))

/-- Encode the source latch in argument order. -/
def bankEnv : {widths : List Width} → Values widths → Env widths
  | [], _ => .nil
  | _ :: _, bank =>
    let rest := match bank with | .cons _ tail => tail
    .cons (bank.get .head) (bankEnv rest)

def bankOperands {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    {Δ : List Width} (scope : Scope args past Δ) :
    {widths : List Width} → Wires args past (dataPorts (inputSorts widths)) → Operands Δ widths
  | [], _ => .nil
  | _ :: _, wires =>
    let rest := match wires with | .cons _ tail => tail
    .cons (scope.resolveValue (wires.get .head)) (bankOperands scope rest)

def prependNames {Γ : List Width} {ports : List (Diamond.Ty Width)} :
    (widths : List Width) → Tuple (Names Γ) ports → Tuple (Names (widths ++ Γ)) ports
  | [], names => names
  | w :: rest, names => (prependNames rest names).map (weaken w)

def bankNames (Γ : List Width) :
    (carried : List Width) → Tuple (Names (carried ++ Γ)) (dataPorts (inputSorts carried))
  | [] => .nil
  | w :: rest => .cons .here ((bankNames Γ rest).map (weaken w))

/-- Block arguments precede captured inputs in CF. The source header ports
retain their captured-input-then-latch order. -/
def headerScope (Γ carried : List Width) :
    Scope (headerPorts (inputSorts Γ) (inputSorts carried)) [] (carried ++ Γ) :=
  ⟨appendTuple (bankNames Γ carried) (prependNames carried (inputNames Γ)), PUnit.unit⟩

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Program Γ carried result entrySigs headerSigs)

def entryTerm {Δ : List Width} (scope : Scope (dataPorts (inputSorts Γ)) (extend [] entrySigs) Δ) :
    Terminator (Label carried result) [result] Δ :=
  .br ⟨.header, bankOperands scope (g.phiInputs .entry)⟩

def headerTerm {Δ : List Width}
    (scope : Scope (headerPorts (inputSorts Γ) (inputSorts carried)) (extend [] headerSigs) Δ) :
    Terminator (Label carried result) [result] Δ :=
  .condBr (scope.resolveValue g.predicate)
    ⟨.header, bankOperands scope (g.phiInputs .backedge)⟩
    ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩

/-- Emit the preheader, a self-branching header, and a distinct exit block.
The entry and backedge each pass an entire typed Φ column in order. -/
def lower : Cfg TargetOp (Label carried result) Γ [result] where
  entry := lowerCode opcode g.preheader (entryScope Γ) (entryTerm g)
  block
    | .header => lowerCode opcode g.header (headerScope Γ carried) (headerTerm g)
    | .exit => .terminator (.ret (.cons .here .nil))

end Bank

/-- The scalar API is the singleton bank specialization. -/
abbrev Program (Γ : List Width) (carried result : Width)
    (entrySigs headerSigs : List (List (Diamond.Ty Width))) :=
  Bank.Program Γ [carried] result entrySigs headerSigs

abbrev Label (carried result : Width) := Bank.Label [carried] result
@[match_pattern] abbrev Label.header {carried result : Width} : Label carried result [carried] := Bank.Label.header
@[match_pattern] abbrev Label.exit {carried result : Width} : Label carried result [result] := Bank.Label.exit

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

abbrev headerScope (Γ : List Width) (carried : Width) := Bank.headerScope Γ [carried]

abbrev entryTerm (g : Program Γ carried result entrySigs headerSigs) {Δ : List Width} :=
  @Bank.entryTerm Γ [carried] result entrySigs headerSigs g Δ

abbrev headerTerm (g : Program Γ carried result entrySigs headerSigs) {Δ : List Width} :=
  @Bank.headerTerm Γ [carried] result entrySigs headerSigs g Δ

abbrev lower (g : Program Γ carried result entrySigs headerSigs) := Bank.lower g

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
