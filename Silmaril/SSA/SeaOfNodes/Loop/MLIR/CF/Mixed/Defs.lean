module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! Mixed predicate and word banks in the existing typed CF block emitter. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed

open Diamond (ValueSort dataPorts)
open RVSDG (Tuple extend)
open SeaOfNodes.MLIR.Lowering (Names Scope valueWidth operands lowerCode weaken)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Terminator)

abbrev Widths (sorts : List (ValueSort Width)) := sorts.map valueWidth

abbrev Program (inputs carried : List (ValueSort Width)) (result : Width)
    (entrySigs headerSigs : List (List (Diamond.Ty Width))) :=
  Loop.Graph Op inputs carried entrySigs headerSigs (.data result)

/-- Each source position has its own SSA name, even when several positions
have the same width. Predicate names have type i1. -/
def names (suffix : List Width) :
    (sorts : List (ValueSort Width)) → Tuple (Names (Widths sorts ++ suffix)) (dataPorts sorts)
  | [] => .nil
  | s :: rest => .cons .here ((names suffix rest).map (weaken (valueWidth s)))

def entryScope (inputs : List (ValueSort Width)) : Scope (dataPorts inputs) [] (Widths inputs) :=
  ⟨List.append_nil (Widths inputs) ▸ names [] inputs, PUnit.unit⟩

def headerScope (inputs carried : List (ValueSort Width)) :
    Scope (headerPorts inputs carried) [] (Widths carried ++ Widths inputs) :=
  ⟨appendTuple (names (Widths inputs) carried)
    (Bank.prependNames (Widths carried) (entryScope inputs).inputs), PUnit.unit⟩

variable {inputs carried : List (ValueSort Width)} {result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

abbrev Label (carried : List (ValueSort Width)) (result : Width) := Bank.Label (Widths carried) result

def entryTerm (g : Program inputs carried result entrySigs headerSigs) {Δ : List Width}
    (scope : Scope (dataPorts inputs) (extend [] entrySigs) Δ) :
    Terminator (Label carried result) [result] Δ :=
  .br ⟨.header, operands scope (g.phiInputs .entry)⟩

def headerTerm (g : Program inputs carried result entrySigs headerSigs) {Δ : List Width}
    (scope : Scope (headerPorts inputs carried) (extend [] headerSigs) Δ) :
    Terminator (Label carried result) [result] Δ :=
  .condBr (scope.resolveValue g.predicate)
    ⟨.header, operands scope (g.phiInputs .backedge)⟩
    ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩

/-- Emit one preheader, a conditional header with the full feedback bank,
and a singleton word exit using the existing typed CF operations. -/
def lower (g : Program inputs carried result entrySigs headerSigs) :
    Cfg TargetOp (Label carried result) (Widths inputs) [result] where
  entry := lowerCode opcode g.preheader (entryScope inputs) (entryTerm g)
  block
    | .header => lowerCode opcode g.header (headerScope inputs carried) (headerTerm g)
    | .exit => .terminator (.ret (.cons .here .nil))

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed
