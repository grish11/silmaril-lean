module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Defs

/-! # Sink the final pure header binding into the existing return block -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink

open Silmaril.MLIR.Arith (Var Width)
open Silmaril.MLIR.CF (Block Cfg Frame Terminator)
open Silmaril.MLIR.Pure (Operands i1)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra Γ args : List Width} {saved carried result w : Width}

/-- The header retains its argument bank. The old exit result argument is
replaced by the typed inputs of the sunk operation. -/
inductive ExitLabel (bank inputs : List Width) : List Width → Type where
  | header : ExitLabel bank inputs bank
  | exit : ExitLabel bank inputs inputs

abbrev SavedBank (saved carried : Width) (extra : List Width) := (extra ++ [saved]) ++ [carried]

abbrev Source (Input : List Width) (saved carried result : Width) (extra : List Width) :=
  Cfg TargetOp (Label saved carried result extra) Input [result]

abbrev TargetCfg (Input : List Width) (saved carried result : Width) (extra args : List Width) :=
  Cfg TargetOp (ExitLabel (SavedBank saved carried extra) args) Input [result]

/-- An entry with one actual jump to the header, under any retained lets. -/
inductive Entry : {Γ : List Width} →
      Block TargetOp (Label saved carried result extra) Γ [result] → Type where
  | jump {Γ : List Width} (packet : Operands Γ (SavedBank saved carried extra)) :
      Entry (.terminator (.br ⟨.header, packet⟩))
  | keep {Γ args : List Width} {w : Width} (op : TargetOp args w) (operands : Operands Γ args)
      {rest : Block TargetOp (Label saved carried result extra) (w :: Γ) [result]} (tail : Entry rest) :
      Entry (.letOp op operands rest)

def Entry.check? : {Γ : List Width} →
    (code : Block TargetOp (Label saved carried result extra) Γ [result]) → Option (Entry code)
  | _, .terminator (.br ⟨.header, packet⟩) => some (.jump packet)
  | _, .letOp op operands rest => (check? rest).map (.keep op operands)
  | _, .terminator _ => none

def Entry.code {Γ : List Width} {source : Block TargetOp (Label saved carried result extra) Γ [result]}
    (entry : Entry source) (exitArgs : List Width) :
    Block TargetOp (ExitLabel (SavedBank saved carried extra) exitArgs) Γ [result] :=
  match entry with
  | .jump packet => .terminator (.br ⟨.header, packet⟩)
  | .keep op operands tail => .letOp op operands (tail.code exitArgs)

/-- Search for the inverse of weakening every read past the removed binding. -/
def unweaken? : {args : List Width} → (packet : Operands (w :: Γ) args) →
    Option { original : Operands Γ args // For.renameOperands Var.there original = packet }
  | _, .nil => some ⟨.nil, rfl⟩
  | _, .cons .here _ => none
  | _, .cons (.there ref) rest => do
    let clean ← unweaken? rest
    pure ⟨.cons ref clean.1, congrArg (Operands.cons (.there ref)) clean.2⟩

/-- The final let's result appears solely in argument zero of the false
edge. The condition and the whole true-edge feedback packet are weakened
from the scope before that let. -/
inductive Header : Nat → {Γ : List Width} →
      Block TargetOp (Label saved carried result extra) Γ [result] → Type where
  | last {Γ args : List Width} (op : TargetOp args result) (operands : Operands Γ args)
      (test : Var Γ i1) (feedback : Operands Γ (SavedBank saved carried extra)) :
      Header 0 (.letOp op operands (.terminator
        (.condBr (.there test) ⟨.header, For.renameOperands Var.there feedback⟩
          ⟨.exit, .cons .here .nil⟩)))
  | keep {index : Nat} {Γ args : List Width} {w : Width} (op : TargetOp args w) (operands : Operands Γ args)
      {rest : Block TargetOp (Label saved carried result extra) (w :: Γ) [result]}
      (tail : Header index rest) : Header (index + 1) (.letOp op operands rest)

def Header.checkLast? (op : TargetOp args result) (operands : Operands Γ args) :
    (tail : Block TargetOp (Label saved carried result extra) (result :: Γ) [result]) →
    Option (Header 0 (.letOp op operands tail))
  | .terminator (.condBr (.there test) ⟨.header, feedback⟩ ⟨.exit, .cons .here .nil⟩) => do
    let clean ← unweaken? feedback
    pure (by rw [← clean.2]; exact .last op operands test clean.1)
  | _ => none

def Header.check? : (index : Nat) → {Γ : List Width} →
    (code : Block TargetOp (Label saved carried result extra) Γ [result]) → Option (Header index code)
  | 0, _, .letOp (w := width) op operands tail =>
    if same : width = result then by subst width; exact checkLast? op operands tail
    else none
  | index + 1, _, .letOp op operands rest => (check? index rest).map (.keep op operands)
  | _, _, .terminator _ => none

def Header.opcode {index : Nat} {Γ : List Width}
    {original : Block TargetOp (Label saved carried result extra) Γ [result]} (header : Header index original) : (args : List Width) × TargetOp args result :=
  match header with
  | .last op .. => ⟨_, op⟩
  | .keep _ _ rest => rest.opcode

def Header.code {index : Nat} {Γ : List Width}
    {original : Block TargetOp (Label saved carried result extra) Γ [result]} (header : Header index original) :
    Block TargetOp (ExitLabel (SavedBank saved carried extra) header.opcode.1) Γ [result] :=
  match header with
  | .last _ operands test feedback =>
    .terminator (.condBr test ⟨.header, feedback⟩ ⟨.exit, operands⟩)
  | .keep op operands rest => .letOp op operands rest.code

/-- Scan the selected source let's actual suffix at its real cut. -/
def sourceUses : (index cut : Nat) → {Γ : List Width} →
    Block TargetOp (Label saved carried result extra) Γ [result] →
    Option (List (Use (Label saved carried result extra)))
  | 0, cut, _, .letOp _ _ tail => some (useSitesAt (some ⟨_, .header⟩) 0 (cut + 1) tail)
  | index + 1, cut, _, .letOp _ _ tail => sourceUses index (cut + 1) tail
  | _, _, _, .terminator _ => none

def packetRefs (Input : List Width) : (args : List Width) → Operands (args ++ Input) args
  | [] => .nil
  | _ :: rest => .cons .here (For.renameOperands Var.there (packetRefs Input rest))

structure Emission (source : Source Input saved carried result extra) (index : Nat) where
  entry : Entry source.entry
  header : Header index (source.block .header)
  returns : source.block .exit = .terminator (.ret (.cons .here .nil))

variable {source : Source Input saved carried result extra} {index : Nat}

def Emission.cfg (emission : Emission source index) :
    TargetCfg Input saved carried result extra emission.header.opcode.1 where
  entry := emission.entry.code _
  block
    | .header => emission.header.code
    | .exit => .letOp emission.header.opcode.2 (packetRefs Input _)
        (.terminator (.ret (.cons .here .nil)))

def exitId : BlockId (ExitLabel (SavedBank saved carried extra) args) := some ⟨_, .exit⟩

def targets : List (Target (ExitLabel (SavedBank saved carried extra) args)) :=
  [⟨_, .header⟩, ⟨_, .exit⟩]

def isExit : Target (ExitLabel (SavedBank saved carried extra) args) → Bool
  | ⟨_, .header⟩ => false
  | ⟨_, .exit⟩ => true

def targetDecEq : DecidableEq (Target (ExitLabel (SavedBank saved carried extra) args)) :=
  fun a b => decidable_of_iff (isExit a = isExit b)
    ⟨by rcases a with ⟨_, a⟩; rcases b with ⟨_, b⟩; cases a <;> cases b <;> simp_all [isExit],
      congrArg isExit⟩

/-- Cut zero exposes all incoming operand arguments. The new value is
read by the existing return at cut one. -/
def Emission.operandSites (emission : Emission source index) :
    List (Point (ExitLabel (SavedBank saved carried extra) emission.header.opcode.1)) :=
  emission.header.opcode.1.map fun _ => ⟨exitId, 0⟩

def checkCut (emission : Emission source index) : Bool :=
  let _ := targetDecEq (saved := saved) (carried := carried) (extra := extra)
    (args := emission.header.opcode.1)
  Dominance.Placement.checkCut emission.cfg targets emission.operandSites
    [.ordinary ⟨exitId, 1⟩] ⟨exitId, 0⟩

def admit? (source : Source Input saved carried result extra) (index : Nat) : Option (Emission source index) := do
  let entry ← Entry.check? source.entry
  let header ← Header.check? index (source.block .header)
  match returns : source.block .exit with
  | .terminator (.ret (.cons .here .nil)) => some ⟨entry, header, returns⟩
  | _ => none

/-- Perform the physical rewrite for one nominated current header index
and validate the new cut on its actual typed CFG. -/
def sink? (source : Source Input saved carried result extra) (index : Nat) : Option (Emission source index) :=
  (admit? source index).filter checkCut

/-- Relate the exact packets before and after motion. The existing
header bank is untouched. An exit packet records the operands with which
the old header evaluated the removed operation. -/
def restorePacket (op : TargetOp args result) :
    Frame (ExitLabel (SavedBank saved carried extra) args) → Frame (Label saved carried result extra)
  | ⟨.header, packet⟩ => ⟨.header, packet⟩
  | ⟨.exit, packet⟩ => ⟨.exit, .cons (evalOp op packet) .nil⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink
