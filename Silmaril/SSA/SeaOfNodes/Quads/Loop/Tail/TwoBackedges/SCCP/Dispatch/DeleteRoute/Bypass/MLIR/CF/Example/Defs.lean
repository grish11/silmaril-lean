module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Defs

/-! An executable checked CF loop with two predicate ports and one byte port. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Blocks (Bank)

abbrev width : Width := ⟨8, by decide⟩
abbrev word : ValueSort Width := .data width
abbrev regs : List (ValueSort Width) := [.predicate, .predicate, word]
abbrev ports := dataPorts regs

instance bankEq : BankDecidableEq Word ports where
  atPort i := Fin.cases (motive := fun j => DecidableEq (Val Word ports[j]))
    (inferInstance : DecidableEq (ULift Bool))
    (fun j => Fin.cases (motive := fun k => DecidableEq (Val Word ports[k.succ]))
      (inferInstance : DecidableEq (ULift Bool))
      (fun k => Fin.cases (motive := fun l => DecidableEq (Val Word ports[l.succ.succ]))
        (inferInstance : DecidableEq (Word width)) (fun l => l.elim0) k) j) i

def bytePort : Port ports (.value word) := .tail (.tail .head)

def program : Program Op regs word where
  preheader := []
  header := []
  again := .head
  select := .tail .head
  result := bytePort
  feedback side :=
    let stop : Quad Op regs :=
      ⟨_, _, .head, .ult width, .cons bytePort (.cons bytePort .nil)⟩
    if side then [stop, ⟨_, _, bytePort, .arithmetic (.constant 99), .nil⟩] else [stop]

def looping : Program Op regs word := { program with feedback := fun _ => [] }

def entry (again side : Bool) : Bank (regs := regs) model :=
  .cons ⟨again⟩ (.cons ⟨side⟩ (.cons (7 : Word width) .nil))

def facts (side : Fact Word (.value .predicate)) : Tuple (Fact Word) ports :=
  .cons .overdefined (.cons side (.cons (.constant (7 : Word width)) .nil))

/-- Run the original five-block source and the compiled CF at independently
chosen block budgets. The outer option reports checker admission. -/
def observations (p : Program Op regs word) (again side : Bool)
    (originalFuel cfFuel : Nat) : Option (Option Nat × Option Nat) := do
  let cfg ← compile p (facts (.constant ⟨side⟩))
  let input := entry again side
  return ((p.source.runFrom model originalFuel 0 input).map BitVec.toNat,
    (cfg.run evalOp cfFuel (encodeValues input)).map (fun env => (env.get .here).toNat))

/-- Execute the actual CF feedback block and inspect the entire reaching
header bank in argument order. -/
def reachingBank (side : Bool) : Option (Bool × Bool × Nat) := do
  let cfg ← compile program (facts (.constant ⟨side⟩))
  let bank := encodeValues (entry true side)
  match (cfg.block .feedback).eval evalOp (fun term env => term.eval env) (bank.append bank) with
  | .inl ⟨.header, args⟩ =>
    some ((args.get .here).getLsbD 0, (args.get (.there .here)).getLsbD 0,
      (args.get (.there (.there .here))).toNat)
  | _ => none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
