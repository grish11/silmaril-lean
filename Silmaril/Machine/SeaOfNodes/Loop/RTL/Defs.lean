module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-! # Machine RTL for tail-tested, one-carried-word loops -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL

open Silmaril.Machine.Lir (Binop Cond Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Func Label Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL
  (PortTy Reg WordOp emitOpsWith inputs portIndex register registerWith word)
open Silmaril.SSA.SeaOfNodes.Diamond (ValueSort)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming headerPorts)
open Silmaril.SSA.RVSDG (Port)

abbrev headerSigs : List (List PortTy) :=
  [[.value word], [.value word], [.value .predicate]]

inductive Update where
  | add
  | sub
  deriving DecidableEq

def Update.source : Update → WordOp [word, word] word
  | .add => .add
  | .sub => .sub

def Update.target : Update → Binop
  | .add => .add
  | .sub => .sub

def Update.eval : Update → Word → Word → Word
  | .add, old, delta => old + delta
  | .sub, old, delta => old - delta

inductive Guard where
  | eq
  | ne
  /-- Strict signed i64 comparison in source operand order. -/
  | slt
  deriving DecidableEq

def Guard.source : Guard → WordOp [word, word] (.predicate : ValueSort Unit)
  | .eq => .eq
  | .ne => .ne
  | .slt => .slt

def Guard.target : Guard → Cond
  | .eq => .eq
  | .ne => .ne
  | .slt => .lts

/-- Each activation computes a new carried word, then compares it with a word
constant. True feeds back the new word. False returns the old carried word. -/
structure Profile where
  update : Update
  limit : Word
  guard : Guard
  deriving DecidableEq

def countdown : Profile := ⟨.sub, 0, .ne⟩

abbrev WordLoop := Graph WordOp inputs [word] [] headerSigs word

def Profile.graph (p : Profile) : WordLoop where
  preheader := .nil
  header :=
    .cons p.update.source (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil))
      (.cons (.const p.limit) .nil
        (.cons p.guard.source (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
          .nil))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (0 : Fin 3) .head) .nil
  predicate := .output (2 : Fin 3) .head
  result := .arg (.tail (.tail .head))

/-- The carried port is the loop parameter. Other ports retain the registers
bound at function entry. -/
def headerRegister {t : PortTy} (port : Port (headerPorts inputs [word]) t) : Reg :=
  match portIndex port with
  | 2 => .phi
  | i => .arg i

/-- Encode the source Phi operand in the actual predecessor's context. -/
def Profile.incomingRegister (p : Profile) : Incoming → Reg
  | .entry => register ((p.graph.phiInputs .entry).get .head)
  | .backedge => registerWith headerRegister ((p.graph.phiInputs .backedge).get .head)

abbrev incomingRegister := countdown.incomingRegister

/-- Source block label and zero-based successor ordinal in the emitted
terminator. RTL lists the nonzero arm first. -/
def incomingSlot : Incoming → Label × Nat
  | .entry => (0, 0)
  | .backedge => (1, 0)

def Profile.preheader (p : Profile) : Block Reg :=
  ⟨[.arg 0, .arg 1], [], .jump 1 [p.incomingRegister .entry]⟩

def Profile.header (p : Profile) : Block Reg :=
  ⟨[.phi], emitOpsWith headerRegister p.graph.header,
    .cond (registerWith headerRegister p.graph.predicate)
      1 [p.incomingRegister .backedge] 2 [registerWith headerRegister p.graph.result]⟩

def exitBlock : Block Reg :=
  ⟨[.node 3], [], .ret [.node 3]⟩

def Profile.lowerFunc (p : Profile) : Func Reg := ⟨⟨2, 1⟩, 0, [p.preheader, p.header, exitBlock]⟩

def Profile.lower (p : Profile) : Prog Reg := ⟨[p.lowerFunc]⟩

/-- The numeric predicate tested by the RTL branch after the update. -/
def Profile.guardWord (p : Profile) (old delta : Word) : Word :=
  ofBool (p.guard.target.eval (p.update.eval old delta) p.limit)

/-- Exact frame after executing the header producers. -/
def Profile.headerFrame (p : Profile) (frame : Frame Reg) (old delta : Word) : Frame Reg :=
  ((frame.set (.node 0) (p.update.eval old delta)).set (.node 1) p.limit).set (.node 2) (p.guardWord old delta)

abbrev graph : WordLoop := countdown.graph
abbrev preheader : Block Reg := countdown.preheader
abbrev header : Block Reg := countdown.header
abbrev lowerFunc : Func Reg := countdown.lowerFunc
abbrev lower : Prog Reg := countdown.lower

def nonzeroWord (next : Word) : Word := ofBool (next != 0)

abbrev headerFrame := countdown.headerFrame

end Silmaril.Machine.SeaOfNodes.Loop.RTL
