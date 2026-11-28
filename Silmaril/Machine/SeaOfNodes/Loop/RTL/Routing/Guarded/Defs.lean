module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Defs

/-! # A checked two-word bank with an updated-word guard -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog State)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg)
open Silmaril.SSA.RVSDG (Wires)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

abbrev Native := BankGraph 2 RTL.headerSigs

def pair (first second : Word) : WordTuple 2 := .cons first (.cons second .nil)

def updateWires : Wires (headerArgs 1) [] [wordPort, wordPort] :=
  .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

def guardWires : Wires (headerArgs 1) [[wordPort], [wordPort]] [wordPort, wordPort] :=
  .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)

/-- Compare the update to the limit. Feedback carries the update and a copy
of the old first field. Exit observes the old second field. -/
def graph (p : Profile) : Native where
  preheader := .nil
  header := Checked.schedule p updateWires guardWires
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.arg (.tail (.tail .head))) .nil)
  predicate := .output (2 : Fin 3) .head
  result := .arg (.tail (.tail (.tail .head)))

def rtl (g : Native) : Prog Reg := lowerBank g

/-- The exact frame and point after the emitted header's branch. -/
def successor (p : Profile) (fr : Frame Reg) (first second : Word) (mem : Memory) : State Reg :=
  let after := p.headerFrame fr first second
  if p.guardWord first second = 0 then
    ⟨⟨0, 2, 0⟩, after.set .phi second, [], mem⟩
  else
    ⟨⟨0, 1, 0⟩, bindBank after (pair (p.update.eval first second) first), [], mem⟩

def recognize (g : Native) : Option Profile :=
  (Checked.decodeSchedule g.header).bind fun p =>
    if Checked.provenance g = Checked.provenance (graph p) then some p else none

def lowerChecked (g : Native) : Option Checked.Phi.Targets :=
  (recognize g).bind fun _ =>
    if (lowerBankFunc g).WellFormed then some (rtl g, Generic.lower g) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded
