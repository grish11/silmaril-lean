module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Defs

/-! # Checked RTL and explicit-φ λSSA for the same one-word loop -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi

open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg WordOp)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

abbrev Targets := Prog Reg × Region (Primitive WordOp)

/-- The existing native matcher controls admission to both targets. -/
def lowerChecked (g : WordLoop) : Option Targets :=
  (Checked.lower g).map fun rtl => (rtl, Generic.lower g)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi
