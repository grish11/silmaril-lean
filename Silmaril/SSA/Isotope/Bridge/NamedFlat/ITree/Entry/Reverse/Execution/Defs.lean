module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs

/-! # Observe the actual reverse RTL with explicit ordered live-out reads -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

/-- Run the attached mutable graph directly. Its exit payload already
contains the selected fields in declared order. -/
noncomputable def observeAttached (M : Model (κ := κ) Events P.Instr) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) (source : CFG V K P.Instr)
    (record : Ty.denote (AtomValues.carrier (κ := κ)) (Region.packedInputType I.context.toList)) :=
  CFG.Cyclic.run (treeModel M.raw) (withLiveOut fields source) (store I.names I.context record) >>=
    fun final => pure (FiniteCFG.packedTreeOutput (treeExitNumber I.exits (obs final)))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
