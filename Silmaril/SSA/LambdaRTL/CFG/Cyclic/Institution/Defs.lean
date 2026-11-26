module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison.Defs
public import Silmaril.SSA.LambdaRTL.Version.Institution.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.Thms

/-! # Named cyclic observational institutions

Signatures are primitive alphabets with functions as renamings. Register,
label and value types and the Elgot monad are fixed. The models at a signature
form the discrete category of pair-lawful interpretations. A reduct
precomposes the primitive interpretation with the renaming. Sentences are
equations between observational program classes. Satisfaction compares the
whole exit-label and payload computation at every common initial store.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution

open CategoryTheory Silmaril.Elgot Silmaril.Logic.Institution
open Silmaril.SSA.LambdaRTL.Institution (Sig LawfulModel)
open Comparison

variable {V K F F' : Type} [DecidableEq V]

/-- Change the primitive alphabet of an admitted lexical SSA graph.
The entry and packet contexts are preserved. -/
def renameLexical (h : F → F') (graph : LexicalGraph V K F) : LexicalGraph V K F' where
  graph := graph.graph.mapOp h
  entrySSA := by
    obtain ⟨context, zero, entry⟩ := graph.entrySSA
    exact ⟨context, zero, by simpa only [CFG.mapOp, Body.toRegion_mapOp] using
      (Region.isSSA_mapOp h _ context).mpr entry⟩
  blocksSSA := by
    intro item member
    obtain ⟨source, listed, rfl⟩ := List.mem_map.mp member
    simpa only [Block.mapOp, Body.toRegion_mapOp] using
      (Region.isSSA_mapOp h _ {source.2.param}).mpr (graph.blocksSSA source listed)

variable (V K : Type) [DecidableEq V] [DecidableEq K] (M : Type → Type) [Monad M] [Iterate M] (α : Type)

/-- Equations between mutable program classes. -/
abbrev RTLEquation (S : Sig) :=
  RTLClass V K S.ops M α × RTLClass V K S.ops M α

/-- Equations between lexical program classes. -/
abbrev SSAEquation (S : Sig) :=
  SSAClass V K S.ops M α × SSAClass V K S.ops M α

/-- Named mutable equations at a single alphabet. -/
def rtlRoom (S : Sig) : Room.{0, 0, 0} where
  Sen := RTLEquation V K M α S
  Mod := Cat.of (Discrete (LawfulModel M α S.ops))
  Sat model equation := rtlSat model.as equation.1 equation.2

/-- Named packet-scoped lexical equations at a single alphabet. -/
def ssaRoom (S : Sig) : Room.{0, 0, 0} where
  Sen := SSAEquation V K M α S
  Mod := Cat.of (Discrete (LawfulModel M α S.ops))
  Sat model equation := ssaSat model.as equation.1 equation.2

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution
