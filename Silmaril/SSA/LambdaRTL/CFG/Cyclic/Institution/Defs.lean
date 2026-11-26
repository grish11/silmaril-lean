module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison.Defs
public import Silmaril.SSA.LambdaRTL.Version.Institution.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.Thms

/-! # Named cyclic observational institutions

Signatures are primitive alphabets with functions as renamings. Register,
label and value types and the Elgot monad are fixed. The models at a signature
form the discrete category of pair-lawful interpretations. A reduct
precomposes the primitive interpretation with the renaming. Sentences compare
two observational program classes at every common initial store. The
comparison relation acts on the whole exit-label and payload computations.
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

variable {V K M α}

/-- Compare mutable observations at every common input in one model. -/
def rtlRelSat {F : Type} (R : M (K × α) → M (K × α) → Prop)
    (model : PairModel F M α) (lhs rhs : RTLClass V K F M α) : Prop :=
  ∀ store, R (rtlClassObserve model lhs store) (rtlClassObserve model rhs store)

/-- Compare lexical observations at every common input in one model. -/
def ssaRelSat {F : Type} (R : M (K × α) → M (K × α) → Prop)
    (model : PairModel F M α) (lhs rhs : SSAClass V K F M α) : Prop :=
  ∀ store, R (ssaClassObserve model lhs store) (ssaClassObserve model rhs store)

variable (V K M α)

/-- Named mutable comparisons at a single alphabet. -/
def rtlRelationRoom (R : M (K × α) → M (K × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := RTLEquation V K M α S
  Mod := Cat.of (Discrete (LawfulModel M α S.ops))
  Sat model comparison := rtlRelSat R model.as comparison.1 comparison.2

/-- Named packet-scoped lexical comparisons at a single alphabet. -/
def ssaRelationRoom (R : M (K × α) → M (K × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := SSAEquation V K M α S
  Mod := Cat.of (Discrete (LawfulModel M α S.ops))
  Sat model comparison := ssaRelSat R model.as comparison.1 comparison.2

/-- Named mutable equations at a single alphabet. -/
def rtlRoom (S : Sig) : Room.{0, 0, 0} := rtlRelationRoom V K M α Eq S

/-- Named packet-scoped lexical equations at a single alphabet. -/
def ssaRoom (S : Sig) : Room.{0, 0, 0} := ssaRelationRoom V K M α Eq S

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution
