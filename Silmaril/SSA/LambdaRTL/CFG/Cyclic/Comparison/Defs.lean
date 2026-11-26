module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Defs

/-! # Observational classes for named cyclic λRTL and λSSA

Fix the register and label types, instruction alphabet, value carrier and
monad. Models share the compiler's pair law. A common input is a store on the
original register type. The lexical interface reads those values at version
zero. Both observations are computations of a label and payload, with the
first missing table label serving as the exit. Equality ranges over every
pair-lawful model at the fixed carrier and monad and every common input.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison

open Silmaril.Elgot

universe v w

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- A lexical table with a version-zero input context at entry and a
singleton packet context at each labelled body. -/
structure LexicalGraph (V K : Type w) (F : Type v) [DecidableEq V] where
  graph : CFG (V × Nat) K F
  entrySSA : ∃ context : Finset (V × Nat),
    (∀ reg ∈ context, reg.2 = 0) ∧ graph.entry.toRegion.IsSSA context
  blocksSSA : ∀ item ∈ graph.blocks, item.2.body.toRegion.IsSSA {item.2.param}

/-- Read the admitted lexical table as mutable RTL over the original names. -/
noncomputable def deversion [DecidableEq V] [Infinite V] (graph : LexicalGraph V K F) : CFG V K F :=
  Cyclic.RoundTrip.deversionGraph graph.graph

/-- The common interpretation of the instruction alphabet and packet operations. -/
abbrev PairModel (F : Type v) (M : Type w → Type w) (α : Type w) [Monad M] :=
  { model : Model F M α // model.PairLawful }

variable [DecidableEq V] [DecidableEq K] [Monad M] [Iterate M]

/-- The mutable observation projects away the final store. -/
def rtlObserve (model : PairModel F M α) (graph : CFG V K F) (store : V → α) : M (K × α) :=
  obs <$> Cyclic.run model.val graph store

/-- Lift the common store to lexical names. The entry context and packets
ensure that the initial values of nonzero versions are irrelevant. -/
def ssaObserve (model : PairModel F M α) (graph : LexicalGraph V K F) (store : V → α) : M (K × α) :=
  Cyclic.runSSA model.val graph.graph (fun reg => store reg.1)

/-- Equality of whole mutable observations at the same initial store,
uniformly in the models of the common profile. -/
def rtlSetoid : Setoid (CFG V K F) where
  r lhs rhs := ∀ (model : PairModel F M α) (store : V → α),
    rtlObserve model lhs store = rtlObserve model rhs store
  iseqv := ⟨fun _ _ _ => rfl, fun h model store => (h model store).symm,
    fun h₁ h₂ model store => (h₁ model store).trans (h₂ model store)⟩

/-- Equality of whole lexical observations at the same initial store,
uniformly in the models of the common profile. -/
def ssaSetoid : Setoid (LexicalGraph V K F) where
  r lhs rhs := ∀ (model : PairModel F M α) (store : V → α),
    ssaObserve model lhs store = ssaObserve model rhs store
  iseqv := ⟨fun _ _ _ => rfl, fun h model store => (h model store).symm,
    fun h₁ h₂ model store => (h₁ model store).trans (h₂ model store)⟩

abbrev RTLClass (V K : Type w) (F : Type v) (M : Type w → Type w) (α : Type w)
    [DecidableEq V] [DecidableEq K] [Monad M] [Iterate M] :=
  Quotient (rtlSetoid (V := V) (K := K) (F := F) (M := M) (α := α))

abbrev SSAClass (V K : Type w) (F : Type v) (M : Type w → Type w) (α : Type w)
    [DecidableEq V] [DecidableEq K] [Monad M] [Iterate M] :=
  Quotient (ssaSetoid (V := V) (K := K) (F := F) (M := M) (α := α))

/-- Observe a mutable program class in one common model and input. -/
def rtlClassObserve (model : PairModel F M α) (program : RTLClass V K F M α)
    (store : V → α) : M (K × α) :=
  Quotient.lift (s := rtlSetoid (M := M) (α := α)) (fun graph => rtlObserve model graph store)
    (fun _ _ equivalent => equivalent model store) program

/-- Observe a lexical program class in one common model and input. -/
def ssaClassObserve (model : PairModel F M α) (program : SSAClass V K F M α)
    (store : V → α) : M (K × α) :=
  Quotient.lift (s := ssaSetoid (M := M) (α := α)) (fun graph => ssaObserve model graph store)
    (fun _ _ equivalent => equivalent model store) program

/-- A model satisfies an equation between mutable classes when their
observations agree for every common input. -/
def rtlSat (model : PairModel F M α) (lhs rhs : RTLClass V K F M α) : Prop :=
  ∀ store, rtlClassObserve model lhs store = rtlClassObserve model rhs store

/-- A model satisfies an equation between lexical classes when their
observations agree for every common input. -/
def ssaSat (model : PairModel F M α) (lhs rhs : SSAClass V K F M α) : Prop :=
  ∀ store, ssaClassObserve model lhs store = ssaClassObserve model rhs store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
