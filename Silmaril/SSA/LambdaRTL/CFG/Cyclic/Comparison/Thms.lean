module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
import Silmaril.SSA.LambdaRTL.Thms

/-! Versioning and deversioning give inverse maps between observational
classes for the common named cyclic profile. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison

open Silmaril.Elgot

universe v w

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V]

theorem LexicalGraph.entry_zero (graph : LexicalGraph V K F) :
    ∀ reg ∈ graph.graph.entry.toRegion.fv, reg.2 = 0 := by
  obtain ⟨_, zero, entrySSA⟩ := graph.entrySSA
  exact fun _ used => zero _ (Region.fv_subset_of_isSSA entrySSA used)

theorem LexicalGraph.packetClosed (graph : LexicalGraph V K F) :
    Cyclic.RoundTrip.PacketClosed graph.graph :=
  fun item member => Region.fv_subset_of_isSSA (graph.blocksSSA item member)

variable [DecidableEq K]

/-- The version compiler meets the lexical entry and packet interface. -/
def version (graph : CFG V K F) : LexicalGraph V K F where
  graph := Versioning.compile graph
  entrySSA := ⟨_, by simp +contextual [List.mem_map], Versioning.compile_entry_isSSA graph⟩
  blocksSSA := Versioning.compile_blocks_areSSA graph

variable [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]

@[simp] theorem observe_version (model : PairModel F M α) (graph : CFG V K F) (store : V → α) :
    ssaObserve model (version graph) store = rtlObserve model graph store :=
  (Versioning.run_commutes model.val model.property graph (fun reg => store reg.1)).symm

theorem version_equiv_iff (lhs rhs : CFG V K F) :
    (ssaSetoid (M := M) (α := α)).r (version lhs) (version rhs) ↔
      (rtlSetoid (M := M) (α := α)).r lhs rhs := by
  change (∀ (model : PairModel F M α) (store : V → α),
    ssaObserve model (version lhs) store = ssaObserve model (version rhs) store) ↔
      (∀ model store, rtlObserve model lhs store = rtlObserve model rhs store)
  simp only [observe_version]

/-- Compile representatives of mutable classes. -/
def versionClass : RTLClass V K F M α → SSAClass V K F M α :=
  Quotient.map version (fun _ _ => (version_equiv_iff _ _).mpr)

variable [Infinite V]

/-- The mutable observation uses only the version-zero part of an arbitrary
lexical input. Packet closure discharges every other input read. -/
theorem observe_deversion_runSSA (model : PairModel F M α) (graph : LexicalGraph V K F)
    (input : V × Nat → α) :
    rtlObserve model (deversion graph) (fun reg => input (reg, 0)) =
      Cyclic.runSSA model.val graph.graph input :=
  (Versioning.run_commutes model.val model.property _ input).trans
    (Cyclic.RoundTrip.runSSA_deversion_reversion model.val model.property _
      graph.packetClosed graph.entry_zero input)

@[simp] theorem observe_deversion (model : PairModel F M α) (graph : LexicalGraph V K F)
    (store : V → α) : rtlObserve model (deversion graph) store = ssaObserve model graph store :=
  observe_deversion_runSSA model graph (fun reg => store reg.1)

theorem deversion_equiv_iff (lhs rhs : LexicalGraph V K F) :
    (rtlSetoid (M := M) (α := α)).r (deversion lhs) (deversion rhs) ↔
      (ssaSetoid (M := M) (α := α)).r lhs rhs := by
  change (∀ (model : PairModel F M α) (store : V → α),
    rtlObserve model (deversion lhs) store = rtlObserve model (deversion rhs) store) ↔
      (∀ model store, ssaObserve model lhs store = ssaObserve model rhs store)
  simp only [observe_deversion]

/-- Deversion representatives, keeping the packet decoders in the mutable graph. -/
noncomputable def deversionClass : SSAClass V K F M α → RTLClass V K F M α :=
  Quotient.map deversion (fun _ _ => (deversion_equiv_iff _ _).mpr)

@[simp] theorem deversion_version_class (program : RTLClass V K F M α) :
    deversionClass (versionClass program) = program := by
  refine Quotient.inductionOn program fun graph => Quotient.sound ?_
  exact fun model store => Versioning.roundTrip_run_obs model.val model.property graph store

@[simp] theorem version_deversion_class (program : SSAClass V K F M α) :
    versionClass (deversionClass program) = program := by
  refine Quotient.inductionOn program fun graph => Quotient.sound ?_
  exact fun model store => (observe_version model _ store).trans (observe_deversion model graph store)

/-- The observational class equivalence for the common named cyclic interface. -/
noncomputable def classEquiv : RTLClass V K F M α ≃ SSAClass V K F M α where
  toFun := versionClass
  invFun := deversionClass
  left_inv := deversion_version_class
  right_inv := version_deversion_class

omit [Infinite V] in
@[simp] theorem classObserve_version (model : PairModel F M α) (program : RTLClass V K F M α)
    (store : V → α) :
    ssaClassObserve model (versionClass program) store = rtlClassObserve model program store :=
  Quotient.inductionOn program (fun graph => observe_version model graph store)

@[simp] theorem classObserve_deversion (model : PairModel F M α) (program : SSAClass V K F M α)
    (store : V → α) :
    rtlClassObserve model (deversionClass program) store = ssaClassObserve model program store :=
  Quotient.inductionOn program (fun graph => observe_deversion model graph store)

omit [Infinite V] in
theorem ssaSat_version_iff (model : PairModel F M α) (lhs rhs : RTLClass V K F M α) :
    ssaSat model (versionClass lhs) (versionClass rhs) ↔ rtlSat model lhs rhs := by
  simp only [ssaSat, rtlSat, classObserve_version]

theorem rtlSat_deversion_iff (model : PairModel F M α) (lhs rhs : SSAClass V K F M α) :
    rtlSat model (deversionClass lhs) (deversionClass rhs) ↔ ssaSat model lhs rhs := by
  simp only [rtlSat, ssaSat, classObserve_deversion]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
