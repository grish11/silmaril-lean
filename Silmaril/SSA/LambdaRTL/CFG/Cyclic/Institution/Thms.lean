module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Institution.Renaming
import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution

open CategoryTheory Silmaril.Elgot Silmaril.Logic.Institution
open Silmaril.SSA.LambdaRTL.Institution
  (Sig LawfulModel lawfulReductFunctor lawfulReductFunctor_id lawfulReductFunctor_comp)
open Comparison

variable {V K F F' F'' : Type} {M : Type → Type} {α : Type} [DecidableEq V]

@[simp] theorem renameLexical_id (graph : LexicalGraph V K F) : renameLexical id graph = graph := by
  cases graph
  simp only [renameLexical, CFG.mapOp_id]

theorem renameLexical_comp (h : F → F') (k : F' → F'') (graph : LexicalGraph V K F) :
    renameLexical (k ∘ h) graph = renameLexical k (renameLexical h graph) := by
  cases graph
  simp only [renameLexical, CFG.mapOp_comp]

variable [DecidableEq K] [Monad M] [LawfulMonad M] [Iterate M]

/-- Changing primitive names commutes with a whole mutable execution,
including its store, by reducing the model along the same renaming. -/
theorem run_mapOp (h : F → F') (model : Model F' M α) (graph : CFG V K F) (store : V → α) :
    Cyclic.run model (graph.mapOp h) store = Cyclic.run (model.reduct h) graph store :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRenaming.run_mapOp h model graph store

/-- Changing primitive names commutes with a whole lexical execution
under the corresponding model reduct. -/
theorem runSSA_mapOp (h : F → F') (model : Model F' M α) (graph : CFG V K F) (input : V → α) :
    Cyclic.runSSA model (graph.mapOp h) input = Cyclic.runSSA (model.reduct h) graph input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRenaming.runSSA_mapOp h model graph input

theorem rtlObserve_mapOp (h : F → F') (model : PairModel F' M α) (graph : CFG V K F) (store : V → α) :
    rtlObserve model (graph.mapOp h) store = rtlObserve (LawfulModel.reduct h model) graph store :=
  congrArg (fun run => obs <$> run) (run_mapOp h model.val graph store)

theorem ssaObserve_rename (h : F → F') (model : PairModel F' M α) (graph : LexicalGraph V K F)
    (store : V → α) :
    ssaObserve model (renameLexical h graph) store = ssaObserve (LawfulModel.reduct h model) graph store :=
  runSSA_mapOp h model.val graph.graph (fun name => store name.1)

/-- Rename primitives on mutable observational classes. -/
def rtlMapClass (h : F → F') : RTLClass V K F M α → RTLClass V K F' M α :=
  Quotient.map (CFG.mapOp h) fun _ _ equivalent model store => by
    simp only [rtlObserve_mapOp]
    exact equivalent (LawfulModel.reduct h model) store

/-- Rename primitives on lexical observational classes. -/
def ssaMapClass (h : F → F') : SSAClass V K F M α → SSAClass V K F' M α :=
  Quotient.map (renameLexical h) fun _ _ equivalent model store => by
    simp only [ssaObserve_rename]
    exact equivalent (LawfulModel.reduct h model) store

@[simp] theorem rtlMapClass_id (program : RTLClass V K F M α) : rtlMapClass id program = program :=
  Quotient.inductionOn program fun graph => congrArg (Quotient.mk _) (CFG.mapOp_id graph)

@[simp] theorem ssaMapClass_id (program : SSAClass V K F M α) : ssaMapClass id program = program :=
  Quotient.inductionOn program fun graph => congrArg (Quotient.mk _) (renameLexical_id graph)

theorem rtlMapClass_comp (h : F → F') (k : F' → F'') (program : RTLClass V K F M α) :
    rtlMapClass (k ∘ h) program = rtlMapClass k (rtlMapClass h program) :=
  Quotient.inductionOn program fun graph => congrArg (Quotient.mk _) (CFG.mapOp_comp h k graph)

theorem ssaMapClass_comp (h : F → F') (k : F' → F'') (program : SSAClass V K F M α) :
    ssaMapClass (k ∘ h) program = ssaMapClass k (ssaMapClass h program) :=
  Quotient.inductionOn program fun graph => congrArg (Quotient.mk _) (renameLexical_comp h k graph)

@[simp] theorem rtlClassObserve_map (h : F → F') (model : PairModel F' M α)
    (program : RTLClass V K F M α) (store : V → α) :
    rtlClassObserve model (rtlMapClass h program) store =
      rtlClassObserve (LawfulModel.reduct h model) program store :=
  Quotient.inductionOn program fun graph => rtlObserve_mapOp h model graph store

@[simp] theorem ssaClassObserve_map (h : F → F') (model : PairModel F' M α)
    (program : SSAClass V K F M α) (store : V → α) :
    ssaClassObserve model (ssaMapClass h program) store =
      ssaClassObserve (LawfulModel.reduct h model) program store :=
  Quotient.inductionOn program fun graph => ssaObserve_rename h model graph store

/-- Satisfaction of a renamed mutable equation is satisfaction in the reduct. -/
theorem rtlSat_map_iff (h : F → F') (model : PairModel F' M α) (lhs rhs : RTLClass V K F M α) :
    rtlSat model (rtlMapClass h lhs) (rtlMapClass h rhs) ↔ rtlSat (LawfulModel.reduct h model) lhs rhs := by
  simp only [rtlSat, rtlClassObserve_map]

/-- Satisfaction of a renamed lexical equation is satisfaction in the reduct. -/
theorem ssaSat_map_iff (h : F → F') (model : PairModel F' M α) (lhs rhs : SSAClass V K F M α) :
    ssaSat model (ssaMapClass h lhs) (ssaMapClass h rhs) ↔ ssaSat (LawfulModel.reduct h model) lhs rhs := by
  simp only [ssaSat, ssaClassObserve_map]

variable (V K M α)

/-- Mutable cyclic RTL equations under primitive-alphabet renamings. -/
def rtl : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := rtlRoom V K M α
      map h := ⟨fun equation => (rtlMapClass h equation.1, rtlMapClass h equation.2),
        lawfulReductFunctor h, fun model equation => rtlSat_map_iff h model.as equation.1 equation.2⟩
      map_id S := Room.hom_ext
        (funext fun equation => Prod.ext (rtlMapClass_id equation.1) (rtlMapClass_id equation.2))
        (lawfulReductFunctor_id S.ops)
      map_comp h k := Room.hom_ext
        (funext fun equation => Prod.ext (rtlMapClass_comp h k equation.1) (rtlMapClass_comp h k equation.2))
        (lawfulReductFunctor_comp h k) }

/-- Packet-scoped cyclic SSA equations under primitive-alphabet renamings. -/
def ssa : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := ssaRoom V K M α
      map h := ⟨fun equation => (ssaMapClass h equation.1, ssaMapClass h equation.2),
        lawfulReductFunctor h, fun model equation => ssaSat_map_iff h model.as equation.1 equation.2⟩
      map_id S := Room.hom_ext
        (funext fun equation => Prod.ext (ssaMapClass_id equation.1) (ssaMapClass_id equation.2))
        (lawfulReductFunctor_id S.ops)
      map_comp h k := Room.hom_ext
        (funext fun equation => Prod.ext (ssaMapClass_comp h k equation.1) (ssaMapClass_comp h k equation.2))
        (lawfulReductFunctor_comp h k) }

variable {V K M α} [LawfulElgotMonad M]

/-- Versioning is natural on observational classes. -/
theorem versionClass_map (h : F → F') (program : RTLClass V K F M α) :
    versionClass (rtlMapClass h program) = ssaMapClass h (versionClass program) := by
  refine Quotient.inductionOn program fun graph => Quotient.sound fun model store => ?_
  rw [observe_version, rtlObserve_mapOp, ssaObserve_rename]
  exact (observe_version (LawfulModel.reduct h model) graph store).symm

variable [Infinite V]

/-- Deversioning is natural on observational classes, using the inverse
of the versioning square. -/
theorem deversionClass_map (h : F → F') (program : SSAClass V K F M α) :
    deversionClass (ssaMapClass h program) = rtlMapClass h (deversionClass program) := by
  simpa only [version_deversion_class, deversion_version_class] using
    (congrArg deversionClass (versionClass_map h (deversionClass program))).symm

variable (V K M α)

/-- At one alphabet the two equation rooms are isomorphic, with identity on models. -/
noncomputable def roomIso (S : Sig) : rtlRoom V K M α S ≅ ssaRoom V K M α S where
  hom := ⟨fun equation => (versionClass equation.1, versionClass equation.2),
    𝟭 _, fun model equation => ssaSat_version_iff model.as equation.1 equation.2⟩
  inv := ⟨fun equation => (deversionClass equation.1, deversionClass equation.2),
    𝟭 _, fun model equation => rtlSat_deversion_iff model.as equation.1 equation.2⟩
  hom_inv_id := Room.hom_ext
    (funext fun equation => Prod.ext (deversion_version_class equation.1) (deversion_version_class equation.2))
    rfl
  inv_hom_id := Room.hom_ext
    (funext fun equation => Prod.ext (version_deversion_class equation.1) (version_deversion_class equation.2))
    rfl

/-- The cyclic equation institutions are naturally isomorphic over the
common alphabet category. Naturality is equality on observational classes. -/
noncomputable def comparisonIso : (rtl V K M α).I ≅ (ssa V K M α).I :=
  NatIso.ofComponents (roomIso V K M α) fun {_ _} h => by
    apply Room.hom_ext
    · exact funext fun equation => Prod.ext (versionClass_map h equation.1) (versionClass_map h equation.2)
    · exact CategoryTheory.Functor.ext fun model => by cases model; rfl

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution
