module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.WellFormed

/-! Capture reindexing at the pulled valuation and actual re-emitted observations. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open CategoryTheory (Discrete)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp model)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes
open Diamond (Model Val)
open Diamond.LambdaSSA.Institution.Fiber (fiberRoom inputModel)
open Silmaril.Isotope.Institution.Observational (ssaBeh)
open Silmaril.Logic.Institution.Observational (Sentence)
open Institution (equation rtlBehaviors scope)

universe w
variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable (perm : InputPermutation arity)
variable {g : SourceWithEntry arity entrySigs sigs}
variable {p : Plan arity entrySigs}

/-- The inverse permutation restores the exact source graph. -/
theorem reindexCaptures_symm (g : SourceWithEntry arity entrySigs sigs) :
    reindexCaptures perm.symm (reindexCaptures perm g) = g :=
  Proofs.reindexCaptures_symm perm g

/-- Changing capture addresses commutes with the entire dependent entry
table and the entry latch. -/
theorem initial_reindex (g : SourceWithEntry arity entrySigs sigs)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (reindexCaptures perm g).initial m input = g.initial m (perm.pull input) :=
  Proofs.initial_mapCaptures (fun i => perm i) g m input

/-- Recognition ensures the unchanged header reads only its bank and
producers. The native partial result is therefore preserved by pulling
the external valuation along the same capture permutation. -/
theorem denote_reindex (recognized : recognize g = some p)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (reindexCaptures perm g).denote m input = g.denote m (perm.pull input) :=
  Proofs.denote_mapCaptures (fun i => perm i) recognized m input

variable {before after : Checked.Phi.Targets}

/-- The ordinary checker accepts the mapped graph whenever it accepts the original. -/
theorem lowerChecked_reindex (accepted : lowerChecked g = some before) :
    ∃ targets, lowerChecked (reindexCaptures perm g) = some targets :=
  Proofs.lowerChecked_mapCaptures (fun i => perm i) accepted

/-- Acceptance is reflected by rechecking with the inverse permutation. -/
theorem lowerChecked_reindex_iff :
    (∃ targets, lowerChecked (reindexCaptures perm g) = some targets) ↔
      ∃ targets, lowerChecked g = some targets := by
  refine ⟨fun ⟨_, accepted⟩ => ?_, fun ⟨_, accepted⟩ => lowerChecked_reindex perm accepted⟩
  simpa only [reindexCaptures_symm] using lowerChecked_reindex perm.symm accepted

/-- Once the mapped graph passes the ordinary checker, both actual
re-emissions have the original behaviours at the pulled input. The λSSA
observation-set equality ranges over all initial and final memories. -/
theorem observations_reindex (accepted : lowerChecked g = some before)
    (emitted : lowerChecked (reindexCaptures perm g) = some after)
    (input : WordTuple arity) (initial : Memory) :
    rtlBehaviors input initial after.1 = rtlBehaviors (perm.pull input) initial before.1 ∧
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope emitted) =
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory (perm.pull input)) (scope accepted) :=
  Proofs.observations_mapCaptures (fun i => perm i) accepted emitted input initial

/-- Starting from one successful check, re-emit with the ordinary checker
and compare both actual target behaviours at every pulled valuation. -/
theorem reemit_observations (accepted : lowerChecked g = some before) :
    ∃ targets, ∃ emitted : lowerChecked (reindexCaptures perm g) = some targets,
      ∀ (input : WordTuple arity) (initial : Memory),
        rtlBehaviors input initial targets.1 = rtlBehaviors (perm.pull input) initial before.1 ∧
          ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope emitted) =
            ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory (perm.pull input)) (scope accepted) := by
  obtain ⟨targets, emitted⟩ := lowerChecked_reindex perm accepted
  exact ⟨targets, emitted, observations_reindex perm accepted emitted⟩

variable {right : SourceWithEntry arity rightEntry rightSigs}
variable {rightBefore rightAfter : Checked.Phi.Targets}

/-- At a common typed input, both re-emitted equations reflect native
partial equality at its pullback, including when neither side returns. -/
theorem reindex_equation_at_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (reindexCaptures perm g) = some after)
    (rightEmitted : lowerChecked (reindexCaptures perm right) = some rightAfter)
    (input : WordTuple arity) (initial : Memory) :
    let original := g.denote model (perm.pull input) = right.denote model (perm.pull input)
    ((Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial) ↔ original) ∧
      ((fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted)) ↔ original) :=
  Proofs.mapCaptures_equation_at_iff (fun i => perm i) leftChecked rightChecked leftEmitted rightEmitted input initial

/-- The inverse permutation supplies a preimage for every old valuation,
so all-input satisfaction reflects the original native equation. -/
theorem reindex_equation_holds_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (reindexCaptures perm g) = some after)
    (rightEmitted : lowerChecked (reindexCaptures perm right) = some rightAfter) (initial : Memory) :
    let original := (Loop.Institution.Sentence.equation (equation g right)).Holds model
    ((∀ input : WordTuple arity, (Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial)) ↔ original) ∧
      ((∀ input : WordTuple arity, (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted))) ↔ original) :=
  Proofs.reindex_equation_holds_iff perm leftChecked rightChecked leftEmitted rightEmitted initial

variable (mapping : InputMap arity)

/-- External reads in the dependent entry commute with the valuation pullback. -/
theorem initial_mapCaptures (g : SourceWithEntry arity entrySigs sigs)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (mapCaptures mapping g).initial m input = g.initial m (mapping.pull input) :=
  Proofs.initial_mapCaptures mapping g m input

/-- The mapped native graph has the partial result at the pulled valuation. -/
theorem denote_mapCaptures (recognized : recognize g = some p)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (mapCaptures mapping g).denote m input = g.denote m (mapping.pull input) :=
  Proofs.denote_mapCaptures mapping recognized m input

/-- Forward acceptance allows several old captures to read the same new slot. -/
theorem lowerChecked_mapCaptures (accepted : lowerChecked g = some before) :
    ∃ targets, lowerChecked (mapCaptures mapping g) = some targets :=
  Proofs.lowerChecked_mapCaptures mapping accepted

/-- Recheck and compare both actual targets at the pulled valuation. Equality
includes exact returns with full memory and actual divergence. -/
theorem reemit_mapped_observations (accepted : lowerChecked g = some before) :
    ∃ targets, ∃ emitted : lowerChecked (mapCaptures mapping g) = some targets,
      ∀ (input : WordTuple arity) (initial : Memory),
        rtlBehaviors input initial targets.1 = rtlBehaviors (mapping.pull input) initial before.1 ∧
          ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope emitted) =
            ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory (mapping.pull input)) (scope accepted) := by
  obtain ⟨targets, emitted⟩ := lowerChecked_mapCaptures mapping accepted
  exact ⟨targets, emitted, Proofs.observations_mapCaptures mapping accepted emitted⟩

/-- All new inputs test exactly the old valuations in the image of the pullback. -/
theorem mapCaptures_equation_holds_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (mapCaptures mapping g) = some after)
    (rightEmitted : lowerChecked (mapCaptures mapping right) = some rightAfter) (initial : Memory) :
    let image := ∀ old ∈ Set.range (fun input : WordTuple arity => mapping.pull input),
      g.denote model old = right.denote model old
    ((∀ input : WordTuple arity, (Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial)) ↔ image) ∧
      ((∀ input : WordTuple arity, (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted))) ↔ image) :=
  Proofs.mapCaptures_equation_holds_iff mapping leftChecked rightChecked leftEmitted rightEmitted initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
