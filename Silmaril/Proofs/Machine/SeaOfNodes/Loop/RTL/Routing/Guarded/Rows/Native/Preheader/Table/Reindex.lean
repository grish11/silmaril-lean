module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open CategoryTheory (Discrete)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp model)
open Silmaril.SSA.RVSDG (Locals Tuple Wires)
open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Model Val)
open Diamond.LambdaSSA.Institution.Fiber (fiberRoom inputModel)
open Silmaril.Isotope.Institution.Observational (ssaBeh)
open Silmaril.Logic.Institution.Observational (Sentence)
open Institution (equation rtlBehaviors scope)

universe w
variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable (perm : InputPermutation arity)

private theorem column_symm {past : List (List PortTy)} {ports : List PortTy}
    (wires : Wires (wordPorts arity) past ports) :
    InputPermutation.column perm.symm (perm.column wires) = wires := by
  induction wires with
  | nil => rfl
  | cons wire _ ih =>
    cases wire <;> simp only [InputPermutation.column, Tuple.map] at ih ⊢ <;>
      rw [ih]
    rw [InputPermutation.port_symm]

private theorem flow_symm {past : List (List PortTy)}
    (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    reindexFlow perm.symm (reindexFlow perm flow) = flow := by
  induction flow with
  | nil => rfl
  | cons op args rest ih => rw [reindexFlow, reindexFlow, column_symm, ih]

theorem reindexCaptures_symm (g : SourceWithEntry arity entrySigs sigs) :
    reindexCaptures perm.symm (reindexCaptures perm g) = g := by
  cases g with
  | mk preheader header phi predicate result =>
    have columns : (fun edge => match edge with
      | Loop.Incoming.entry => InputPermutation.column perm.symm (perm.column (phi .entry))
      | Loop.Incoming.backedge => phi .backedge) = phi := by
      funext edge
      cases edge with
      | entry => exact column_symm perm (phi .entry)
      | backedge => rfl
    unfold reindexCaptures
    rw [flow_symm]
    exact congrArg (fun inputs => Loop.Graph.mk preheader header inputs predicate result) columns

private theorem eval_flow (m : Model.{0, 0, w} WordOp)
    {past sigs : List (List PortTy)} (flow : Dataflow WordOp (wordPorts arity) past sigs)
    (input : Tuple (Val m.value) (wordPorts arity)) (locals : Locals (Val m.value) past) :
    (reindexFlow perm flow).eval m input locals = flow.eval m (perm.pull input) locals := by
  induction flow with
  | nil => rfl
  | cons op args rest ih =>
    simp only [reindexFlow, Dataflow.eval, InputPermutation.read_column perm]
    exact ih _

theorem initial_reindex (g : SourceWithEntry arity entrySigs sigs)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (reindexCaptures perm g).initial m input = g.initial m (perm.pull input) := by
  let column : EntryColumnWith arity entrySigs := g.phiInputs .entry
  exact (congrArg (fun locals => (perm.column column).read input locals)
    (eval_flow perm m g.preheader input PUnit.unit)).trans
    (perm.read_column input column (g.preheader.eval m (perm.pull input) PUnit.unit))

variable {g : SourceWithEntry arity entrySigs sigs} {p : Plan arity entrySigs}

theorem denote_reindex (recognized : recognize g = some p)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (reindexCaptures perm g).denote m input = g.denote m (perm.pull input) := by
  obtain ⟨rfl, rfl⟩ := recognize_sound recognized
  have header (bank : Tuple (Val m.value) (wordPorts arity)) :
      (reindexCaptures perm p.graph).step m input bank = p.graph.step m (perm.pull input) bank :=
    Rows.step_reindex p.row perm m input bank
  simp only [Loop.Graph.denote, initial_reindex, header]

variable {before after : Checked.Phi.Targets}

private theorem denote_reindex_of_checked (accepted : lowerChecked g = some before) (input : WordTuple arity) :
    (reindexCaptures perm g).denote model input = g.denote model (perm.pull input) := by
  obtain ⟨_, recognized, _, _⟩ := lowerChecked_sound accepted
  exact denote_reindex perm recognized model input

theorem observations_reindex (accepted : lowerChecked g = some before)
    (emitted : lowerChecked (reindexCaptures perm g) = some after)
    (input : WordTuple arity) (initial : Memory) :
    rtlBehaviors input initial after.1 = rtlBehaviors (perm.pull input) initial before.1 ∧
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope emitted) =
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory (perm.pull input)) (scope accepted) := by
  have rtl (start : Memory) :
      rtlBehaviors input start after.1 = rtlBehaviors (perm.pull input) start before.1 := by
    ext outcome
    rw [Institution.rtl_behavior_iff emitted, Institution.rtl_behavior_iff accepted,
      denote_reindex_of_checked perm accepted]
  refine ⟨rtl initial, ?_⟩
  ext observation
  refine (Institution.rtl_room_observation_iff emitted input observation).trans
    (Iff.trans ?_ (Institution.rtl_room_observation_iff accepted (perm.pull input) observation).symm)
  cases observation with
  | ret start result finish =>
    obtain ⟨label, payload⟩ := result
    change Memory at start finish
    simp only [Silmaril.Isotope.Institution.Observational.Observation.Holds, rtl]
  | fault _ _ => rfl
  | diverge start =>
    change Memory at start
    simp only [Silmaril.Isotope.Institution.Observational.Observation.Holds, rtl]

variable {right : SourceWithEntry arity rightEntry rightSigs}
variable {rightBefore rightAfter : Checked.Phi.Targets}

theorem reindex_equation_at_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (reindexCaptures perm g) = some after)
    (rightEmitted : lowerChecked (reindexCaptures perm right) = some rightAfter)
    (input : WordTuple arity) (initial : Memory) :
    let original := g.denote model (perm.pull input) = right.denote model (perm.pull input)
    ((Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial) ↔ original) ∧
      ((fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted)) ↔ original) := by
  have rtl := Institution.rtl_equation_at_iff leftEmitted rightEmitted input initial
  rw [denote_reindex_of_checked perm leftChecked, denote_reindex_of_checked perm rightChecked] at rtl
  exact ⟨rtl, (Institution.rtl_room_equation_at_iff leftEmitted rightEmitted input initial).symm.trans rtl⟩

theorem reindex_equation_holds_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (reindexCaptures perm g) = some after)
    (rightEmitted : lowerChecked (reindexCaptures perm right) = some rightAfter) (initial : Memory) :
    let original := (Loop.Institution.Sentence.equation (equation g right)).Holds model
    ((∀ input : WordTuple arity, (Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial)) ↔ original) ∧
      ((∀ input : WordTuple arity, (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted))) ↔ original) := by
  have pulls : (∀ input : WordTuple arity,
        g.denote model (perm.pull input) = right.denote model (perm.pull input)) ↔
      (Loop.Institution.Sentence.equation (equation g right)).Holds model := by
    constructor
    · intro holds old
      have same := InputPermutation.pull_symm (value := model.value) perm old
      exact same ▸ holds (InputPermutation.pull perm.symm old)
    · exact fun holds input => holds (perm.pull input)
  have atInput := fun input => reindex_equation_at_iff perm leftChecked rightChecked leftEmitted rightEmitted input initial
  exact ⟨(forall_congr' fun input => (atInput input).1).trans pulls,
    (forall_congr' fun input => (atInput input).2).trans pulls⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
