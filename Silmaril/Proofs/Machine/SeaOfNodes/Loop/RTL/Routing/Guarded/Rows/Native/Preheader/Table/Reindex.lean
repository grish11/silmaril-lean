module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open CategoryTheory (Discrete)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp model)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)
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
    cases wire with
    | arg port =>
      exact congrArg₂ Tuple.cons (congrArg (Origin.arg (past := past)) (InputPermutation.port_symm perm port)) ih
    | output index port => exact congrArg (Tuple.cons (.output index port)) ih

private theorem flow_symm {past : List (List PortTy)}
    (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    reindexFlow perm.symm (reindexFlow perm flow) = flow := by
  induction flow with
  | nil => rfl
  | cons op args rest ih =>
    change Dataflow.cons op (InputPermutation.column perm.symm (perm.column args))
      (reindexFlow perm.symm (reindexFlow perm rest)) = _
    rw [column_symm, ih]

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
    exact congrArg₂ (fun flow inputs => Loop.Graph.mk flow header inputs predicate result)
      (flow_symm perm preheader) columns

variable (mapping : InputMap arity)

private theorem eval_flow (m : Model.{0, 0, w} WordOp)
    {past sigs : List (List PortTy)} (flow : Dataflow WordOp (wordPorts arity) past sigs)
    (input : Tuple (Val m.value) (wordPorts arity)) (locals : Locals (Val m.value) past) :
    (mapCaptureFlow mapping flow).eval m input locals = flow.eval m (mapping.pull input) locals := by
  induction flow with
  | nil => rfl
  | cons op args rest ih =>
    simp only [mapCaptureFlow, Dataflow.eval, InputMap.read_column mapping]
    exact ih _

theorem initial_mapCaptures (g : SourceWithEntry arity entrySigs sigs)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (mapCaptures mapping g).initial m input = g.initial m (mapping.pull input) := by
  let column : EntryColumnWith arity entrySigs := g.phiInputs .entry
  exact (congrArg (fun locals => (mapping.column column).read input locals)
    (eval_flow mapping m g.preheader input PUnit.unit)).trans
    (mapping.read_column input column (g.preheader.eval m (mapping.pull input) PUnit.unit))

variable {g : SourceWithEntry arity entrySigs sigs} {p : Plan arity entrySigs}

theorem denote_mapCaptures (recognized : recognize g = some p)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (mapCaptures mapping g).denote m input = g.denote m (mapping.pull input) := by
  obtain ⟨rfl, rfl⟩ := recognize_sound recognized
  have header (bank : Tuple (Val m.value) (wordPorts arity)) :
      (mapCaptures mapping p.graph).step m input bank = p.graph.step m (mapping.pull input) bank :=
    Rows.step_capture_congr p.row m input (mapping.pull input) bank
  simp only [Loop.Graph.denote, initial_mapCaptures, header]

variable {before after : Checked.Phi.Targets}

private theorem denote_mapCaptures_of_checked (accepted : lowerChecked g = some before) (input : WordTuple arity) :
    (mapCaptures mapping g).denote model input = g.denote model (mapping.pull input) := by
  obtain ⟨_, recognized, _, _⟩ := lowerChecked_sound accepted
  exact denote_mapCaptures mapping recognized model input

theorem observations_mapCaptures (accepted : lowerChecked g = some before)
    (emitted : lowerChecked (mapCaptures mapping g) = some after)
    (input : WordTuple arity) (initial : Memory) :
    rtlBehaviors input initial after.1 = rtlBehaviors (mapping.pull input) initial before.1 ∧
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope emitted) =
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory (mapping.pull input)) (scope accepted) := by
  have rtl (start : Memory) :
      rtlBehaviors input start after.1 = rtlBehaviors (mapping.pull input) start before.1 := by
    ext outcome
    rw [Institution.rtl_behavior_iff emitted, Institution.rtl_behavior_iff accepted,
      denote_mapCaptures_of_checked mapping accepted]
  refine ⟨rtl initial, ?_⟩
  ext observation
  refine (Institution.rtl_room_observation_iff emitted input observation).trans
    (Iff.trans ?_ (Institution.rtl_room_observation_iff accepted (mapping.pull input) observation).symm)
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

theorem mapCaptures_equation_at_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (mapCaptures mapping g) = some after)
    (rightEmitted : lowerChecked (mapCaptures mapping right) = some rightAfter)
    (input : WordTuple arity) (initial : Memory) :
    let original := g.denote model (mapping.pull input) = right.denote model (mapping.pull input)
    ((Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial) ↔ original) ∧
      ((fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted)) ↔ original) := by
  have rtl := Institution.rtl_equation_at_iff leftEmitted rightEmitted input initial
  rw [denote_mapCaptures_of_checked mapping leftChecked, denote_mapCaptures_of_checked mapping rightChecked] at rtl
  exact ⟨rtl, (Institution.rtl_room_equation_at_iff leftEmitted rightEmitted input initial).symm.trans rtl⟩

theorem mapCaptures_equation_holds_iff (leftChecked : lowerChecked g = some before)
    (rightChecked : lowerChecked right = some rightBefore)
    (leftEmitted : lowerChecked (mapCaptures mapping g) = some after)
    (rightEmitted : lowerChecked (mapCaptures mapping right) = some rightAfter) (initial : Memory) :
    let image := ∀ old ∈ Set.range (fun input : WordTuple arity => mapping.pull input),
      g.denote model old = right.denote model old
    ((∀ input : WordTuple arity, (Sentence.eq after.1 rightAfter.1).Holds (rtlBehaviors input initial)) ↔ image) ∧
      ((∀ input : WordTuple arity, (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
        (Sentence.eq (scope leftEmitted) (scope rightEmitted))) ↔ image) := by
  have pulls : (∀ input : WordTuple arity,
        g.denote model (mapping.pull input) = right.denote model (mapping.pull input)) ↔
      ∀ old ∈ Set.range (fun input : WordTuple arity => mapping.pull input),
        g.denote model old = right.denote model old := by
    constructor
    · rintro holds _ ⟨input, rfl⟩
      exact holds input
    · exact fun holds input => holds _ ⟨input, rfl⟩
  have atInput input := mapCaptures_equation_at_iff mapping leftChecked rightChecked leftEmitted rightEmitted
    input initial
  exact ⟨(forall_congr' fun input => (atInput input).1).trans pulls,
    (forall_congr' fun input => (atInput input).2).trans pulls⟩

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
  have atInput input := mapCaptures_equation_at_iff (fun i => perm i) leftChecked rightChecked
    leftEmitted rightEmitted input initial
  exact ⟨(forall_congr' fun input => (atInput input).1).trans pulls,
    (forall_congr' fun input => (atInput input).2).trans pulls⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
