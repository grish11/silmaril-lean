module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open SingleTheta (Carries)
open Isomorphism.Invocation (loopVertex)
open Isomorphism.Proofs (LocalsRelated read_same)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args entry carried returned outs params : Ports (Ty V S)} {extra : Nat}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}
variable {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
variable {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
variable {inputL inputR : Tuple m.Val args} {store : σ}
variable {locL locR : Location} {stopL stopR : Block m σ outs}

theorem prepend_related {context : Ports (Ty V S)}
    {capturesL capturesR : Tuple m.Val context} {argsL argsR : Tuple m.Val params}
    (captures : TupleRelated m ids capturesL capturesR) (arguments : TupleRelated m ids argsL argsR) :
    TupleRelated m ids (prependContext argsL capturesL) (prependContext argsR capturesR) := by
  induction context with
  | nil => cases captures; exact arguments
  | cons _ _ ih => cases captures with | cons head tail => exact .cons head (ih tail)

theorem open_lambda {context : Ports (Ty V S)}
    (code : NestedTheta.Term (Instruction Op) (context ++ params) [] sigs outs)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    Job.openClosure m (.closure captures code.toGraph) arguments =
      .region code (prependContext arguments captures) PUnit.unit :=
  congrArg (fun term => Job.region (m := m) (past := []) term (prependContext arguments captures) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph code)

theorem application_eval {fn : Function V S} {entry : Tuple m.Val args}
    {inputs : Wires args [] (fn.port :: fn.args)} {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args}
    {outcome : Continuation.Partial.Outcome m σ fn.results}
    (selected : inputs.read entry PUnit.unit = .cons callee arguments)
    (ran : Eval primitives (.call callee arguments) store outcome) :
    Eval primitives (.node (applicationVertex fn inputs).kind (applicationVertex fn inputs).childSigs
      (fun i => i.elim0) (inputs.read entry PUnit.unit)) store outcome :=
  selected.symm ▸ Eval.apply (fn := fn) (cs := fun _ => []) (children := fun i => i.elim0) ran

theorem block_observations
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    locR = locL.rename mapping ∧ SitesRelated m ids stopL.site stopR.site ∧ stopL.store = stopR.store := by
  induction stopped with
  | acyclic _ sites _ _ => exact ⟨rfl, sites, rfl⟩
  | theta _ _ _ _ _ _ _ sites _ _ => exact ⟨rfl, sites, rfl⟩
  | gamma _ _ _ _ _ ih => exact ⟨congrArg (Location.gamma _) ih.1, ih.2⟩
  | loop _ _ _ _ _ _ _ ih => exact ⟨congrArg Location.loop ih.1, ih.2⟩
  | application _ _ _ _ _ ih => exact ⟨congrArg Location.application ih.1, ih.2⟩

theorem block_evals
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    Eval primitives (.region left inputL PUnit.unit) store stopL.outcome ∧
    Eval primitives (.region right inputR PUnit.unit) store stopR.outcome := by
  induction stopped with
  | acyclic _ _ ranL ranR => exact ⟨ranL.eval, ranR.eval⟩
  | @theta _ _ _ sigsL sigsR map left right _ _ _ _ first current _ _ _ _
      initial outputs startsL startsR startsStore completed location sites firstL firstR =>
    have done : SingleTheta.Finishes primitives (map.child 0 0) left right first _ _ :=
      ⟨current, completed, .blocked location sites firstL firstR⟩
    obtain ⟨ranL, ranR⟩ := done.eval
    rw [startsL, startsStore] at ranL
    rw [startsR, startsStore] at ranR
    exact ⟨.bindBlocked (node := loopVertex initial sigsL) (.theta ranL),
      .bindBlocked (node := loopVertex initial sigsR) (.theta ranR)⟩
  | @gamma _ _ _ _ extra _ sigsL sigsR armsL armsR entryL entryR _ _ store tag _ _ stopL stopR
      inputs outputs selectedL selectedR _ ih =>
    obtain ⟨childL, childR⟩ := ih
    cases stopL
    cases stopR
    refine ⟨.bindBlocked (node := vertex inputs sigsL) ?_, .bindBlocked (node := vertex inputs sigsR) ?_⟩
    · exact selectedL.symm ▸ Eval.gamma (cs := sigsL) (children := armsL) childL
    · exact selectedR.symm ▸ Eval.gamma (cs := sigsR) (children := armsR) childR

  | @loop _ _ _ sigsL sigsR _ _ _ _ _ _ _ _ _ _ stopL stopR
      initial outputs startsL startsR startsStore completed _ ih =>
    cases stopL
    cases stopR
    have ran := rewind completed ⟨Eval.loopBlocked ih.1, Eval.loopBlocked ih.2⟩
    obtain ⟨ranL, ranR⟩ := ran
    rw [startsL, startsStore] at ranL
    rw [startsR, startsStore] at ranR
    exact ⟨.bindBlocked (node := loopVertex initial sigsL) (.theta ranL),
      .bindBlocked (node := loopVertex initial sigsR) (.theta ranR)⟩

  | @application _ _ _ fn _ _ _ left right captL captR _ _ argsL argsR _ _ _ stopL stopR
      inputs outputs selectedL selectedR _ ih =>
    cases stopL
    cases stopR
    have ranL := Eval.call ((open_lambda left captL argsL).symm ▸ ih.1)
    have ranR := Eval.call ((open_lambda right captR argsR).symm ▸ ih.2)
    exact ⟨.bindBlocked (node := applicationVertex fn inputs) (application_eval selectedL ranL),
      .bindBlocked (node := applicationVertex fn inputs) (application_eval selectedR ranR)⟩

private theorem selected_tuple {valuesL valuesR : Tuple m.Val (.control (extra + 2) :: entry)}
    (related : TupleRelated m ids valuesL valuesR) :
    ∃ tag nextL nextR, valuesL = .cons (.control tag) nextL ∧ valuesR = .cons (.control tag) nextR ∧
      TupleRelated m ids nextL nextR := by
  cases related with
  | cons head tail =>
    cases head with
    | control tag => exact ⟨tag, _, _, rfl, rfl, tail⟩

/-- γ congruence uses the related selector to choose a single pair of arms.
All three outcomes keep the enclosing frame or resume its wiring suffix. -/
theorem gamma
    {childSigsL childSigsR : Fin (extra + 2) → List (Ports (Ty V S))}
    {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsL i) returned}
    {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsR i) returned}
    (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
    (arms : ∀ tag {nextL nextR : Tuple m.Val entry}, TupleRelated m ids nextL nextR →
      RegionPair primitives ids (mapping.child 0 tag.val) (armsL tag) (armsR tag) nextL nextR store)
    (related : TupleRelated m ids inputL inputR) :
    RegionPair primitives ids mapping (code inputs armsL outputs) (code inputs armsR outputs) inputL inputR store := by
  obtain ⟨tag, nextL, nextR, selectL, selectR, values⟩ :=
    selected_tuple (read_same related LocalsRelated.empty inputs)
  cases arms tag values with
  | @returned _ _ finalStore paired ranL ranR =>
    have locals := LocalsRelated.empty.snoc (fun _ _ same => same) rfl paired
    refine .returned (finalStore := finalStore) (read_same related locals outputs)
      (.bind (node := vertex inputs childSigsL) ?_ (.ret outputs _ _ _))
      (.bind (node := vertex inputs childSigsR) ?_ (.ret outputs _ _ _))
    · exact selectL.symm ▸ Eval.gamma (cs := childSigsL) (children := armsL) ranL
    · exact selectR.symm ▸ Eval.gamma (cs := childSigsR) (children := armsR) ranR
  | blocked stopped => exact .blocked (.gamma inputs outputs selectL selectR stopped)
  | productive run =>
    refine .productive (productive_map run ?_ ?_)
    · intro target pending reached
      refine ⟨.bind (past := []) (.ret outputs) inputL PUnit.unit pending, .inside (node := vertex inputs childSigsL) ?_⟩
      exact selectL.symm ▸ Feedback.Reaches.gamma (cs := childSigsL) (children := armsL) reached
    · intro target pending reached
      refine ⟨.bind (past := []) (.ret outputs) inputR PUnit.unit pending, .inside (node := vertex inputs childSigsR) ?_⟩
      exact selectR.symm ▸ Feedback.Reaches.gamma (cs := childSigsR) (children := armsR) reached

private theorem initial_restart {body : LoopBody Op carried sigsL}
    (initial : Wires args [] carried) (outputs : Wires args [carried] outs) (input : Tuple m.Val args) (store : σ) :
    Feedback.Reaches primitives (.region (loopCode initial body outputs) input PUnit.unit) store
      ⟨carried, sigsL, body, (initial.read input PUnit.unit, store)⟩
      (.bind (past := []) (.ret outputs) input PUnit.unit .empty) :=
  .inside (node := loopVertex initial sigsL)
    (.theta (.restart (input := (initial.read input PUnit.unit, store))
      (current := (initial.read input PUnit.unit, store)) .refl))

/-- Compose θ with any paired observation of its fresh body activations. -/
theorem loop {bodyL : LoopBody Op carried sigsL} {bodyR : LoopBody Op carried sigsR}
    (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
    (observe : ∀ {nextL nextR : Tuple m.Val carried}, TupleRelated m ids nextL nextR → ∀ store,
      RegionPair primitives ids (mapping.child 0 0) bodyL bodyR nextL nextR store)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping (loopCode initial bodyL outputs)
      (loopCode initial bodyR outputs) inputL inputR store := by
  let first : Carries m ids σ carried :=
    ⟨initial.read inputL PUnit.unit, initial.read inputR PUnit.unit,
      read_same inputs LocalsRelated.empty initial, store⟩
  cases classify (fun current => observe current.related current.store) first with
  | outer live =>
    exact .productive (.feedback live (initial_restart initial outputs inputL store)
      (initial_restart initial outputs inputR store))
  | activation completed observed =>
    cases observed with
    | @exited _ _ _ finalStore exits values ranL ranR =>
      have ran := rewind completed ⟨Eval.stop ranL exits, Eval.stop ranR exits⟩
      have locals := LocalsRelated.empty.snoc (fun _ _ same => same) rfl values
      exact .returned (finalStore := finalStore) (read_same inputs locals outputs)
        (.bind (node := loopVertex initial sigsL) (.theta ran.1) (.ret outputs _ _ _))
        (.bind (node := loopVertex initial sigsR) (.theta ran.2) (.ret outputs _ _ _))
    | blocked stopped =>
      exact .blocked (.loop initial outputs rfl rfl rfl completed stopped)
    | inner live =>
      refine .productive (productive_map live ?_ ?_)
      · intro target pending reached
        exact ⟨.bind (past := []) (.ret outputs) inputL PUnit.unit (.loop bodyL pending),
          .inside (node := loopVertex initial sigsL) (.theta (.iteration (left_completed completed) reached))⟩
      · intro target pending reached
        exact ⟨.bind (past := []) (.ret outputs) inputR PUnit.unit (.loop bodyR pending),
          .inside (node := loopVertex initial sigsR) (.theta (.iteration (right_completed completed) reached))⟩

private theorem acyclic {bodyL : Graph Op args [] sigsL outs} {bodyR : Graph Op args [] sigsR outs}
    (admitted : OrderedGraph mapping bodyL bodyR) (respects : ActionsRespect primitives ids)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping (embed bodyL.toTerm) (embed bodyR.toTerm) inputL inputR store := by
  obtain ⟨_, _, paired⟩ := Local.graph_evaluate admitted respects inputs store
  cases paired with
  | returned values ranL ranR => exact .returned values ranL ranR
  | blocked location sites ranL ranR => exact .blocked (.acyclic location sites ranL ranR)

theorem regions (admitted : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping left right inputL inputR store := by
  induction admitted generalizing store with
  | acyclic admitted => exact acyclic admitted respects inputs store
  | theta initial outputs _ admitted =>
    exact loop initial outputs (fun related store => acyclic admitted respects related store) inputs store
  | gamma wiring outputs _ _ children =>
    exact gamma wiring outputs (by
      intro tag _ _ paired
      exact children tag paired store) inputs
  | loop initial outputs _ _ body => exact loop initial outputs body inputs store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
