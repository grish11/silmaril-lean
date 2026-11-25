module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Application
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open PartialLink.Invocation (start_linked start_error_iff)
open Isomorphism.Invocation (request)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs params results finalL finalR : Ports (Ty V S)}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}

private theorem terminal_of_eval {job : Job m results} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ results}
    (ran : Eval primitives job store outcome) :
    SingleTheta.TerminalOutcome primitives ⟨Continuation.start job, store⟩ outcome := by
  intro target
  apply TerminalPath.target_iff
  refine ⟨ran.steps .halt, ?_⟩
  cases outcome with
  | returned => exact fun _ stepped => _root_.Part.notMem_none _ stepped
  | blocked => exact fun _ => (ran.blocks .halt).no_step

private theorem invoke_regions {context : Ports (Ty V S)}
    {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL results}
    {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR results}
    {capturesL capturesR : Tuple m.Val context} {argsL argsR : Tuple m.Val params} {store : σ}
    (observed : RegionPair primitives ids mapping left right
      (prependContext argsL capturesL) (prependContext argsR capturesR) store) :
    CallPair primitives ids mapping results
      ⟨Continuation.start (.call (.closure capturesL left.toGraph) argsL), store⟩
      ⟨Continuation.start (.call (.closure capturesR right.toGraph) argsR), store⟩ := by
  have actualL := open_lambda left capturesL argsL
  have actualR := open_lambda right capturesR argsR
  cases observed with
  | returned values ranL ranR =>
    exact .returned values (terminal_of_eval (.call (actualL.symm ▸ ranL)))
      (terminal_of_eval (.call (actualR.symm ▸ ranR)))
  | blocked stopped =>
    obtain ⟨ranL, ranR⟩ := block_evals stopped
    exact .blocked stopped (terminal_of_eval (.call (actualL.symm ▸ ranL)))
      (terminal_of_eval (.call (actualR.symm ▸ ranR)))
  | productive run =>
    exact .productive (productive_map run (fun ran => ⟨_, .call (actualL.symm ▸ ran)⟩)
      (fun ran => ⟨_, .call (actualR.symm ▸ ran)⟩))

theorem calls (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ScheduledLambda m ids mapping params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ) :
    CallPair primitives ids mapping results
      ⟨Continuation.start (.call calleeL argsL), store⟩
      ⟨Continuation.start (.call calleeR argsR), store⟩ := by
  cases callees with
  | closure captures code =>
    exact invoke_regions (regions code respects (prepend_related captures arguments) store)
  | application calleeCaptures calleeIso code captures wires outputs =>
    exact invoke_regions (captured_application code respects wires outputs
      (prepend_related captures arguments) calleeCaptures calleeIso store)

private theorem terminal_excludes_infinite {source : Config m σ outs}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (ran : SingleTheta.TerminalOutcome primitives source outcome) : ¬ InfiniteTrace (Step primitives) source := by
  have reached := (ran (outcome.atStack .halt)).mpr rfl
  exact RightUnique.not_infinite_of_final (R := Step primitives)
    (fun _ _ _ a b => _root_.Part.mem_unique a b) reached.path reached.terminal

theorem infinite_iff {sourceL sourceR : Config m σ outs}
    (paired : CallPair primitives ids mapping outs sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR := by
  cases paired with
  | returned _ ranL ranR =>
    exact iff_of_false (terminal_excludes_infinite ranL) (terminal_excludes_infinite ranR)
  | blocked _ ranL ranR =>
    exact iff_of_false (terminal_excludes_infinite ranL) (terminal_excludes_infinite ranR)
  | productive run =>
    have infinite := productive_infinite run .halt .halt
    exact ⟨fun _ => infinite.2, fun _ => infinite.1⟩

theorem link_then_invoke (respects : ActionsRespect primitives ids)
    {left : Omega Op args outs sigsL} {right : Omega Op args outs sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Ordered Op (renameVertex positions) args outs left.toTerm.region right.toTerm.region)
    {unitL unitR : Nat} (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputL inputR : Tuple m.Val args} (imports : TupleRelated m ids inputL inputR)
    (port : Port outs (.value (.function params results)))
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ)
    (admitted : ∀ {exportsL exportsR : Tuple m.Val outs} {post : σ},
      Links primitives unitL left inputL store (.linked exportsL post) →
      Links primitives unitR right inputR store (.linked exportsR post) →
      TupleRelated m ids exportsL exportsR →
      ScheduledLambda m ids mapping params results (exportsL.get port) (exportsR.get port)) :
    DispatchPair primitives ids (renameVertex positions) mapping results
      ((request unitL left inputL port argsL store).start primitives)
      ((request unitR right inputR port argsR store).start primitives) := by
  have paired := link_related respects iso schedule identities imports store
  have linkedL : Links primitives unitL left inputL store (link primitives unitL left inputL store) := link_spec
  have linkedR : Links primitives unitR right inputR store (link primitives unitR right inputR store) := link_spec
  generalize link primitives unitL left inputL store = outcomeL at paired linkedL
  generalize link primitives unitR right inputR store = outcomeR at paired linkedR
  cases paired with
  | undefined address identity sites stopped =>
    rw [(start_error_iff (request := request unitL left inputL port argsL store) (primitives := primitives)).mpr linkedL,
      (start_error_iff (request := request unitR right inputR port argsR store) (primitives := primitives)).mpr linkedR]
    exact .linkBlocked address identity sites stopped
  | linked exports post =>
    rw [start_linked (request := request unitL left inputL port argsL store) (primitives := primitives) linkedL,
      start_linked (request := request unitR right inputR port argsR store) (primitives := primitives) linkedR]
    exact .invoked (calls respects (admitted linkedL linkedR exports) arguments post)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
