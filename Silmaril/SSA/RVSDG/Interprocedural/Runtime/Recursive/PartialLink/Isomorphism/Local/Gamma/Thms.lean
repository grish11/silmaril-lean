module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Dispatch
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Application
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Resumption

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma

open Continuation.Partial
open Isomorphism.Invocation (request)
open SingleTheta (Carries)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs entry returned params results finalL finalR : Ports (Ty V S)} {extra : Nat}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
variable {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
variable {inputL inputR : Tuple m.Val args} {store : σ}
variable {locL locR : Location} {stopL stopR : Block m σ outs}

/-- A block keeps the chosen γ arm positions, mapped local address, typed
operands of the same primitive, and exact attempt store. -/
theorem BlockPair.observations
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    locR = locL.rename mapping ∧ SitesRelated m ids stopL.site stopR.site ∧ stopL.store = stopR.store :=
  Proofs.block_observations stopped

/-- The address certificate erases to the actual independent evaluations,
with each enclosing γ continuation and θ frame retained. -/
theorem BlockPair.evals
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    Eval primitives (.region left inputL PUnit.unit) store stopL.outcome ∧
    Eval primitives (.region right inputR PUnit.unit) store stopR.outcome :=
  Proofs.block_evals stopped

/-- γ congruence for paired ordered behaviors. Only the common selected
arm is evaluated. On return the suffix reads the related results. On block
or productive feedback it remains pending in each real machine. -/
theorem gamma
    {childSigsL childSigsR : Fin (extra + 2) → List (Ports (Ty V S))}
    {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsL i) returned}
    {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsR i) returned}
    (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
    (arms : ∀ tag {nextL nextR : Tuple m.Val entry}, TupleRelated m ids nextL nextR →
      RegionPair primitives ids (mapping.child 0 tag.val) (armsL tag) (armsR tag) nextL nextR store)
    (related : TupleRelated m ids inputL inputR) :
    RegionPair primitives ids mapping (code inputs armsL outputs) (code inputs armsR outputs) inputL inputR store :=
  Proofs.gamma inputs outputs arms related

/-- A depth-independent θ congruence over observers of fresh activations.
Each related selector either exits or restarts with its full carry. The
chosen block or productive child keeps the θ and saved suffix frames. -/
theorem loop {carried : Ports (Ty V S)} {bodyL : LoopBody Op carried sigsL} {bodyR : LoopBody Op carried sigsR}
    (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
    (observe : ∀ {nextL nextR : Tuple m.Val carried}, TupleRelated m ids nextL nextR → ∀ store,
      RegionPair primitives ids (mapping.child 0 0) bodyL bodyR nextL nextR store)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping (loopCode initial bodyL outputs)
      (loopCode initial bodyR outputs) inputL inputR store :=
  Proofs.loop initial outputs observe inputs store

section Feedback

variable {carried : Ports (Ty V S)} {bodyL : LoopBody Op carried sigsL} {bodyR : LoopBody Op carried sigsR}
variable {first current next : Carries m ids σ carried}

/-- Distinguish an exit, block or productive child after finite feedback
from a stream of completed feedback iterations. Each successor comes
from paired activation evaluation. -/
theorem loop_observations
    (observe : ∀ input : Carries m ids σ carried,
      RegionPair primitives ids mapping bodyL bodyR input.left input.right input.store)
    (first : Carries m ids σ carried) : LoopPair primitives mapping bodyL bodyR first :=
  Proofs.classify observe first

/-- Every pair of completed activations gives two positive segments with
unchanged parent frames and the exact next carried tuple and store. -/
theorem IterationPair.steps (paired : IterationPair primitives bodyL bodyR first next)
    (parentL : Continuation.Stack m carried finalL) (parentR : Continuation.Stack m carried finalR) :
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsL bodyL (first.left, first.store)).config parentL)
      ((Feedback.Restart.mk carried sigsL bodyL (next.left, next.store)).config parentL) ∧
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsR bodyR (first.right, first.store)).config parentR)
      ((Feedback.Restart.mk carried sigsR bodyR (next.right, next.store)).config parentR) :=
  Proofs.iteration_steps paired parentL parentR

theorem IterationPair.replay
    {outcomeL outcomeR : Continuation.Partial.Outcome m σ carried}
    (completed : ReflTransGen (IterationPair primitives bodyL bodyR) first current)
    (later : Eval primitives (.iteration bodyL current.left) current.store outcomeL ∧
      Eval primitives (.iteration bodyR current.right) current.store outcomeR) :
    Eval primitives (.iteration bodyL first.left) first.store outcomeL ∧
    Eval primitives (.iteration bodyR first.right) first.store outcomeR :=
  Proofs.rewind completed later

theorem IterationPair.completed (completed : ReflTransGen (IterationPair primitives bodyL bodyR) first current) :
    ReflTransGen (Feedback.Iteration primitives bodyL) (first.left, first.store) (current.left, current.store) ∧
    ReflTransGen (Feedback.Iteration primitives bodyR) (first.right, first.store) (current.right, current.store) :=
  ⟨Proofs.left_completed completed, Proofs.right_completed completed⟩

theorem IterationPair.runs (live : InfiniteTrace (IterationPair primitives bodyL bodyR) first) :
    Feedback.Run primitives bodyL (first.left, first.store) ∧ Feedback.Run primitives bodyR (first.right, first.store) :=
  Proofs.outer_runs live

end Feedback

theorem regions (admitted : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping left right inputL inputR store :=
  Proofs.regions admitted respects inputs store

section Application

variable {captured : Ports (Ty V S)} {fn : Function V S}

/-- Congruence for a selected call to two actual closures with scheduled
call-free bodies. The application reads these closures and the related
arguments from its real operand wires. Its typed suffix is preserved. -/
theorem application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
    {entryL entryR : Tuple m.Val args} (entries : TupleRelated m ids entryL entryR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    {argsL argsR : Tuple m.Val fn.args} (arguments : TupleRelated m ids argsL argsR)
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn inputs outputs) (applicationCode fn inputs outputs)
      entryL entryR store :=
  Proofs.application code respects inputs outputs entries captures arguments selectL selectR store

/-- Replay a successful call into the caller's actual suffix with the
returned tuple bound once and the exact final store. -/
theorem resume_application {entry : Tuple m.Val args} {inputs : Wires args [] (fn.port :: fn.args)}
    (outputs : Wires args [fn.results] outs) (parent : Continuation.Stack m outs finalL)
    {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args} {store returnedStore : σ} {value : Tuple m.Val fn.results}
    (selected : inputs.read entry PUnit.unit = .cons callee arguments)
    (ran : Eval primitives (.call callee arguments) store (.returned value returnedStore)) :
    ReflTransGen (Step primitives) ⟨.eval (.region (applicationCode fn inputs outputs) entry PUnit.unit) parent, store⟩
      (resumedApplication outputs entry parent value returnedStore) :=
  Proofs.resume_application outputs parent selected ran

/-- A first return to the saved application frame on either side
reflects to a paired return and actual suffix resumption on the other,
with related full tuples at the same returned store. -/
theorem application_resumption
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
    {entryL entryR : Tuple m.Val args} {captL captR : Tuple m.Val captured}
    (captures : TupleRelated m ids captL captR)
    {argsL argsR : Tuple m.Val fn.args} (arguments : TupleRelated m ids argsL argsR)
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR)
    (parentL : Continuation.Stack m outs finalL) (parentR : Continuation.Stack m outs finalR) (store : σ) :
    (∀ {valueL : Tuple m.Val fn.results} {returnedStore : σ},
      CallReturnsTo primitives (.closure captL left.toGraph) argsL (applicationFrame outputs entryL parentL)
        store valueL returnedStore →
      ∃ valueR, TupleRelated m ids valueL valueR ∧
        ReflTransGen (Step primitives)
          ⟨.eval (.region (applicationCode fn inputs outputs) entryR PUnit.unit) parentR, store⟩
          (resumedApplication outputs entryR parentR valueR returnedStore)) ∧
    (∀ {valueR : Tuple m.Val fn.results} {returnedStore : σ},
      CallReturnsTo primitives (.closure captR right.toGraph) argsR (applicationFrame outputs entryR parentR)
        store valueR returnedStore →
      ∃ valueL, TupleRelated m ids valueL valueR ∧
        ReflTransGen (Step primitives)
          ⟨.eval (.region (applicationCode fn inputs outputs) entryL PUnit.unit) parentL, store⟩
          (resumedApplication outputs entryL parentL valueL returnedStore)) :=
  Proofs.application_resumption code respects inputs outputs captures arguments selectL selectR parentL parentR store

end Application

/-- Each side replays the finite route to the common paired feedback
stream, then positive restart segments with its own saved frame. -/
theorem ProductivePair.infinite {jobL jobR : Job m outs}
    (run : ProductivePair primitives ids jobL jobR store)
    (frameL : Continuation.Stack m outs finalL) (frameR : Continuation.Stack m outs finalR) :
    InfiniteTrace (Step primitives) ⟨.eval jobL frameL, store⟩ ∧
    InfiniteTrace (Step primitives) ⟨.eval jobR frameR, store⟩ :=
  Proofs.productive_infinite run frameL frameR

/-- At actual successful dispatch, infinite microsteps transport in
both directions. Finite returns and selected blocks are terminal. -/
theorem CallPair.infinite_iff {sourceL sourceR : Config m σ outs}
    (paired : CallPair primitives ids mapping outs sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR :=
  Proofs.infinite_iff paired

/-- Compose ordered partial ω linking with paired code for the actual
export, including a statically witnessed application. Terminal observations
reflect back to the paired endpoints. -/
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
      ((request unitR right inputR port argsR store).start primitives) :=
  Proofs.link_then_invoke respects iso schedule identities imports port arguments store admitted

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma
