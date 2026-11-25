module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Dispatch
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs finalL finalR captured : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {fn : Function V S}

private theorem terminal_return {job : Job m fn.results} {store returnedStore : σ}
    {value : Tuple m.Val fn.results} (ran : Eval primitives job store (.returned value returnedStore)) :
    TerminalPath primitives ⟨Continuation.start job, store⟩ ⟨.returned value .halt, returnedStore⟩ :=
  ⟨ran.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

private theorem terminal_return_excludes_run {source target : Config m σ fn.results}
    (terminal : TerminalPath primitives source target) : ¬ InfiniteTrace (Step primitives) source :=
  RightUnique.not_infinite_of_final (R := Step primitives) (fun _ _ _ a b => _root_.Part.mem_unique a b)
    terminal.path terminal.terminal

private theorem match_return_paths {sourceL sourceR : Config m σ fn.results}
    (paired : CallPair primitives ids mapping fn.results sourceL sourceR) :
    (∀ {valueL : Tuple m.Val fn.results} {store : σ},
      TerminalPath primitives sourceL ⟨.returned valueL .halt, store⟩ →
      ∃ valueR, TupleRelated m ids valueL valueR ∧ TerminalPath primitives sourceR ⟨.returned valueR .halt, store⟩) ∧
    (∀ {valueR : Tuple m.Val fn.results} {store : σ},
      TerminalPath primitives sourceR ⟨.returned valueR .halt, store⟩ →
      ∃ valueL, TupleRelated m ids valueL valueR ∧ TerminalPath primitives sourceL ⟨.returned valueL .halt, store⟩) := by
  cases paired with
  | returned values knownL knownR =>
    constructor
    · intro value store observed
      have same := Option.some.inj (congrArg Config.result ((knownL _).mp observed))
      cases same
      exact ⟨_, values, (knownR _).mpr rfl⟩
    · intro value store observed
      have same := Option.some.inj (congrArg Config.result ((knownR _).mp observed))
      cases same
      exact ⟨_, values, (knownL _).mpr rfl⟩
  | blocked _ knownL knownR =>
    constructor <;> intro _ _ observed
    · cases congrArg Config.result ((knownL _).mp observed)
    · cases congrArg Config.result ((knownR _).mp observed)
  | productive run =>
    have live := productive_infinite run .halt .halt
    constructor <;> intro _ _ observed
    · exact False.elim (terminal_return_excludes_run (fn := fn) observed live.1)
    · exact False.elim (terminal_return_excludes_run (fn := fn) observed live.2)

theorem resume_application {entry : Tuple m.Val args} {inputs : Wires args [] (fn.port :: fn.args)}
    (outputs : Wires args [fn.results] outs) (parent : Continuation.Stack m outs finalL)
    {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args} {store returnedStore : σ} {value : Tuple m.Val fn.results}
    (selected : inputs.read entry PUnit.unit = .cons callee arguments)
    (ran : Eval primitives (.call callee arguments) store (.returned value returnedStore)) :
    ReflTransGen (Step primitives) ⟨.eval (.region (applicationCode fn inputs outputs) entry PUnit.unit) parent, store⟩
      (resumedApplication outputs entry parent value returnedStore) :=
  (((application_eval selected ran).steps (applicationFrame outputs entry parent)).head (.of_next_some rfl)).tail
    (.of_next_some rfl)

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
          (resumedApplication outputs entryL parentL valueL returnedStore)) := by
  have matched := match_return_paths (fn := fn) (calls respects (.closure captures code) arguments store)
  constructor
  · intro value returnedStore observed
    have ran := returns_of_delimited _ observed
    obtain ⟨_, values, path⟩ := matched.1 (terminal_return (fn := fn) ran)
    exact ⟨_, values, resume_application outputs parentR selectR (returns_iff_path.mpr path.path)⟩
  · intro value returnedStore observed
    have ran := returns_of_delimited _ observed
    obtain ⟨_, values, path⟩ := matched.2 (terminal_return (fn := fn) ran)
    exact ⟨_, values, resume_application outputs parentL selectL (returns_iff_path.mpr path.path)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
