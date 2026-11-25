module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Defs

/-! Selected γ composition for ordered partial execution. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma

open Continuation.Partial
open Continuation.Descent (Pending)
open Relation (ReflTransGen)
open SingleTheta (Carries)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs entry returned carried params : Ports (Ty V S)} {extra : Nat}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}

abbrev vertex (inputs : Wires args [] (.control (extra + 2) :: entry))
    (sigs : Fin (extra + 2) → List (Ports (Ty V S))) :
    NestedTheta.Node (Instruction Op) args [] returned :=
  ⟨_, .base (.gamma extra), inputs, sigs⟩

/-- A single γ followed by its typed result wiring. The suffix may read
the original region arguments as well as the selected arm's outputs. -/
abbrev code (inputs : Wires args [] (.control (extra + 2) :: entry))
    {sigs : Fin (extra + 2) → List (Ports (Ty V S))}
    (arms : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigs i) returned)
    (outputs : Wires args [returned] outs) : NestedTheta.Term (Instruction Op) args [] [returned] outs :=
  .bind (vertex inputs sigs) arms (.ret outputs)

abbrev applicationVertex (fn : Function V S) (inputs : Wires args [] (fn.port :: fn.args)) :
    NestedTheta.Node (Instruction Op) args [] fn.results :=
  ⟨_, .base (.simple (.apply fn)), inputs, fun _ => []⟩

/-- A single application followed by its typed result wiring. The
ordinary binding saves the caller's entry and suffix across dispatch. -/
abbrev applicationCode (fn : Function V S) (inputs : Wires args [] (fn.port :: fn.args))
    (outputs : Wires args [fn.results] outs) :
    NestedTheta.Term (Instruction Op) args [] [fn.results] outs :=
  .bind (applicationVertex fn inputs) (fun i => i.elim0) (.ret outputs)

/-- The application and its closure dispatch share this ordinary
binding frame. The frame saves the entire caller entry. -/
abbrev applicationFrame {head final : Ports (Ty V S)} (outputs : Wires args [head] outs)
    (entry : Tuple m.Val args) (parent : Continuation.Stack m outs final) : Continuation.Stack m head final :=
  .resume (past := []) (.ret outputs) entry PUnit.unit parent

def resumedApplication {head final : Ports (Ty V S)} (outputs : Wires args [head] outs)
    (entry : Tuple m.Val args) (parent : Continuation.Stack m outs final)
    (value : Tuple m.Val head) (store : σ) : Config m σ final :=
  ⟨.eval (.region (.ret outputs) entry (Locals.snoc (past := []) PUnit.unit value)) parent, store⟩

/-- The first actual return of the selected call to its saved binding. -/
abbrev CallReturnsTo {fn : Function V S} {final : Ports (Ty V S)} (primitives : Primitives m σ)
    (callee : m.Val fn.port) (arguments : Tuple m.Val fn.args) (frame : Continuation.Stack m fn.results final)
    (store : σ) (value : Tuple m.Val fn.results) (returnedStore : σ) : Prop :=
  ReflTransGen (InsideStep primitives frame) ⟨.eval (.call callee arguments) frame, store⟩
    ⟨.returned value frame, returnedStore⟩

abbrev LoopBody (Op : Dialect.{u, v} (ValueSort V S) S) (carried : Ports (Ty V S))
    (sigs : List (Ports (Ty V S))) :=
  NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)

/-- An outer θ with a wiring suffix. Its activation is scoped in fresh
locals, and the suffix also has access to the original arguments. -/
abbrev loopCode (initial : Wires args [] carried) (body : LoopBody Op carried sigs)
    (outputs : Wires args [carried] outs) :
    NestedTheta.Term (Instruction Op) args [] [carried] outs :=
  .bind (Isomorphism.Invocation.loopVertex initial sigs) (fun _ => body) (.ret outputs)

/-- A positive outer iteration requires a whole successful activation on
each side, including any inner θ, followed by the actual feedback edge. -/
def IterationPair (primitives : Primitives m σ) (left : LoopBody Op carried sigsL) (right : LoopBody Op carried sigsR)
    (input next : Carries m ids σ carried) : Prop :=
  Feedback.Iteration primitives left (input.left, input.store) (next.left, next.store) ∧
  Feedback.Iteration primitives right (input.right, input.store) (next.right, next.store)

/-- The outer γ, θ and application bindings are at vertex zero.
Structural child maps choose an arm or loop body. Application follows
the selected closure's separate address map. -/
inductive Location where
  | acyclic (inner : Local.Location)
  | theta (inner : Local.Location)
  | gamma (arm : Nat) (inner : Location)
  | loop (inner : Location)
  | application (inner : Location)
  deriving DecidableEq, Repr

def Location.rename (mapping : Renaming) : Location → Location
  | .acyclic inner => .acyclic (mapping.location inner)
  | .theta inner => .theta ((mapping.child 0 0).location inner)
  | .gamma arm inner => .gamma arm (inner.rename (mapping.child 0 arm))
  | .loop inner => .loop (inner.rename (mapping.child 0 0))
  | .application inner => .application (inner.rename mapping)

/-- Finite γ/θ trees over ordered acyclic graphs. Each structural binding
uses common typed input and output wiring. Only the selected γ arm is
entered, and θ restarts its own body with fresh locals. -/
inductive CodePair (Op : Dialect.{u, v} (ValueSort V S) S) :
    {args outs : Ports (Ty V S)} → {sigsL sigsR : List (Ports (Ty V S))} →
    Renaming → NestedTheta.Term (Instruction Op) args [] sigsL outs →
    NestedTheta.Term (Instruction Op) args [] sigsR outs → Prop where
  | acyclic {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
      (ordered : OrderedGraph map left right) :
    CodePair Op map (embed left.toTerm) (embed right.toTerm)
  | theta {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (position : map.vertices 0 = 0) (ordered : OrderedGraph (map.child 0 0) left right) :
    CodePair Op map (SingleTheta.code initial left outputs) (SingleTheta.code initial right outputs)
  | gamma {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
      (position : map.vertices 0 = 0) (arms : ∀ i, CodePair Op (map.child 0 i.val) (armsL i) (armsR i)) :
    CodePair Op map (code inputs armsL outputs) (code inputs armsR outputs)

  | loop {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (position : map.vertices 0 = 0) (body : CodePair Op (map.child 0 0) left right) :
    CodePair Op map (loopCode initial left outputs) (loopCode initial right outputs)

/-- The existing typed primitive diagnostic and exact pending continuation. -/
structure Block (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (outs : Ports (Ty V S)) where
  site : Site m
  pending : Pending m site.outs outs
  store : σ

def Block.outcome (stop : Block m σ outs) : Continuation.Partial.Outcome m σ outs :=
  .blocked stop.site stop.pending stop.store

/-- Body-local blocking certificates under a selected γ. The θ constructor
keeps completed feedback and the blocked fresh activation. The γ constructor
keeps the actual selector and pushes the original enclosing suffix. -/
inductive BlockPair (primitives : Primitives m σ) (ids : GlobalRel) :
    {args outs : Ports (Ty V S)} → {sigsL sigsR : List (Ports (Ty V S))} →
    (map : Renaming) →
    NestedTheta.Term (Instruction Op) args [] sigsL outs →
    NestedTheta.Term (Instruction Op) args [] sigsR outs →
    Tuple m.Val args → Tuple m.Val args → σ →
    Location → Location → Block m σ outs → Block m σ outs → Prop where
  | acyclic {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Term Op args [] sigsL outs} {right : Term Op args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {start store : σ}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs outs} {pendingR : Pending m siteR.outs outs}
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left inputL PUnit.unit start location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right inputR PUnit.unit start (map.location location) (.blocked siteR pendingR store)) :
    BlockPair primitives ids map (embed left) (embed right) inputL inputR start
      (.acyclic location) (.acyclic (map.location location)) ⟨siteL, pendingL, store⟩ ⟨siteR, pendingR, store⟩
  | theta {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {start store : σ}
      {first current : SingleTheta.Carries m ids σ carried}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs (Theta.BodyResults carried)}
      {pendingR : Pending m siteR.outs (Theta.BodyResults carried)}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (startsL : first.left = initial.read entryL PUnit.unit) (startsR : first.right = initial.read entryR PUnit.unit)
      (startsStore : first.store = start)
      (completed : ReflTransGen (SingleTheta.FeedbackPair primitives left right) first current)
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left.toTerm current.left PUnit.unit current.store
        location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right.toTerm current.right PUnit.unit current.store
        ((map.child 0 0).location location) (.blocked siteR pendingR store)) :
    BlockPair primitives ids map (SingleTheta.code initial left outputs) (SingleTheta.code initial right outputs)
      entryL entryR start (.theta location) (.theta ((map.child 0 0).location location))
      ⟨siteL, .bind (past := []) (.ret outputs) entryL PUnit.unit (.loop (embed left.toTerm) pendingL), store⟩
      ⟨siteR, .bind (past := []) (.ret outputs) entryR PUnit.unit (.loop (embed right.toTerm) pendingR), store⟩
  | gamma {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      {entryL entryR : Tuple m.Val args} {inputL inputR : Tuple m.Val entry} {store : σ}
      {tag : Fin (extra + 2)} {locL locR : Location} {stopL stopR : Block m σ returned}
      (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
      (selectL : inputs.read entryL PUnit.unit = .cons (.control tag) inputL)
      (selectR : inputs.read entryR PUnit.unit = .cons (.control tag) inputR)
      (selected : BlockPair primitives ids (map.child 0 tag.val) (armsL tag) (armsR tag)
        inputL inputR store locL locR stopL stopR) :
    BlockPair primitives ids map (code inputs armsL outputs) (code inputs armsR outputs) entryL entryR store
      (.gamma tag.val locL) (.gamma tag.val locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit stopR.pending, stopR.store⟩

  | loop {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {store : σ} {first current : Carries m ids σ carried}
      {locL locR : Location} {stopL stopR : Block m σ (Theta.BodyResults carried)}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (startsL : first.left = initial.read entryL PUnit.unit) (startsR : first.right = initial.read entryR PUnit.unit)
      (startsStore : first.store = store)
      (completed : ReflTransGen (IterationPair primitives left right) first current)
      (stopped : BlockPair primitives ids (map.child 0 0) left right current.left current.right
        current.store locL locR stopL stopR) :
    BlockPair primitives ids map (loopCode initial left outputs) (loopCode initial right outputs)
      entryL entryR store (.loop locL) (.loop locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit (.loop left stopL.pending), stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit (.loop right stopR.pending), stopR.store⟩

  | application {args outs captured : Ports (Ty V S)} {fn : Function V S} {map : Renaming}
      {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {captL captR : Tuple m.Val captured} {entryL entryR : Tuple m.Val args}
      {argsL argsR : Tuple m.Val fn.args} {store : σ}
      {locL locR : Location} {stopL stopR : Block m σ fn.results}
      (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
      (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
      (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR)
      (stopped : BlockPair primitives ids map left right (prependContext argsL captL) (prependContext argsR captR)
        store locL locR stopL stopR) :
    BlockPair primitives ids map (applicationCode fn inputs outputs) (applicationCode fn inputs outputs)
      entryL entryR store (.application locL) (.application locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit stopR.pending, stopR.store⟩

variable {primitives : Primitives m σ} {mapping : Renaming}

/-- A common productive feedback stream and finite syntax-directed routes
to its first checkpoints. Both routes retain all pending typed frames. -/
inductive ProductivePair (primitives : Primitives m σ) (ids : GlobalRel)
    {outs : Ports (Ty V S)} (jobL jobR : Job m outs) (store : σ) : Prop where
  | reached {carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      {initial : SingleTheta.Carries m ids σ carried}
      {pendingL pendingR : Pending m carried outs}
      (paired : InfiniteTrace (SingleTheta.FeedbackPair primitives left right) initial)
      (ranL : Feedback.Reaches primitives jobL store ⟨carried, sigsL, embed left.toTerm, (initial.left, initial.store)⟩ pendingL)
      (ranR : Feedback.Reaches primitives jobR store ⟨carried, sigsR, embed right.toTerm, (initial.right, initial.store)⟩ pendingR)

  | feedback {carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      {initial : Carries m ids σ carried}
      {pendingL pendingR : Pending m carried outs}
      (paired : InfiniteTrace (IterationPair primitives left right) initial)
      (ranL : Feedback.Reaches primitives jobL store ⟨carried, sigsL, left, (initial.left, initial.store)⟩ pendingL)
      (ranR : Feedback.Reaches primitives jobR store ⟨carried, sigsR, right, (initial.right, initial.store)⟩ pendingR)

inductive RegionPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (left : NestedTheta.Term (Instruction Op) args [] sigsL outs)
    (right : NestedTheta.Term (Instruction Op) args [] sigsR outs)
    (inputL inputR : Tuple m.Val args) (store : σ) : Prop where
  | returned {leftValue rightValue : Tuple m.Val outs} {finalStore : σ}
      (values : TupleRelated m ids leftValue rightValue)
      (ranL : Eval primitives (.region left inputL PUnit.unit) store (.returned leftValue finalStore))
      (ranR : Eval primitives (.region right inputR PUnit.unit) store (.returned rightValue finalStore))
  | blocked {locL locR : Location} {stopL stopR : Block m σ outs}
      (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR)
  | productive (run : ProductivePair primitives ids (.region left inputL PUnit.unit) (.region right inputR PUnit.unit) store)

/-- An activation that does not select outer feedback. An inner run is
witnessed by the selected arm's productive feedback certificate. -/
inductive Activation (primitives : Primitives m σ) (mapping : Renaming)
    (left : LoopBody Op carried sigsL) (right : LoopBody Op carried sigsR)
    (input : Carries m ids σ carried) : Prop where
  | exited {tag : m.Val (.control 2)} {outL outR : Tuple m.Val carried} {store : σ}
      (exits : (tag.selector.val == 1) = false)
      (values : TupleRelated m ids outL outR)
      (ranL : Eval primitives (.region left input.left PUnit.unit) input.store (.returned (.cons tag outL) store))
      (ranR : Eval primitives (.region right input.right PUnit.unit) input.store (.returned (.cons tag outR) store))
  | blocked {locL locR : Location} {stopL stopR : Block m σ (Theta.BodyResults carried)}
      (stopped : BlockPair primitives ids mapping left right input.left input.right input.store locL locR stopL stopR)
  | inner (live : ProductivePair primitives ids (.region left input.left PUnit.unit)
      (.region right input.right PUnit.unit) input.store)

/-- The observed loop either reaches an exit, block or productive inner
activation after completed outer restarts, or keeps completing outer
activations forever. The prefix and stream use the same carried relation. -/
inductive LoopPair (primitives : Primitives m σ) (mapping : Renaming)
    (left : LoopBody Op carried sigsL) (right : LoopBody Op carried sigsR)
    (input : Carries m ids σ carried) : Prop where
  | activation {current : Carries m ids σ carried}
      (completed : ReflTransGen (IterationPair primitives left right) input current)
      (observed : Activation primitives mapping left right current)
  | outer (live : InfiniteTrace (IterationPair primitives left right) input)

inductive ScheduledLambda (m : Machine.{u, v, w} Op) (ids : GlobalRel) (mapping : Renaming)
    (params outs : Ports (Ty V S)) :
    m.Val (.value (.function params outs)) → m.Val (.value (.function params outs)) → Prop where
  | closure {captured : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {captL captR : Tuple m.Val captured}
      {left : NestedTheta.Term (Instruction Op) (captured ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (captured ++ params) [] sigsR outs}
      (captures : TupleRelated m ids captL captR) (code : CodePair Op mapping left right) :
    ScheduledLambda m ids mapping params outs (.closure captL left.toGraph) (.closure captR right.toGraph)

  /-- The caller's first capture is the actual paired λ. Its code is
  admitted by call-free `CodePair`. No runtime lookup or target choice
  is used in the witness. Other captures and arguments may feed the call
  and the wiring suffix. -/
  | application {context captured : Ports (Ty V S)} {fn : Function V S}
      {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {calleeL calleeR : Tuple m.Val captured} {capturesL capturesR : Tuple m.Val context}
      (calleeCaptures : TupleRelated m ids calleeL calleeR)
      (calleeIso : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph)
      (calleeCode : CodePair Op mapping left right)
      (captures : TupleRelated m ids capturesL capturesR)
      (arguments : Wires (fn.port :: (context ++ params)) [] fn.args)
      (outputs : Wires (fn.port :: (context ++ params)) [fn.results] outs) :
    ScheduledLambda m ids mapping params outs
      (.closure (.cons (.closure calleeL left.toGraph) capturesL)
        (applicationCode fn (.cons (.arg .head) arguments) outputs).toGraph)
      (.closure (.cons (.closure calleeR right.toGraph) capturesR)
        (applicationCode fn (.cons (.arg .head) arguments) outputs).toGraph)

/-- Finite observations and productive feedback at the two call entries.
The original entries are the actual selected closures and post-link store. -/
inductive CallPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (outs : Ports (Ty V S)) : Config m σ outs → Config m σ outs → Prop where
  | returned {sourceL sourceR : Config m σ outs} {valueL valueR : Tuple m.Val outs} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL (.returned valueL store))
      (ranR : SingleTheta.TerminalOutcome primitives sourceR (.returned valueR store)) :
    CallPair primitives ids mapping outs sourceL sourceR
  | blocked {sourceL sourceR : Config m σ outs}
      {args : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {store : σ} {locL locR : Location} {stopL stopR : Block m σ outs}
      (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL stopL.outcome)
      (ranR : SingleTheta.TerminalOutcome primitives sourceR stopR.outcome) :
    CallPair primitives ids mapping outs sourceL sourceR
  | productive {jobL jobR : Job m outs} {store : σ}
      (run : ProductivePair primitives ids jobL jobR store) :
    CallPair primitives ids mapping outs ⟨Continuation.start jobL, store⟩ ⟨Continuation.start jobR, store⟩

inductive DispatchPair (primitives : Primitives m σ) (ids : GlobalRel) (unitRename : Nat → Nat)
    (mapping : Renaming) (outs : Ports (Ty V S)) :
    Except (Failure m σ) (Config m σ outs) → Except (Failure m σ) (Config m σ outs) → Prop where
  | linkBlocked {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (address : unitRename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (sites : SitesRelated m ids siteL siteR) (store : σ) :
    DispatchPair primitives ids unitRename mapping outs
      (.error ⟨unitL, vertexL, siteL, store⟩) (.error ⟨unitR, vertexR, siteR, store⟩)
  | invoked {sourceL sourceR : Config m σ outs} (calls : CallPair primitives ids mapping outs sourceL sourceR) :
    DispatchPair primitives ids unitRename mapping outs (.ok sourceL) (.ok sourceR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma
