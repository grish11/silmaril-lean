module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Defs

/-! # A conditional child activation with ordered completion -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Conditional

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer child before : List (Ty Data)} {t : Ty Data}

/-- The condition sees the old outer store. The true arm uses the ordinary
child and commit, while the false arm executes a loop-free update. -/
structure Form (P : InstructionSet.{u,v} Data) (outer child : List (Ty Data)) (t : Ty Data) where
  parent : Nested.Form P outer child t
  selectChild : Expr P outer .bool
  skip : Body P outer outer

structure Choice (P : InstructionSet.{u,v} Data) (outer before : List (Ty Data)) where
  build : Build (Opcode P) outer before (.bool :: outer)
  decision : Port build.nodes .bool
  childPass : Port build.nodes .count
  childToken : Port build.nodes .bool

variable (f : Form P outer child t) (neg : P [.bool] .bool)

def Form.step : Stmt P true outer outer :=
  .branch f.selectChild f.parent.step f.skip.source.enableWhile

def Form.source : Program P true outer t := whileProgram f.parent.guard f.step f.parent.result

def Form.choice (ctx : Tuple (Port before) (.bool :: outer)) : Choice P outer before :=
  let test := (expr f.selectChild).lower (params := outer) (tail ctx)
  let shared := test.code.liftRefs ctx
  let call := f.parent.childRegion neg shared
  let commit := f.parent.commit.lower (params := outer) call.refs
  let yes := f.parent.activation neg shared
  let no := f.skip.lower (yes.code.liftRefs shared)
  let flag := no.code.lift (yes.code.lift (test.refs.get .head))
  let joined := phiNodes flag (no.code.liftRefs yes.refs) no.refs
  ⟨(Build.straight test).thenBuild (yes.thenBuild ((Build.straight no).thenBuild (.straight joined))),
    joined.code.lift flag,
    joined.code.lift (no.code.lift (commit.code.lift (passRef (.bool :: child)))),
    joined.code.lift (no.code.lift (commit.code.lift (portLeft (.head : Port (.bool :: child) .bool))))⟩

def Form.iteration (before : List (Ty Data)) : Choice P outer (loopTest f.parent.guard outer before).nodes :=
  f.choice neg ((loopTest f.parent.guard outer before).code.liftRefs (loopSlots outer before))

def Form.region (init : Tuple (Port before) (.bool :: outer)) :
    Build (Opcode P) outer before (.bool :: outer) :=
  let test := loopTest f.parent.guard outer before
  let step := (f.iteration neg before).build
  ⟨_, .loop init (.seq (.straight test.code) step.code)
    (step.code.lift (test.refs.get .head)) step.refs (.source neg),
    (ports (.bool :: outer)).map fun _ p => portLeft p⟩

def Form.program : Build (Opcode P) outer [] [t, .bool] :=
  let initial := entry P outer
  let run := f.region neg initial.refs
  (Build.straight initial).thenBuild
    ⟨run.nodes, run.code, .cons (run.refs.get (.tail f.parent.result)) (.cons (run.refs.get .head) .nil)⟩

def Form.translate :
    Graph (Opcode P) outer [t, .bool] (f.program neg).nodes.length (f.program neg).nodes.length :=
  let p := f.program neg
  p.code.toGraph p.refs

def Form.outerPass : Ref (f.translate neg).sort .count := numberPort (passRef (.bool :: outer))

def Form.decision : Ref (f.translate neg).sort .bool :=
  numberPort (insideRef (.bool :: outer) (f.iteration neg (entry P outer).nodes).decision)

def Form.childPass : Ref (f.translate neg).sort .count :=
  numberPort (insideRef (.bool :: outer) (f.iteration neg (entry P outer).nodes).childPass)

def Form.childToken : Ref (f.translate neg).sort .bool :=
  numberPort (insideRef (.bool :: outer) (f.iteration neg (entry P outer).nodes).childToken)

/-- The emitted decision is defined at a continuing coordinate. Only a
true decision carries a child first-pass and completion witness. -/
def Form.activation (m : Interpretation.{u,v,w} P) (values : (f.translate neg).Valuation (model m))
    (i : Index (f.program neg).nodes.length) : Prop :=
  let flag := f.decision neg
  let pass := f.childPass neg
  let token := f.childToken neg
  ∃ selected : Bool, flag.read m.carrier (values (flag.id, i)) = some ⟨selected⟩ ∧
    (selected = true → ∃ count : Nat,
      pass.read m.carrier (values (pass.id, i)) = some ⟨count⟩ ∧
      token.read m.carrier (values (token.id, i)) = some ⟨true⟩)

end Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Conditional
