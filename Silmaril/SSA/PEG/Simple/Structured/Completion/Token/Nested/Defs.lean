module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Defs

/-! # A completion-carrying outer loop with one unconditional child -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Nested

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer child before : List (Ty Data)} {t : Ty Data}

/-- Each outer step projects a fresh child entry from its current store,
runs the whole child, and commits a loop-free update from the child's
exit store. The capture tuple may duplicate or preserve outer slots. -/
structure Form (P : InstructionSet.{u,v} Data) (outer child : List (Ty Data)) (t : Ty Data) where
  guard : Expr P outer .bool
  capture : Tuple (Port outer) child
  childGuard : Expr P child .bool
  childBody : Body P child child
  commit : Body P child outer
  result : Port outer t

variable (f : Form P outer child t) (neg : P [.bool] .bool)

def Form.step : Stmt P true outer outer :=
  .seq (.project f.capture)
    (.seq (.while rfl f.childGuard f.childBody.source.enableWhile) f.commit.source.enableWhile)

def Form.source : Program P true outer t := whileProgram f.guard f.step f.result

def captureRefs (capture : Tuple (Port outer) child) (ctx : Tuple (Port before) (.bool :: outer)) :
    Tuple (Port before) (.bool :: child) :=
  .cons (ctx.get .head) (select (tail ctx) capture)

def Form.childRegion (ctx : Tuple (Port before) (.bool :: outer)) :
    Build (Opcode P) outer before (.bool :: child) :=
  loop f.childGuard f.childBody neg (captureRefs f.capture ctx)

def Form.activation (ctx : Tuple (Port before) (.bool :: outer)) :
    Build (Opcode P) outer before (.bool :: outer) :=
  let inner := f.childRegion neg ctx
  inner.thenBuild (.straight (f.commit.lower inner.refs))

def Form.region (init : Tuple (Port before) (.bool :: outer)) :
    Build (Opcode P) outer before (.bool :: outer) :=
  let test := loopTest f.guard outer before
  let step := f.activation neg (test.code.liftRefs (loopSlots outer before))
  ⟨_, .loop init (.seq (.straight test.code) step.code)
    (step.code.lift (test.refs.get .head)) step.refs (.source neg),
    (ports (.bool :: outer)).map fun _ p => portLeft p⟩

def Form.program : Build (Opcode P) outer [] [t, .bool] :=
  let initial := entry P outer
  let run := f.region neg initial.refs
  (Build.straight initial).thenBuild
    ⟨run.nodes, run.code, .cons (run.refs.get (.tail f.result)) (.cons (run.refs.get .head) .nil)⟩

def Form.translate :
    Graph (Opcode P) outer [t, .bool] (f.program neg).nodes.length (f.program neg).nodes.length :=
  let p := f.program neg
  p.code.toGraph p.refs

def Form.outerPass : Ref (f.translate neg).sort .count :=
  numberPort (passRef (.bool :: outer))

def Form.childPass : Ref (f.translate neg).sort .count :=
  let before := (entry P outer).nodes
  let test := loopTest f.guard outer before
  let inner := f.childRegion neg (test.code.liftRefs (loopSlots outer before))
  let post := f.commit.lower (params := outer) inner.refs
  numberPort (insideRef (.bool :: outer) (post.code.lift (passRef (.bool :: child))))

def Form.childToken : Ref (f.translate neg).sort .bool :=
  let before := (entry P outer).nodes
  let test := loopTest f.guard outer before
  let inner := f.childRegion neg (test.code.liftRefs (loopSlots outer before))
  let post := f.commit.lower (params := outer) inner.refs
  numberPort (insideRef (.bool :: outer) (post.code.lift (portLeft (.head : Port (.bool :: child) .bool))))

/-- The actual Figure 11 child pass and marker at the specified outer
activation. The pass samples at its own coordinate, retaining the outer one. -/
def Form.childExit (m : Interpretation.{u,v,w} P) (values : (f.translate neg).Valuation (model m))
    (i : Index (f.program neg).nodes.length) (count : Nat) : Prop :=
  let pass := f.childPass neg
  let token := f.childToken neg
  pass.read m.carrier (values (pass.id, i)) = some ⟨count⟩ ∧
    token.read m.carrier (values (token.id, i)) = some ⟨true⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Nested
