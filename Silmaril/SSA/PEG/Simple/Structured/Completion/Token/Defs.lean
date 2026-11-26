module

public import Silmaril.SSA.PEG.Simple.Structured.Defs

/-! # A completion-carrying structured while -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {vars outs params before ins : List (Ty Data)} {t : Ty Data}

inductive Opcode (P : InstructionSet.{u,v} Data) : InstructionSet.{u,max u v} Data
  | source {ins : List (Ty Data)} {t : Ty Data} : P ins t → Opcode P ins t
  | start : Opcode P [] .bool
  | after (t : Ty Data) : Opcode P [.bool, t] .bool

/-- The token carries only completion. Figure 11's strict primitive
operands require both the previous token and the assignment result. -/
def model (m : Interpretation.{u,v,w} P) : Interpretation.{u,max u v,w} (Opcode P) where
  carrier := m.carrier
  run
    | .source op, args => m.run op args
    | .start, .nil => some ⟨true⟩
    | .after _, .cons token (.cons _ .nil) => some token

mutual

def expr : {t : Ty Data} → Expr P vars t → Expr (Opcode P) vars t
  | _, .var p => .var p
  | _, .op op args => .op (.source op) (arguments args)

def arguments : {ins : List (Ty Data)} → Args P vars ins → Args (Opcode P) vars ins
  | _, .nil => .nil
  | _, .cons first rest => .cons (expr first) (arguments rest)

end

/-- A loop-free body. Conditionals join data and completion using the
same guard and the same choice of arm. -/
inductive Body (P : InstructionSet.{u,v} Data) : List (Ty Data) → List (Ty Data) → Type (max u v)
  | assign {vars : List (Ty Data)} {t : Ty Data} (rhs : Expr P vars t) : Body P vars (t :: vars)
  | project {vars outs : List (Ty Data)} (slots : Tuple (Port vars) outs) : Body P vars outs
  | seq {vars mid outs : List (Ty Data)} (first : Body P vars mid) (second : Body P mid outs) :
    Body P vars outs
  | branch {vars outs : List (Ty Data)} (guard : Expr P vars .bool)
      (yes no : Body P vars outs) : Body P vars outs

def Body.ofStmt : {vars outs : List (Ty Data)} → Stmt P false vars outs → Body P vars outs
  | _, _, .assign rhs => .assign rhs
  | _, _, .project slots => .project slots
  | _, _, .seq first second => .seq (ofStmt first) (ofStmt second)
  | _, _, .branch guard yes no => .branch guard (ofStmt yes) (ofStmt no)
  | _, _, .while impossible _ _ => nomatch impossible

def Body.source : {vars outs : List (Ty Data)} → Body P vars outs → Stmt P false vars outs
  | _, _, .assign rhs => .assign rhs
  | _, _, .project slots => .project slots
  | _, _, .seq first second => .seq first.source second.source
  | _, _, .branch guard yes no => .branch guard yes.source no.source

def tail {F : Ty Data → Type w} : Tuple F (.bool :: vars) → Tuple F vars
  | .cons _ rest => rest

def Body.lower : {vars outs : List (Ty Data)} → Body P vars outs →
    {before : List (Ty Data)} → Tuple (Port before) (.bool :: vars) →
    Simple.Build (Opcode P) params before (.bool :: outs)
  | _, _, .assign (t := t) rhs, _, ctx =>
    let value := (expr rhs).lower (tail ctx)
    let token := value.code.lift (ctx.get .head)
    ⟨_, .emit value.code (.op (.after t)) (.cons token value.refs),
      .cons .head (.cons (.tail (value.refs.get .head))
        ((value.code.liftRefs (tail ctx)).map fun _ p => .tail p))⟩
  | _, _, .project slots, _, ctx => .keep (.cons (ctx.get .head) (select (tail ctx) slots))
  | _, _, .seq first second, _, ctx =>
    let a := first.lower ctx
    a.thenBuild (second.lower a.refs)
  | _, _, .branch guard yes no, _, ctx =>
    let test := (expr guard).lower (tail ctx)
    let initial := test.code.liftRefs ctx
    let y := yes.lower initial
    let n := no.lower (y.code.liftRefs initial)
    let flag := n.code.lift (y.code.lift (test.refs.get .head))
    let joined := phiNodes flag (n.code.liftRefs y.refs) n.refs
    test.thenBuild (y.thenBuild (n.thenBuild joined))

def entry (P : InstructionSet.{u,v} Data) (vars : List (Ty Data)) :
    Simple.Build (Opcode P) vars [] (.bool :: vars) :=
  let inputs := paramNodes (P := Opcode P) (nodes := []) (ports vars)
  ⟨_, .emit inputs.code (.op .start) .nil, .cons .head (inputs.refs.map fun _ p => .tail p)⟩

def loopSlots (vars before : List (Ty Data)) :
    Tuple (Port ((.bool :: vars) ++ before)) (.bool :: vars) :=
  (ports (.bool :: vars)).map fun _ p => portLeft p

def loop (guard : Expr P vars .bool) (body : Body P vars vars) (neg : P [.bool] .bool)
    (init : Tuple (Port before) (.bool :: vars)) :
    Build (Opcode P) params before (.bool :: vars) :=
  let slots := loopSlots vars before
  let test := (expr guard).lower (params := params) (tail slots)
  let step := body.lower (test.code.liftRefs slots)
  ⟨_, .loop init (.seq (.straight test.code) (.straight step.code))
    (step.code.lift (test.refs.get .head)) step.refs (.source neg),
    (ports (.bool :: vars)).map fun _ p => portLeft p⟩

def program (guard : Expr P vars .bool) (body : Body P vars vars) (ret : Port vars t)
    (neg : P [.bool] .bool) : Build (Opcode P) vars [] [t, .bool] :=
  let initial := entry P vars
  let run := loop guard body neg initial.refs
  (Build.straight initial).thenBuild
    ⟨run.nodes, run.code, .cons (run.refs.get (.tail ret)) (.cons (run.refs.get .head) .nil)⟩

/-- Data first, then completion. Both evals sample at the unchanged guard's
shared pass. The extra carried θ records completion of earlier body steps. -/
def translate (guard : Expr P vars .bool) (body : Body P vars vars) (ret : Port vars t)
    (neg : P [.bool] .bool) :
    Graph (Opcode P) vars [t, .bool] (program guard body ret neg).nodes.length
      (program guard body ret neg).nodes.length :=
  let p := program guard body ret neg
  p.code.toGraph p.refs

def source (guard : Expr P vars .bool) (body : Body P vars vars) (ret : Port vars t) :
    Program P true vars t :=
  whileProgram guard body.source.enableWhile ret

end Silmaril.SSA.PEG.Simple.Structured.Token
