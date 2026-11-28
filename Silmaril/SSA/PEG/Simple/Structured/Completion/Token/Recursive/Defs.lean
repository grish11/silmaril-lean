module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Defs

/-! # Recursive completion lowering for typed SIMPLE -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Recursive

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars outs before : List (Ty Data)} {t : Ty Data}

/-- Merge the completion port and every data port under the same decision.
The second arm may refer to the old context lifted through the first arm. -/
def joinBranch (test : Simple.Build (Opcode P) params before [.bool])
    (yes : Build (Opcode P) params test.nodes (.bool :: outs))
    (no : Build (Opcode P) params yes.nodes (.bool :: outs)) :
    Build (Opcode P) params before (.bool :: outs) :=
  let flag := no.code.lift (yes.code.lift (test.refs.get .head))
  let joined := phiNodes flag (no.code.liftRefs yes.refs) no.refs
  (Build.straight test).thenBuild (yes.thenBuild (no.thenBuild (.straight joined)))

/-- All loop outputs, including completion, share the existing pass. -/
def closeLoop (neg : P [.bool] .bool) (ctx : Tuple (Port before) (.bool :: vars))
    (test : Simple.Build (Opcode P) params ((.bool :: vars) ++ before) [.bool])
    (body : Build (Opcode P) params test.nodes (.bool :: vars)) :
    Build (Opcode P) params before (.bool :: vars) :=
  ⟨_, .loop ctx (.seq (.straight test.code) body.code)
    (body.code.lift (test.refs.get .head)) body.refs (.source neg),
    (ports (.bool :: vars)).map fun _ p => portLeft p⟩

/-- The result of a statement contains its completion marker followed by
its typed output store. Statement sequencing passes that tuple forward. -/
def compile (neg : P [.bool] .bool) :
    {vars outs : List (Ty Data)} → Stmt P true vars outs →
    {before : List (Ty Data)} → Tuple (Port before) (.bool :: vars) →
    Build (Opcode P) params before (.bool :: outs)
  | _, _, .assign rhs, _, ctx => .straight ((Body.assign rhs).lower ctx)
  | _, _, .project ps, _, ctx => .straight ((Body.project ps).lower ctx)
  | _, _, .seq first second, _, ctx =>
    let a := compile neg first ctx
    a.thenBuild (compile neg second a.refs)
  | _, _, .branch guard yes no, _, ctx =>
    let test := (expr guard).lower (params := params) (tail ctx)
    let shared := test.code.liftRefs ctx
    let y := compile neg yes shared
    let n := compile neg no (y.code.liftRefs shared)
    joinBranch test y n
  | vars, _, .while _ guard body, before, ctx =>
    let test := loopTest guard params before
    closeLoop neg ctx test (compile neg body (test.code.liftRefs (loopSlots vars before)))

def program (p : Program P true params t) (neg : P [.bool] .bool) : Build (Opcode P) params [] [t, .bool] :=
  let initial := entry P params
  let body := compile neg p.body initial.refs
  (Build.straight initial).thenBuild
    ⟨body.nodes, body.code, .cons (body.refs.get (.tail p.retvar)) (.cons (body.refs.get .head) .nil)⟩

def translate (p : Program P true params t) (neg : P [.bool] .bool) :
    Graph (Opcode P) params [t, .bool] (program p neg).nodes.length (program p neg).nodes.length :=
  let compiled := program p neg
  compiled.code.toGraph compiled.refs

end Silmaril.SSA.PEG.Simple.Structured.Token.Recursive
