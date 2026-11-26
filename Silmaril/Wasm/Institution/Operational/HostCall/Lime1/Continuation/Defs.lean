module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs

/-! # Checked Lime1 continuations

Each conditional checks both arms against its resolved signature. An entered
arm starts with the declared parameters and retains the enclosing operand
prefix and continuation until the label exits.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation

open Execution.Runtime (EvalCtx Frame ModuleInst Result Value)
open Wasm.Lime1.Execution

inductive IfType where
  | scalar (type : NumType)
  | indexed (index : TypeIdx) (signature : Wasm.Lime1.FuncType)

def IfType.blockType : IfType → Wasm.Lime1.BlockType
  | .scalar type => .value type
  | .indexed index _ => .typeIdx index

def IfType.signature : IfType → Wasm.Lime1.FuncType
  | .scalar type => ⟨[], [type]⟩
  | .indexed _ signature => signature

def IfType.Resolved (type : IfType) (module : ModuleInst) : Prop :=
  blockType? module.types type.blockType = some type.signature

inductive Op (H : Type) where
  | get (index : LocalIdx)
  | drop
  | call (index : FuncIdx) (site : Site H)
  | br (depth : LabelIdx)
  | brIf (depth : LabelIdx)
  | if_ (type : IfType) (thenArm elseArm : List (Op H))

mutual
def Op.instr {H : Type} : Op H → Wasm.Lime1.Instr
  | .get index => .localGet index
  | .drop => .drop
  | .call index _ => .call index
  | .br depth => .br depth
  | .brIf depth => .brIf depth
  | .if_ type left right => .if_ type.blockType (expr left) (expr right)

def expr {H : Type} : List (Op H) → Wasm.Lime1.Expr
  | [] => []
  | op :: rest => op.instr :: expr rest
end

def code {H : Type} (ops : List (Op H)) : List Admin := expression (expr ops)

/-- Static checks use the entered module, base allocation and active local types.
The first index lists label results from the innermost label to the function label.
The next indices give the delivered result types and the initial stack types.
Each operand stack is ordered bottom to top. -/
inductive Checked {H : Type} (base : Store H) (module : ModuleInst)
    (locals : List NumType) : List (List NumType) → List NumType → List NumType → List (Op H) → Prop where
  | nil {targets results} : Checked base module locals targets results results []
  | get {targets results stack index type ops} (localType : locals[index.toNat]? = some type)
      (tail : Checked base module locals targets results (stack ++ [type]) ops) :
      Checked base module locals targets results stack (.get index :: ops)
  | drop {targets results stack type ops} (tail : Checked base module locals targets results stack ops) :
      Checked base module locals targets results (stack ++ [type]) (.drop :: ops)
  | call {targets} {results saved : List NumType} {index : FuncIdx} {site : Site H} {ops : List (Op H)}
      (resolved : module.funcs[index.toNat]? = some site.address) (allocated : site.Allocated base)
      (tail : Checked base module locals targets results (saved ++ site.type.results) ops) :
      Checked base module locals targets results (saved ++ site.type.params) (.call index site :: ops)
  /-- An unconditional transfer skips the suffix in its current label. -/
  | br {targets} {depth : LabelIdx} {results scratch payload : List NumType} {ops : List (Op H)}
      (target : targets[depth.toNat]? = some payload) :
      Checked base module locals targets results (scratch ++ payload) (.br depth :: ops)
  | brIf {targets} {depth : LabelIdx} {results scratch payload : List NumType} {ops : List (Op H)}
      (target : targets[depth.toNat]? = some payload)
      (tail : Checked base module locals targets results (scratch ++ payload) ops) :
      Checked base module locals targets results ((scratch ++ payload) ++ [.int .i32]) (.brIf depth :: ops)
  | if_ {targets} {results saved : List NumType} {type : IfType} {left right ops : List (Op H)}
      (resolved : type.Resolved module)
      (thenArm : Checked base module locals (type.signature.results :: targets)
        type.signature.results type.signature.params left)
      (elseArm : Checked base module locals (type.signature.results :: targets)
        type.signature.results type.signature.params right)
      (tail : Checked base module locals targets results (saved ++ type.signature.results) ops) :
      Checked base module locals targets results ((saved ++ type.signature.params) ++ [.int .i32])
        (.if_ type left right :: ops)

inductive Contract {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H) :
    List (Op H) → Prop where
  | nil : Contract mem host []
  | get {index ops} (tail : Contract mem host ops) : Contract mem host (.get index :: ops)
  | drop {ops} (tail : Contract mem host ops) : Contract mem host (.drop :: ops)
  | call {index site ops} (siteContract : site.Contract mem host) (tail : Contract mem host ops) :
      Contract mem host (.call index site :: ops)
  | br {depth ops} : Contract mem host (.br depth :: ops)
  | brIf {depth ops} (tail : Contract mem host ops) : Contract mem host (.brIf depth :: ops)
  | if_ {type left right ops} (thenArm : Contract mem host left) (elseArm : Contract mem host right)
      (tail : Contract mem host ops) : Contract mem host (.if_ type left right :: ops)

/-- An open conditional arm retains the enclosing operand prefix and code. -/
structure Label (H : Type) where
  type : IfType
  saved : List Value
  tail : List (Op H)

inductive Phase (H : Type) where
  | source (stack : List Value) (ops : List (Op H))
  | block (label : Label H) (args : List Value) (arm : List (Op H))
  | invoke (saved : List Value) (site : Site H) (args : List Value) (ops : List (Op H))
  | trapped (saved : List Value) (rest : List Admin)
  | frameResult (result : Result)
  | done (result : Result)

/-- Source and lowered branches share the same native instruction and suffix. -/
abbrev Phase.branch {H : Type} (stack : List Value) (depth : LabelIdx) (ops : List (Op H)) : Phase H :=
  .source stack (.br depth :: ops)

structure State (H : Type) where
  bytes : ByteArray
  phase : Phase H
  labels : List (Label H)

def ResultTyped (types : List NumType) : Result → Prop
  | .values vs => vs.map Value.type = types
  | .trap => True

def labelResults {H : Type} (results : List NumType) : List (Label H) → List NumType
  | [] => results
  | label :: _ => label.type.signature.results

def targetTypes {H : Type} (results : List NumType) : List (Label H) → List (List NumType)
  | [] => [results]
  | label :: rest => label.type.signature.results :: targetTypes results rest

inductive LabelsReady {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) : List (Label H) → Prop where
  | nil : LabelsReady mem host active results []
  | cons {label : Label H} {rest : List (Label H)}
      (tail : Checked base active.module (active.locals.map Value.type)
        (targetTypes results rest) (labelResults results rest)
        (label.saved.map Value.type ++ label.type.signature.results) label.tail)
      (contract : Contract mem host label.tail)
      (outer : LabelsReady mem host active results rest) :
      LabelsReady mem host active results (label :: rest)

def Ready {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) (phase : Phase H) (labels : List (Label H)) : Prop :=
  LabelsReady mem host active results labels ∧
  let targets := targetTypes results labels
  let delivered := labelResults results labels
  match phase with
  | .source stack ops => Checked base active.module (active.locals.map Value.type) targets delivered
      (stack.map Value.type) ops ∧ Contract mem host ops
  | .block label args arm => label.type.Resolved active.module ∧
      args.map Value.type = label.type.signature.params ∧
      Checked base active.module (active.locals.map Value.type)
        (label.type.signature.results :: targets) label.type.signature.results (args.map Value.type) arm ∧ Contract mem host arm ∧
      Checked base active.module (active.locals.map Value.type) targets delivered
        (label.saved.map Value.type ++ label.type.signature.results) label.tail ∧ Contract mem host label.tail
  | .invoke saved site args ops => site.Allocated base ∧ site.Arguments args ∧ site.Contract mem host ∧
      Checked base active.module (active.locals.map Value.type) targets delivered
        (saved.map Value.type ++ site.type.results) ops ∧ Contract mem host ops
  | .trapped _ _ => True
  | .frameResult out | .done out => labels = [] ∧ ResultTyped results out

/-- Native layers outside the active label, from the innermost context to
the enclosing function frame. -/
inductive Scope where
  | function (arity : Nat)
  | label (arity : Nat) (saved : List Value) (tail : List Admin) (outer : Scope)

def scopeFor {H : Type} (results : List NumType) : List (Label H) → Scope
  | [] => .function results.length
  | label :: rest => .label (labelResults results rest).length label.saved (code label.tail) (scopeFor results rest)

def frameContext (active : Frame) : Scope → EvalCtx Wasm.Lime1.Instr
  | .function arity => .frame arity active .hole
  | .label arity saved tail outer =>
      (frameContext active outer).comp (.label arity [] (.seq saved .hole tail))

def framed (active : Frame) (body : List Admin) : Scope → List Admin
  | .function arity => [.frame arity active body]
  | .label arity saved tail outer => framed active [.label arity [] (values saved ++ body ++ tail)] outer

def entered (arity : Nat) (active : Frame) (body : List Admin) : List Admin :=
  [.frame arity active [.label arity [] body]]

def invokeContext {H : Type} (scope : Scope) (arity : Nat) (active : Frame)
    (saved : List Value) (ops : List (Op H)) : EvalCtx Wasm.Lime1.Instr :=
  (frameContext active scope).comp (.label arity [] (.seq saved .hole (code ops)))

def Phase.renderIn {H : Type} (scope : Scope) (arity : Nat) (active : Frame) : Phase H → List Admin
  | .source stack ops => framed active [.label arity [] (values stack ++ code ops)] scope
  | .block label args arm => framed active [.label arity [] (values (label.saved ++ args) ++
      .source (.block label.type.blockType (expr arm)) :: code label.tail)] scope
  | .invoke saved site args ops => (invokeContext scope arity active saved ops).plug value
      (values args ++ [.invoke site.address])
  | .trapped saved rest => framed active [.label arity [] (values saved ++ .trap :: rest)] scope
  | .frameResult out => framed active (result out) scope
  | .done out => result out

def Phase.renderCode {H : Type} (results : List NumType) (active : Frame)
    (phase : Phase H) (labels : List (Label H)) : List Admin :=
  phase.renderIn (scopeFor results labels) (labelResults results labels).length active

def render {H : Type} {base : Store H} (mem : Memory32 base) (outer active : Frame)
    (results : List NumType) (state : State H) : Config H :=
  ⟨mem.store state.bytes, outer, state.phase.renderCode results active state.labels⟩

/-- Select the native arm using the actual i32 operand. -/
def select {H : Type} (guard : BitVec 32) (left right : List (Op H)) : List (Op H) :=
  if guard = 0 then right else left

/-- Each edge corresponds to one native step. Leaving an explicit label
restores the enclosing sequence directly, with no additional graph step. -/
inductive Edge {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) : State H → State H → Prop where
  | get {bytes stack index v ops labels} (found : active.locals[index.toNat]? = some v) :
      Edge mem host active results ⟨bytes, .source stack (.get index :: ops), labels⟩
        ⟨bytes, .source (stack ++ [v]) ops, labels⟩
  | drop {bytes stack v ops labels} : Edge mem host active results ⟨bytes, .source (stack ++ [v]) (.drop :: ops), labels⟩
      ⟨bytes, .source stack ops, labels⟩
  | brIf {bytes stack guard depth ops labels} :
      Edge mem host active results ⟨bytes, .source (stack ++ [Value.int .i32 guard]) (.brIf depth :: ops), labels⟩
        ⟨bytes, if guard = 0 then .source stack ops else .branch stack depth ops, labels⟩
  | branchLower {bytes stack depth ops label labels} (positive : 0 < depth.toNat) :
      Edge mem host active results ⟨bytes, .branch stack depth ops, label :: labels⟩
        ⟨bytes, .branch (label.saved ++ stack) (lowerLabel depth) label.tail, labels⟩
  | branchDeliver {bytes scratch payload depth ops label labels} (zero : depth.toNat = 0)
      (typed : payload.map Value.type = label.type.signature.results) :
      Edge mem host active results ⟨bytes, .branch (scratch ++ payload) depth ops, label :: labels⟩
        ⟨bytes, .source (label.saved ++ payload) label.tail, labels⟩
  | functionBranch {bytes scratch payload depth ops} (zero : depth.toNat = 0)
      (typed : payload.map Value.type = results) :
      Edge mem host active results ⟨bytes, .branch (scratch ++ payload) depth ops, []⟩
        ⟨bytes, .frameResult (.values payload), []⟩
  | if_ {bytes saved args guard type left right ops labels} (typed : args.map Value.type = type.signature.params) :
      Edge mem host active results ⟨bytes, .source ((saved ++ args) ++ [Value.int .i32 guard]) (.if_ type left right :: ops), labels⟩
        ⟨bytes, .block ⟨type, saved, ops⟩ args (select guard left right), labels⟩
  | block {bytes label args arm labels} :
      Edge mem host active results ⟨bytes, .block label args arm, labels⟩ ⟨bytes, .source args arm, label :: labels⟩
  | resolve {bytes saved args index site ops labels} (typed : site.Arguments args) :
      Edge mem host active results ⟨bytes, .source (saved ++ args) (.call index site :: ops), labels⟩
        ⟨bytes, .invoke saved site args ops, labels⟩
  | returned {bytes next saved site args ops vs labels} (live : mem.Live next)
      (typed : site.TypedResult (.values vs))
      (answer : host site.code (mem.store bytes) args (.returned (mem.store next) (.values vs))) :
      Edge mem host active results ⟨bytes, .invoke saved site args ops, labels⟩ ⟨next, .source (saved ++ vs) ops, labels⟩
  | trapped {bytes next saved site args ops labels} (live : mem.Live next)
      (answer : host site.code (mem.store bytes) args (.returned (mem.store next) .trap)) :
      Edge mem host active results ⟨bytes, .invoke saved site args ops, labels⟩ ⟨next, .trapped saved (code ops), labels⟩
  | diverged {bytes saved site args ops labels} (answer : host site.code (mem.store bytes) args .diverged) :
      Edge mem host active results ⟨bytes, .invoke saved site args ops, labels⟩ ⟨bytes, .invoke saved site args ops, labels⟩
  | erase {bytes stack kept removed before cut rest labels}
      (split : stack = kept ++ removed) (suffix : before = cut ++ rest) (activeTrap : removed ≠ [] ∨ cut ≠ []) :
      Edge mem host active results ⟨bytes, .trapped stack before, labels⟩ ⟨bytes, .trapped kept rest, labels⟩
  | armResult {bytes stack label labels} :
      Edge mem host active results ⟨bytes, .source stack [], label :: labels⟩
        ⟨bytes, .source (label.saved ++ stack) label.tail, labels⟩
  | armTrap {bytes label labels} :
      Edge mem host active results ⟨bytes, .trapped [] [], label :: labels⟩
        ⟨bytes, .trapped label.saved (code label.tail), labels⟩
  | labelTrap {bytes} : Edge mem host active results ⟨bytes, .trapped [] [], []⟩ ⟨bytes, .frameResult .trap, []⟩
  | labelResult {bytes stack} : Edge mem host active results ⟨bytes, .source stack [], []⟩
      ⟨bytes, .frameResult (.values stack), []⟩
  | frameDone {bytes out} : Edge mem host active results ⟨bytes, .frameResult out, []⟩ ⟨bytes, .done out, []⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation
