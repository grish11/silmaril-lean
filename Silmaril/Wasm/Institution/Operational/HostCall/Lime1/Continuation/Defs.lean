module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs

/-! # Checked Lime1 continuations

Each conditional checks both arms against its resolved signature. An entered
arm starts with the declared parameters and retains the enclosing operand
prefix and continuation until the label exits. Loops use the same scope
structure and carry their source body for restart.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation

open Execution.Runtime (EvalCtx Frame ModuleInst Result Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked

/-- Scalar or indexed control signature used by conditionals and loops. -/
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
  | callIndirect (site : IndirectSite)
  | br (depth : LabelIdx)
  | brIf (depth : LabelIdx)
  | brTable (depths : List LabelIdx) (fallback : LabelIdx)
  | loop (type : IfType) (body : List (Op H))
  | if_ (type : IfType) (thenArm elseArm : List (Op H))

mutual
def Op.instr {H : Type} : Op H → Wasm.Lime1.Instr
  | .get index => .localGet index
  | .drop => .drop
  | .call index _ => .call index
  | .callIndirect site => .callIndirect site.typeIndex
  | .br depth => .br depth
  | .brIf depth => .brIf depth
  | .brTable depths fallback => .brTable depths fallback
  | .loop type body => .loop type.blockType (expr body)
  | .if_ type left right => .if_ type.blockType (expr left) (expr right)

def expr {H : Type} : List (Op H) → Wasm.Lime1.Expr
  | [] => []
  | op :: rest => op.instr :: expr rest
end

def code {H : Type} (ops : List (Op H)) : List Admin := expression (expr ops)

/-- Static checks use the entered module, base allocation and active local types.
The first index lists branch payload signatures from innermost to outermost.
It uses parameters for loop targets and results for conditional and function
targets.
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
  | callIndirect {targets} {results saved : List NumType} {site : IndirectSite} {ops : List (Op H)}
      (linked : site.Linked base module)
      (tail : Checked base module locals targets results (saved ++ site.signature.results) ops) :
      Checked base module locals targets results ((saved ++ site.signature.params) ++ [.int .i32])
        (.callIndirect site :: ops)
  /-- An unconditional transfer skips the suffix in its current label. -/
  | br {targets} {depth : LabelIdx} {results scratch payload : List NumType} {ops : List (Op H)}
      (target : targets[depth.toNat]? = some payload) :
      Checked base module locals targets results (scratch ++ payload) (.br depth :: ops)
  | brIf {targets} {depth : LabelIdx} {results scratch payload : List NumType} {ops : List (Op H)}
      (target : targets[depth.toNat]? = some payload)
      (tail : Checked base module locals targets results (scratch ++ payload) ops) :
      Checked base module locals targets results ((scratch ++ payload) ++ [.int .i32]) (.brIf depth :: ops)
  /-- Every depth must deliver the same ordered payload, including depths
  the runtime selector does not choose. -/
  | brTable {targets} {depths : List LabelIdx} {fallback : LabelIdx}
      {results scratch payload : List NumType} {ops : List (Op H)}
      (listed : ∀ depth ∈ depths, targets[depth.toNat]? = some payload)
      (defaultTarget : targets[fallback.toNat]? = some payload) :
      Checked base module locals targets results ((scratch ++ payload) ++ [.int .i32])
        (.brTable depths fallback :: ops)
  | loop {targets} {results saved : List NumType} {type : IfType} {body ops : List (Op H)}
      (resolved : type.Resolved module)
      (bodyChecked : Checked base module locals (type.signature.params :: targets)
        type.signature.results type.signature.params body)
      (tail : Checked base module locals targets results (saved ++ type.signature.results) ops) :
      Checked base module locals targets results (saved ++ type.signature.params) (.loop type body :: ops)
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
  | callIndirect {site ops} (siteContract : site.Contract mem host) (tail : Contract mem host ops) :
      Contract mem host (.callIndirect site :: ops)
  | br {depth ops} : Contract mem host (.br depth :: ops)
  | brIf {depth ops} (tail : Contract mem host ops) : Contract mem host (.brIf depth :: ops)
  | brTable {depths fallback ops} : Contract mem host (.brTable depths fallback :: ops)
  | loop {type body ops} (bodyContract : Contract mem host body) (tail : Contract mem host ops) :
      Contract mem host (.loop type body :: ops)
  | if_ {type left right ops} (thenArm : Contract mem host left) (elseArm : Contract mem host right)
      (tail : Contract mem host ops) : Contract mem host (.if_ type left right :: ops)

/-- A label retains the enclosing operands and tail. A loop also retains the
body needed to re-enter with a new parameter suffix. -/
structure Label (H : Type) where
  type : IfType
  saved : List Value
  tail : List (Op H)

  restart : Option (List (Op H))

def Label.branchTypes {H : Type} (label : Label H) : List NumType :=
  match label.restart with
  | none => label.type.signature.results
  | some _ => label.type.signature.params

def Label.continuation {H : Type} (label : Label H) : Wasm.Lime1.Expr :=
  match label.restart with
  | none => []
  | some body => [.loop label.type.blockType (expr body)]

inductive Phase (H : Type) where
  | source (stack : List Value) (ops : List (Op H))
  | block (label : Label H) (args : List Value) (arm : List (Op H))
  | invoke (saved : List Value) (site : Site H) (args : List Value) (ops : List (Op H))
  | wasm (saved : List Value) (site : IndirectSite) (callee : WasmTarget) (phase : Graph.Phase) (ops : List (Op H))
  | memory (saved : List Value) (callee : MemoryTarget) (phase : MemoryCallee.Phase) (ops : List (Op H))
  | trapped (saved : List Value) (rest : List Admin)
  | frameResult (result : Result)
  | done (result : Result)

/-- Source and lowered branches share the same native instruction and suffix. -/
abbrev Phase.branch {H : Type} (stack : List Value) (depth : LabelIdx) (ops : List (Op H)) : Phase H :=
  .source stack (.br depth :: ops)

def Phase.afterLookup {H : Type} (saved args : List Value) (indirect : IndirectSite) (target : Option (IndirectTarget H))
    (ops : List (Op H)) : Phase H :=
  match target with
  | some (.host callee) => .invoke saved callee args ops
  | some (.wasm callee) => .wasm saved indirect callee (.invoke args) ops
  | some (.memory callee) => .memory saved callee (.invoke args) ops
  | none => .trapped (saved ++ args) (code ops)

def Phase.afterWasm {H : Type} (saved : List Value) (site : IndirectSite) (callee : WasmTarget)
    (ops : List (Op H)) : Graph.Phase → Phase H
  | .done (.values vs) => .source (saved ++ vs) ops
  | .done .trap => .trapped saved (code ops)
  | phase => .wasm saved site callee phase ops

def Phase.afterMemory {H : Type} (saved : List Value) (callee : MemoryTarget)
    (ops : List (Op H)) : MemoryCallee.Phase → Phase H
  | .done (.values vs) => .source (saved ++ vs) ops
  | .done .trap => .trapped saved (code ops)
  | phase => .memory saved callee phase ops

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
  | label :: rest => label.branchTypes :: targetTypes results rest

def labelBranchTypes {H : Type} (results : List NumType) : List (Label H) → List NumType
  | [] => results
  | label :: _ => label.branchTypes

def labelContinuation {H : Type} : List (Label H) → Wasm.Lime1.Expr
  | [] => []
  | label :: _ => label.continuation

def Label.RestartReady {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (targets : List (List NumType)) (label : Label H) : Prop :=
  match label.restart with
  | none => True
  | some body => label.type.Resolved active.module ∧
      Checked base active.module (active.locals.map Value.type) (label.type.signature.params :: targets)
        label.type.signature.results label.type.signature.params body ∧ Contract mem host body

inductive LabelsReady {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) : List (Label H) → Prop where
  | nil : LabelsReady mem host active results []
  | cons {label : Label H} {rest : List (Label H)}
      (tail : Checked base active.module (active.locals.map Value.type)
        (targetTypes results rest) (labelResults results rest)
        (label.saved.map Value.type ++ label.type.signature.results) label.tail)
      (contract : Contract mem host label.tail)
      (restart : label.RestartReady mem host active (targetTypes results rest))
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
  | .block label args arm => label.restart = none ∧ label.type.Resolved active.module ∧
      args.map Value.type = label.type.signature.params ∧
      Checked base active.module (active.locals.map Value.type)
        (label.type.signature.results :: targets) label.type.signature.results (args.map Value.type) arm ∧ Contract mem host arm ∧
      Checked base active.module (active.locals.map Value.type) targets delivered
        (label.saved.map Value.type ++ label.type.signature.results) label.tail ∧ Contract mem host label.tail
  | .invoke saved site args ops => site.Allocated base ∧ site.Arguments args ∧ site.Contract mem host ∧
      Checked base active.module (active.locals.map Value.type) targets delivered
        (saved.map Value.type ++ site.type.results) ops ∧ Contract mem host ops
  | .wasm saved site callee phase ops =>
      site.Linked base active.module ∧ site.graph.lookup callee.address = some callee.fn ∧
      callee.fn.declaration.type = site.signature ∧
      (∀ args, phase ≠ .call args) ∧ (∀ result, phase ≠ .done result) ∧
      Graph.Admitted site.graph callee.fn phase ∧
      Checked base active.module (active.locals.map Value.type) targets delivered
        (saved.map Value.type ++ site.signature.results) ops ∧ Contract mem host ops
  | .memory saved callee phase ops => callee.Allocated base ∧ callee.Checked mem ∧
      (∀ out, phase ≠ .done out) ∧ MemoryCallee.Ready callee phase ∧
      Checked base active.module (active.locals.map Value.type) targets delivered
        (saved.map Value.type ++ callee.fn.declaration.results) ops ∧ Contract mem host ops
  | .trapped _ _ => True
  | .frameResult out | .done out => labels = [] ∧ ResultTyped results out

/-- Native layers outside the active label, from the innermost context to
the enclosing function frame. -/
inductive Scope where
  | function (arity : Nat)
  | label (arity : Nat) (cont : Wasm.Lime1.Expr) (saved : List Value) (tail : List Admin) (outer : Scope)

def scopeFor {H : Type} (results : List NumType) : List (Label H) → Scope
  | [] => .function results.length
  | label :: rest => .label (labelBranchTypes results rest).length (labelContinuation rest)
      label.saved (code label.tail) (scopeFor results rest)

def frameContext (active : Frame) : Scope → EvalCtx Wasm.Lime1.Instr
  | .function arity => .frame arity active .hole
  | .label arity cont saved tail outer =>
      (frameContext active outer).comp (.label arity cont (.seq saved .hole tail))

def framed (active : Frame) (body : List Admin) : Scope → List Admin
  | .function arity => [.frame arity active body]
  | .label arity cont saved tail outer => framed active [.label arity cont (values saved ++ body ++ tail)] outer

def entered (arity : Nat) (active : Frame) (body : List Admin) : List Admin :=
  [.frame arity active [.label arity [] body]]

def invokeContext {H : Type} (scope : Scope) (arity : Nat) (cont : Wasm.Lime1.Expr) (active : Frame)
    (saved : List Value) (ops : List (Op H)) : EvalCtx Wasm.Lime1.Instr :=
  (frameContext active scope).comp (.label arity cont (.seq saved .hole (code ops)))

def Phase.renderIn {H : Type} (scope : Scope) (arity : Nat) (cont : Wasm.Lime1.Expr) (active : Frame) : Phase H → List Admin
  | .source stack ops => framed active [.label arity cont (values stack ++ code ops)] scope
  | .block label args arm => framed active [.label arity cont (values (label.saved ++ args) ++
      .source (.block label.type.blockType (expr arm)) :: code label.tail)] scope
  | .invoke saved site args ops => (invokeContext scope arity cont active saved ops).plug value
      (values args ++ [.invoke site.address])
  | .wasm saved _ callee phase ops =>
      framed active [.label arity cont (values saved ++ phase.render Graph.limeAdmin callee.callTarget ++ code ops)] scope
  | .memory saved callee phase ops =>
      framed active [.label arity cont (values saved ++ MemoryCallee.render callee phase ++ code ops)] scope
  | .trapped saved rest => framed active [.label arity cont (values saved ++ .trap :: rest)] scope
  | .frameResult out => framed active (result out) scope
  | .done out => result out

def Phase.renderCode {H : Type} (results : List NumType) (active : Frame)
    (phase : Phase H) (labels : List (Label H)) : List Admin :=
  phase.renderIn (scopeFor results labels) (labelBranchTypes results labels).length (labelContinuation labels) active

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
  | brTable {bytes stack selector depths fallback ops labels} :
      Edge mem host active results
        ⟨bytes, .source (stack ++ [Value.int .i32 selector]) (.brTable depths fallback :: ops), labels⟩
        ⟨bytes, .branch stack (depths[selector.toNat]?.getD fallback) ops, labels⟩
  | branchLower {bytes stack depth ops label labels} (positive : 0 < depth.toNat) :
      Edge mem host active results ⟨bytes, .branch stack depth ops, label :: labels⟩
        ⟨bytes, .branch (label.saved ++ stack) (lowerLabel depth) label.tail, labels⟩
  | branchDeliver {bytes scratch payload depth ops label labels} (zero : depth.toNat = 0)
      (exits : label.restart = none) (typed : payload.map Value.type = label.type.signature.results) :
      Edge mem host active results ⟨bytes, .branch (scratch ++ payload) depth ops, label :: labels⟩
        ⟨bytes, .source (label.saved ++ payload) label.tail, labels⟩
  | branchRestart {bytes scratch args depth ops label body labels} (zero : depth.toNat = 0)
      (loopBody : label.restart = some body) (typed : args.map Value.type = label.type.signature.params) :
      Edge mem host active results ⟨bytes, .branch (scratch ++ args) depth ops, label :: labels⟩
        ⟨bytes, .source (label.saved ++ args) (.loop label.type body :: label.tail), labels⟩
  | functionBranch {bytes scratch payload depth ops} (zero : depth.toNat = 0)
      (typed : payload.map Value.type = results) :
      Edge mem host active results ⟨bytes, .branch (scratch ++ payload) depth ops, []⟩
        ⟨bytes, .frameResult (.values payload), []⟩
  | if_ {bytes saved args guard type left right ops labels} (typed : args.map Value.type = type.signature.params) :
      Edge mem host active results ⟨bytes, .source ((saved ++ args) ++ [Value.int .i32 guard]) (.if_ type left right :: ops), labels⟩
        ⟨bytes, .block ⟨type, saved, ops, none⟩ args (select guard left right), labels⟩
  | block {bytes label args arm labels} (exits : label.restart = none) :
      Edge mem host active results ⟨bytes, .block label args arm, labels⟩ ⟨bytes, .source args arm, label :: labels⟩
  | loop {bytes saved args type body ops labels} (typed : args.map Value.type = type.signature.params) :
      Edge mem host active results ⟨bytes, .source (saved ++ args) (.loop type body :: ops), labels⟩
        ⟨bytes, .source args body, ⟨type, saved, ops, some body⟩ :: labels⟩
  | resolve {bytes saved args index site ops labels} (typed : site.Arguments args) :
      Edge mem host active results ⟨bytes, .source (saved ++ args) (.call index site :: ops), labels⟩
        ⟨bytes, .invoke saved site args ops, labels⟩
  | callIndirect {bytes saved args selector site target ops labels}
      (typed : args.map Value.type = site.signature.params) (found : site.Lookup base selector target) :
      Edge mem host active results
        ⟨bytes, .source ((saved ++ args) ++ [Value.int .i32 selector]) (.callIndirect site :: ops), labels⟩
        ⟨bytes, .afterLookup saved args site target ops, labels⟩
  | wasm {bytes saved site callee phase next ops labels}
      (move : site.graph.FrameEdge callee.address phase next) :
      Edge mem host active results ⟨bytes, .wasm saved site callee phase ops, labels⟩
        ⟨bytes, .afterWasm saved site callee ops next, labels⟩
  | memory {bytes written saved callee phase next ops labels}
      (move : MemoryCallee.Edge callee bytes phase written next) :
      Edge mem host active results ⟨bytes, .memory saved callee phase ops, labels⟩
        ⟨written, .afterMemory saved callee ops next, labels⟩
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
