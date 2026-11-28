module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

open Execution.Runtime (Frame Result Value)
open CallContinuation.OuterCall.Computed
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked

/-- After entry the arguments determine the same frame until it is popped.
The relation carries live bytes separately from the frame and its operands. -/
inductive Phase (H : Type) where
  | invoke (args : List Value)
  | body (args stack : List Value) (ops : List Graph.Memory32.Op)
  | ifBlock (args saved : List Value) (type : Option NumType) (arm rest : List Graph.Memory32.Op)
  | arm (args saved : List Value) (type : Option NumType) (phase : Phase H) (rest : List Graph.Memory32.Op)
  | child (args saved : List Value) (callee : MemoryTarget) (phase : Phase H) (rest : List Graph.Memory32.Op)
  | hostInvoke (args saved : List Value) (target : Site H) (operands : List Value) (rest : List Graph.Memory32.Op)
  | branch (args stack : List Value) (depth : LabelIdx) (result : List NumType) (rest : List Graph.Memory32.Op)
  /-- The current label has been removed, leaving a branch for the enclosing label. -/
  | lowered (args stack : List Value) (depth : LabelIdx) (result : List NumType)
  | trapped (args stack : List Value) (rest : List Admin)
  | exit (args : List Value) (out : Result)
  | done (out : Result)

def code (ops : List Graph.Memory32.Op) : List Admin :=
  expression (ops.map fun op => op.v1.toLime)

def expr (ops : List Graph.Memory32.Op) : Wasm.Lime1.Expr :=
  ops.map fun op => op.v1.toLime

def blockType (type : Option NumType) : Wasm.Lime1.BlockType := Wasm.V1.BlockType.toLime type

def selectArm (guard : BitVec 32) (left right : List Graph.Memory32.Op) : List Graph.Memory32.Op :=
  if guard = 0 then right else left

def resultTyped (types : List NumType) : Result → Prop
  | .values vs => vs.map Value.type = types
  | .trap => True

def Typed (callee : MemoryTarget) (types : List NumType) (labels : List (List NumType))
    (stack : List Value) (ops : List Graph.Memory32.Op) : Prop :=
  callee.fn.checkRegion (Prefix.stackTypes stack) types ops labels = true

def InLabel {H : Type} (args : List Value) : Phase H → Prop
  | .body current .. | .ifBlock current .. | .arm current .. | .child current ..
  | .hostInvoke current .. | .branch current .. | .trapped current .. => current = args
  | _ => False

def FromCode (callee : MemoryTarget) (ops : List Graph.Memory32.Op) : Prop :=
  MemoryTarget.sourceOps ops ⊆ MemoryTarget.sourceOps callee.fn.code

def BranchTyped (labels : List (List NumType)) (depth : LabelIdx) (result : List NumType) (stack : List Value) : Prop :=
  labels[depth.toNat]? = some result ∧ Graph.SuffixTyped result stack

/-- Live regions and suspended suffixes retain the type and source links
needed to resume with the ordered result of an arm or invocation. Here
`labels` holds the explicit results, innermost first. The implicit function
label is the final target in both region and pending-branch checking. -/
def ReadyAt {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H) (site : IndirectSite)
    (callee : MemoryTarget) (types : List NumType) (labels : List (List NumType)) : Phase H → Prop
  | .invoke args => args.map Value.type = callee.fn.declaration.params ∧
      types = callee.fn.declaration.results ∧ labels = []
  | .branch args stack depth result _ => args.map Value.type = callee.fn.declaration.params ∧
      BranchTyped (labels ++ callee.fn.entryLabels) depth result stack
  | .lowered args stack depth result => args.map Value.type = callee.fn.declaration.params ∧
      BranchTyped (labels ++ callee.fn.entryLabels).tail depth result stack
  | .trapped args _ _ => args.map Value.type = callee.fn.declaration.params
  | .body args stack ops => args.map Value.type = callee.fn.declaration.params ∧
      ops.all (MemoryTarget.supportedOpAt mem.extent.growthEnabled labels.length) = true ∧ Typed callee types (labels ++ callee.fn.entryLabels) stack ops ∧
      FromCode callee ops
  | .ifBlock args saved type arm rest =>
      args.map Value.type = callee.fn.declaration.params ∧
      arm.all (MemoryTarget.supportedOpAt mem.extent.growthEnabled (labels.length + 1)) = true ∧ FromCode callee arm ∧
      Typed callee type.toList (type.toList :: (labels ++ callee.fn.entryLabels)) [] arm ∧
      rest.all (MemoryTarget.supportedOpAt mem.extent.growthEnabled labels.length) = true ∧ FromCode callee rest ∧
      ∀ vs : List Value, vs.map Value.type = type.toList → Typed callee types (labels ++ callee.fn.entryLabels) (saved ++ vs) rest
  | .arm args saved type phase rest =>
      args.map Value.type = callee.fn.declaration.params ∧ InLabel args phase ∧
      ReadyAt mem host site callee type.toList (type.toList :: labels) phase ∧
      rest.all (MemoryTarget.supportedOpAt mem.extent.growthEnabled labels.length) = true ∧ FromCode callee rest ∧
      ∀ vs : List Value, vs.map Value.type = type.toList → Typed callee types (labels ++ callee.fn.entryLabels) (saved ++ vs) rest
  | .child args saved child phase rest =>
      args.map Value.type = callee.fn.declaration.params ∧
      site.memoryLookup child.address = some child.fn ∧ child.Allocated base ∧
      (∀ out, phase ≠ .done out) ∧ ReadyAt mem host site child child.fn.declaration.results [] phase ∧
      rest.all (MemoryTarget.supportedOpAt mem.extent.growthEnabled labels.length) = true ∧ FromCode callee rest ∧
      ∀ vs : List Value, vs.map Value.type = child.fn.declaration.results → Typed callee types (labels ++ callee.fn.entryLabels) (saved ++ vs) rest
  | .hostInvoke args saved target operands rest =>
      args.map Value.type = callee.fn.declaration.params ∧
      target.Allocated base ∧ target.Arguments operands ∧ target.Contract mem host ∧
      rest.all (MemoryTarget.supportedOpAt mem.extent.growthEnabled labels.length) = true ∧ FromCode callee rest ∧
      ∀ vs : List Value, target.TypedResult (.values vs) → Typed callee types (labels ++ callee.fn.entryLabels) (saved ++ vs) rest
  | .exit args out => args.map Value.type = callee.fn.declaration.params ∧ resultTyped types out
  | .done out => resultTyped types out

abbrev Ready {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H) (site : IndirectSite)
    (callee : MemoryTarget) : Phase H → Prop :=
  ReadyAt mem host site callee callee.fn.declaration.results []

def frameCode : Bool → Nat → Frame → List Admin → List Admin
  | true, arity, frame, body => [.frame arity frame body]
  | false, _, _, body => body

/-- Function activation rendering and label-only rendering use the same
active body. Only actual calls install a native frame in rendered execution. -/
def renderUnder {H : Type} (callee : MemoryTarget) (arity : Nat) (boxed : Bool) : Phase H → List Admin
  | .invoke args => values args ++ [.invoke callee.address]
  | .body args stack ops => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values stack ++ code ops)]
  | .ifBlock args saved type arm rest => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values saved ++ .source (.block (blockType type) (expr arm)) :: code rest)]
  | .arm args saved type phase rest => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values saved ++ renderUnder callee type.toList.length false phase ++ code rest)]
  | .child args saved child phase rest => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values saved ++ renderUnder child child.fn.declaration.results.length true phase ++ code rest)]
  | .hostInvoke args saved target operands rest => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values (saved ++ operands) ++ .invoke target.address :: code rest)]
  | .branch args stack depth _ rest => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values stack ++ .source (.br depth) :: code rest)]
  | .lowered args stack depth _ => frameCode boxed arity (callee.fn.declaration.frame args)
      (values stack ++ [.source (.br depth)])
  | .trapped args stack rest => frameCode boxed arity (callee.fn.declaration.frame args)
      [.label arity [] (values stack ++ .trap :: rest)]
  | .exit args out => frameCode boxed arity (callee.fn.declaration.frame args) (result out)
  | .done out => result out

abbrev renderAt {H : Type} (callee : MemoryTarget) (arity : Nat) : Phase H → List Admin :=
  renderUnder callee arity true

abbrev render {H : Type} (callee : MemoryTarget) : Phase H → List Admin :=
  renderAt callee callee.fn.declaration.results.length

def afterBrIf {H : Type} (args stack : List Value) (depth : LabelIdx) (result : List NumType) (rest : List Graph.Memory32.Op)
    (guard : BitVec 32) : Phase H :=
  if guard = 0 then .body args stack rest else .branch args stack depth result rest

def afterArm {H : Type} (args saved : List Value) (type : Option NumType) (rest : List Graph.Memory32.Op) :
    Phase H → Phase H
  | .exit _ (.values vs) => .body args (saved ++ vs) rest
  | .exit _ .trap => .trapped args saved (code rest)
  | .lowered _ stack depth result => .branch args (saved ++ stack) depth result rest
  | phase => .arm args saved type phase rest

def afterChild {H : Type} (args saved : List Value) (child : MemoryTarget) (rest : List Graph.Memory32.Op) : Phase H → Phase H
  | .done (.values vs) => .body args (saved ++ vs) rest
  | .done .trap => .trapped args saved (code rest)
  | phase => .child args saved child phase rest

def configAt {H : Type} {base : Store H} (mem : Memory32 base) (caller : Frame)
    (saved : List Value) (tail : List Admin) (callee : MemoryTarget) (arity : Nat) (bytes : ByteArray)
    (phase : Phase H) : Config H :=
  ⟨mem.store bytes, caller, values saved ++ renderAt callee arity phase ++ tail⟩

abbrev config {H : Type} {base : Store H} (mem : Memory32 base) (caller : Frame)
    (saved : List Value) (tail : List Admin) (callee : MemoryTarget) (bytes : ByteArray)
    (phase : Phase H) : Config H :=
  configAt mem caller saved tail callee callee.fn.declaration.results.length bytes phase

/-- The page count encoded as the i32 result of a size or successful grow. -/
def pages (bytes : ByteArray) : Value :=
  .int .i32 (BitVec.ofNat 32 (Execution.Memory.size bytes))

inductive Edge {H : Type} {base : Store H} (mem : Memory32 base)
    (host : HostSemantics H) (site : IndirectSite) : MemoryTarget → ByteArray → Phase H → ByteArray → Phase H → Prop where
  | enter {callee bytes args} : Edge mem host site callee bytes (.invoke args) bytes (.body args callee.fn.initial callee.fn.code)
  | get {callee bytes args stack index ops v}
      (found : (callee.fn.declaration.frame args).locals[index.toNat]? = some v) :
      Edge mem host site callee bytes (.body args stack (.ranked (.numeric (.get index)) :: ops))
        bytes (.body args (stack ++ [v]) ops)
  | load {callee bytes args saved offset ptr ops bits}
      (read : MemoryQuery.EdgeAt bytes offset.val (.load ptr) (.value bits)) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr]) (.load offset :: ops))
        bytes (.body args (saved ++ [Value.int .i32 bits]) ops)
  | loadTrap {callee bytes args saved offset ptr ops}
      (read : MemoryQuery.EdgeAt bytes offset.val (.load ptr) .trap) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr]) (.load offset :: ops))
        bytes (.trapped args saved (code ops))
  | store {callee bytes written args saved offset ptr word ops}
      (write : MemoryWrite.EdgeAt bytes offset.val (.store ptr word) (.written written)) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))
        written (.body args saved ops)
  | storeTrap {callee bytes args saved offset ptr word ops}
      (write : MemoryWrite.EdgeAt bytes offset.val (.store ptr word) .trap) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))
        bytes (.trapped args saved (code ops))
  | size {callee bytes args stack ops} :
      Edge mem host site callee bytes (.body args stack (.size :: ops)) bytes (.body args (stack ++ [pages bytes]) ops)
  | grow {callee bytes grown args saved delta ops} (enabled : mem.extent.growthEnabled = true)
      (move : MemoryGrow.Edge (mem.current bytes) (.request delta) (.grown grown)) :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 delta]) (.grow :: ops))
        grown (.body args (saved ++ [pages bytes]) ops)
  | growFail {callee bytes args saved delta ops} :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 delta]) (.grow :: ops))
        bytes (.body args (saved ++ [Value.int .i32 (-1)]) ops)
  | call {callee child bytes args saved operands target rest}
      (link : site.MemoryDirect (base := base) callee target child)
      (typed : operands.map Value.type = target.declaration.params) :
      Edge mem host site callee bytes (.body args (saved ++ operands) (.ranked (.call target) :: rest))
        bytes (.child args saved child (.invoke operands) rest)
  | callHost {callee bytes args saved operands target rest hostCode}
      (link : MemoryDirectHost mem host callee target hostCode)
      (typed : operands.map Value.type = target.declaration.params) :
      Edge mem host site callee bytes (.body args (saved ++ operands) (.ranked (.call target) :: rest))
        bytes (.hostInvoke args saved (Site.directTarget target hostCode) operands rest)
  | callIndirect {callee child bytes args saved operands index signature selector rest}
      (lookup : (site.memorySite index signature).Lookup base selector (some (.memory child)))
      (typed : operands.map Value.type = signature.params) :
      Edge mem host site callee bytes (.body args ((saved ++ operands) ++ [Value.int .i32 selector])
        (.callIndirect index signature :: rest)) bytes (.child args saved child (.invoke operands) rest)
  | callIndirectHost {callee target bytes args saved operands index signature selector rest}
      (lookup : (site.memorySite index signature).Lookup base selector (some (.host target)))
      (typed : operands.map Value.type = signature.params) :
      Edge mem host site callee bytes (.body args ((saved ++ operands) ++ [Value.int .i32 selector])
        (.callIndirect index signature :: rest)) bytes (.hostInvoke args saved target operands rest)
  | indirectTrap {callee bytes args stack index signature selector rest}
      (lookup : (site.memorySite index signature).Lookup base selector none) :
      Edge mem host site callee bytes (.body args (stack ++ [Value.int .i32 selector])
        (.callIndirect index signature :: rest)) bytes (.trapped args stack (code rest))
  | hostReturned {callee target bytes written args saved operands rest vs} (live : mem.Live written)
      (typed : target.TypedResult (.values vs))
      (answer : host target.code (mem.store bytes) operands (.returned (mem.store written) (.values vs))) :
      Edge mem host site callee bytes (.hostInvoke args saved target operands rest)
        written (.body args (saved ++ vs) rest)
  | hostTrapped {callee target bytes written args saved operands rest} (live : mem.Live written)
      (answer : host target.code (mem.store bytes) operands (.returned (mem.store written) .trap)) :
      Edge mem host site callee bytes (.hostInvoke args saved target operands rest)
        written (.trapped args saved (code rest))
  | hostDiverged {callee target bytes args saved operands rest}
      (answer : host target.code (mem.store bytes) operands .diverged) :
      Edge mem host site callee bytes (.hostInvoke args saved target operands rest)
        bytes (.hostInvoke args saved target operands rest)
  | brIf {callee bytes args stack depth result rest guard} :
      Edge mem host site callee bytes (.body args (stack ++ [Value.int .i32 guard])
        (.ranked (.brIf depth result) :: rest)) bytes (afterBrIf args stack depth result rest guard)
  | branchDone {callee bytes args scratch payload result rest} (typed : payload.map Value.type = result) :
      Edge mem host site callee bytes (.branch args (scratch ++ payload) ⟨0⟩ result rest) bytes (.exit args (.values payload))
  | branchLower {callee bytes args stack depth result rest} (outer : 0 < depth.toNat) :
      Edge mem host site callee bytes (.branch args stack depth result rest)
        bytes (.lowered args stack (lowerLabel depth) result)
  | ifSelect {callee bytes args saved type left right rest guard} :
      Edge mem host site callee bytes (.body args (saved ++ [Value.int .i32 guard]) (.if_ type left right :: rest))
        bytes (.ifBlock args saved type (selectArm guard left right) rest)
  | ifEnter {callee bytes args saved type arm rest} :
      Edge mem host site callee bytes (.ifBlock args saved type arm rest) bytes (.arm args saved type (.body args [] arm) rest)
  | armStep {callee bytes written args saved type phase next rest}
      (entered : InLabel args phase) (move : Edge mem host site callee bytes phase written next) :
      Edge mem host site callee bytes (.arm args saved type phase rest) written (afterArm args saved type rest next)
  | child {callee child bytes written args saved phase next rest}
      (move : Edge mem host site child bytes phase written next) :
      Edge mem host site callee bytes (.child args saved child phase rest)
        written (afterChild args saved child rest next)
  | erase {callee bytes args stack kept removed before cut rest}
      (split : stack = kept ++ removed) (suffix : before = cut ++ rest) (active : removed ≠ [] ∨ cut ≠ []) :
      Edge mem host site callee bytes (.trapped args stack before) bytes (.trapped args kept rest)
  | labelDone {callee bytes args vs} : Edge mem host site callee bytes (.body args vs []) bytes (.exit args (.values vs))
  | labelTrap {callee bytes args} : Edge mem host site callee bytes (.trapped args [] []) bytes (.exit args .trap)
  | frameDone {callee bytes args out} : Edge mem host site callee bytes (.exit args out) bytes (.done out)

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee
