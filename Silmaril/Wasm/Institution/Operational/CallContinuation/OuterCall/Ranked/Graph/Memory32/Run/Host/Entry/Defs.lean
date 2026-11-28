module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Defs

/-!
# Entry to one checked V1 direct host site

The entry function is allocated with its actual source, including the host call.
Below that entry, the existing checked graph supplies the callees of the tail.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (EvalCtx Frame FuncAddr MemAddr MemInst Value)
open Computed
open Wasm.V1.Execution

/-- The function describes the declaration, initial operands and graph tail.
The prefix and designated call are inserted between the operands and tail. -/
structure HostEntry (H : Type) where
  index : FuncIdx
  address : FuncAddr
  function : Function
  operands : List Prefix.Op
  site : HostCall.V1.Site H

namespace HostEntry

variable {H : Type}

def v1Func (entry : HostEntry H) : Wasm.V1.Func :=
  let fn := entry.function
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.initial.map Graph.v1CodeSyntax.ops.value ++
    entry.operands.map (Prefix.emit Graph.v1CodeSyntax.ops) ++
    .call entry.site.index :: v1Code fn.code⟩

def tail (entry : HostEntry H) : List Admin := expression (v1Code entry.function.code)

def context (entry : HostEntry H) (args : List Value) : EvalCtx Wasm.V1.Instr :=
  let fn := entry.function
  let arity := fn.declaration.results.length
  .frame arity (fn.declaration.frame args) (.label arity [] .hole)

/-- Source checks and exact native allocation. The graph code guard for the
tail is independent of the operand values and host behavior. -/
structure Checked (entry : HostEntry H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (base : Store H) (outer : Frame) (args : List Value) : Prop where
  resolved : outer.module.funcs[entry.index.toNat]? = some entry.address
  allocated : base.funcs[entry.address.value]? =
    some (.wasm entry.function.declaration.type entry.function.declaration.module entry.v1Func)
  parameters : args.map Value.type = entry.function.declaration.params
  scalar : entry.function.declaration.results.length ≤ 1
  slot : entry.function.declaration.module.memories[0]? = some memory
  linkedHost : entry.function.declaration.module.funcs[entry.site.index.toNat]? = some entry.site.address
  allocatedHost : base.funcs[entry.site.address.value]? = some (.host entry.site.signature entry.site.target)
  scalarHost : entry.site.signature.results.length ≤ 1
  typedBody : entry.function.checkHostPrefix (Prefix.stackTypes entry.function.initial) entry.operands
    entry.site.signature entry.function.code entry.function.declaration.results entry.function.entryLabels = true
  supportedTail : supportedCode entry.function.code entry.function.entryLabels mode
    (program.checkIndirect calls entry.function.rank entry.function.declaration.module) = true
  linkedTail : ∀ target ∈ entry.function.targets, ∃ callee, program.lookup target.address = some callee ∧
    callee.declaration = target.declaration ∧
    entry.function.declaration.module.funcs[target.index.toNat]? = some target.address ∧
    calls.permits entry.function.rank callee.rank

/-- Require the embedding contract at this site's actual input store, for
each ordered argument vector matching the declared parameter types. -/
def Contract (entry : HostEntry H) (host : HostSemantics H) (mode : MemoryMode) (memory : MemAddr)
    (initial : MemInst) (live : Store H) : Prop :=
  ∀ args : List Value, args.map Value.type = entry.site.signature.params →
    entry.site.ReturnContract host (HostStoreEffect mode memory initial) live args

inductive Phase where
  | call
  | invoke
  | computing (stack : List Value) (remaining : List Prefix.Op)
  | trapped (saved : List Value) (tail : List Admin)
  | pending (saved args : List Value)
  | graph (state : State)

def render (entry : HostEntry H) (base : Store H) (memory : MemAddr) (initial : MemInst)
    (bytes : ByteArray) (outer : Frame) (args : List Value) (phase : Phase) : Config H :=
  let live := storeWithBytes base memory initial bytes
  let k := entry.context args
  match phase with
  | .call => ⟨live, outer, values args ++ [.source (.call entry.index)]⟩
  | .invoke => ⟨live, outer, values args ++ [.invoke entry.address]⟩
  | .computing stack remaining =>
    ⟨live, outer, k.plug value (values stack ++ remaining.map (Prefix.emit v1Syntax) ++
      .source (.call entry.site.index) :: entry.tail)⟩
  | .trapped saved tail => ⟨live, outer, k.plug value (values saved ++ .trap :: tail)⟩
  | .pending saved actual =>
    ⟨live, outer, k.plug value (entry.site.pending live (k.activeFrame outer) saved actual entry.tail).code⟩
  | .graph state => Memory32.render base memory initial state

/-- The live frame is fixed during numeric computation and host delivery.
Once the site delivers, the original graph invariant governs the whole run. -/
def Ready (entry : HostEntry H) (mode : MemoryMode) (program : Program) (memory : MemAddr)
    (calls : CallMode) (initial : MemInst) (args : List Value) : Phase → Prop
  | .call | .invoke | .trapped .. => True
  | .computing stack remaining =>
    HostPrefixTyped entry.function (entry.function.declaration.frame args) stack remaining
      entry.site.signature entry.function.code entry.function.declaration.results entry.function.entryLabels
  | .pending saved actual =>
    actual.map Value.type = entry.site.signature.params ∧
      entry.function.checkRegion (entry.site.signature.results.reverse ++ Prefix.stackTypes saved)
        entry.function.declaration.results entry.function.code entry.function.entryLabels = true
  | .graph state => ReadyFor mode program memory calls (entry.function.rank + 1) initial.data.size state

/-- The entry phases reuse native administrative boundaries and the existing
numeric-prefix and Memory32 graph transitions. -/
inductive Edge (entry : HostEntry H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (bytes : ByteArray) (outer : Frame) (args : List Value) : Phase → Phase → Prop where
  | resolve : Edge entry host mode program memory base initial bytes outer args .call .invoke
  | enter : Edge entry host mode program memory base initial bytes outer args .invoke
      (.computing entry.function.initial entry.operands)
  | numeric {stack next op rest}
      (move : Prefix.Reduce (entry.function.declaration.frame args).locals stack op (.values next)) :
      Edge entry host mode program memory base initial bytes outer args (.computing stack (op :: rest))
        (.computing next rest)
  | prefixTrap {stack saved op rest}
      (move : Prefix.Reduce (entry.function.declaration.frame args).locals stack op (.trap saved)) :
      Edge entry host mode program memory base initial bytes outer args (.computing stack (op :: rest))
        (.trapped saved (rest.map (Prefix.emit v1Syntax) ++ .source (.call entry.site.index) :: entry.tail))
  | discard {saved tail kept rest} (move : Prefix.Discard saved tail kept rest) :
      Edge entry host mode program memory base initial bytes outer args (.trapped saved tail) (.trapped kept rest)
  | closeTrap :
      Edge entry host mode program memory base initial bytes outer args (.trapped [] [])
        (.graph ⟨bytes, outer, [.frame entry.function.declaration.results.length
          (entry.function.declaration.frame args) [.trap]]⟩)
  | hostResolve {saved actual} (typed : actual.map Value.type = entry.site.signature.params) :
      Edge entry host mode program memory base initial bytes outer args (.computing (saved ++ actual) [])
        (.pending saved actual)
  | returned {saved actual s' r next}
      (behavior : host entry.site.target (storeWithBytes base memory initial bytes) actual (.returned s' r))
      (stored : s' = storeWithBytes base memory initial next) :
      Edge entry host mode program memory base initial bytes outer args (.pending saved actual)
        (.graph ⟨next, outer, (entry.context args).plug value (values saved ++ result r ++ entry.tail)⟩)
  | diverged {saved actual}
      (behavior : host entry.site.target (storeWithBytes base memory initial bytes) actual .diverged) :
      Edge entry host mode program memory base initial bytes outer args (.pending saved actual) (.pending saved actual)
  | graph {src dst} (move : EdgeAt mode program memory src dst) :
      Edge entry host mode program memory base initial bytes outer args (.graph src) (.graph dst)

abbrev Runs (entry : HostEntry H) (host : HostSemantics H) (mode : MemoryMode)
    (program : Program) (memory : MemAddr) (base : Store H) (initial : MemInst)
    (bytes : ByteArray) (outer : Frame) (args : List Value) :=
  Relation.ReflTransGen (entry.Edge host mode program memory base initial bytes outer args)

end HostEntry
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
