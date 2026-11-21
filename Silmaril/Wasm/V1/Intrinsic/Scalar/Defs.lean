module

public import Silmaril.Wasm.V1.ToCore
public import Silmaril.Wasm.V1.Validation.Modules
public import Silmaril.Wasm.ModuleBuilder

/-! # Native intrinsic Wasm 1.0 scalar code

Instructions use the V1 context and bottom-to-top operand stacks. The fragment
supports integer computation, scalar selection, locals, and direct calls. A
body composes effects over preserved stack prefixes without inserting raw code.
The closed module form contains one exported definition with its own signature
already in scope, so direct self calls do not require unfolding the definition.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Intrinsic.Scalar

open Validation (Context functionContext)

inductive Instr (ctx : Context) : ResultType → ResultType → Type where
  | intConst (width : IntType) (bits : BitVec width.width) : Instr ctx [] [.int width]
  | intBinOp (width : IntType) (op : IntBinOp) : Instr ctx [.int width, .int width] [.int width]
  | intRelOp (width : IntType) (op : IntRelOp) : Instr ctx [.int width, .int width] [.i32]
  | select (ty : ValType) : Instr ctx [ty, ty, .i32] [ty]
  | localGet (idx : LocalIdx) {ty : ValType} (resolved : ctx.locals[idx.toNat]? = some ty) :
      Instr ctx [] [ty]
  | localSet (idx : LocalIdx) {ty : ValType} (resolved : ctx.locals[idx.toNat]? = some ty) :
      Instr ctx [ty] []
  | call (idx : FuncIdx) {sig : FuncType} (resolved : ctx.funcs[idx.toNat]? = some sig) :
      Instr ctx sig.params sig.results

def Instr.erase {ctx inputs outputs} : Instr ctx inputs outputs → V1.Instr
  | .intConst width bits => .intConst width bits
  | .intBinOp width op => .intBinOp width op
  | .intRelOp width op => .intRelOp width op
  | .select _ => .select
  | .localGet idx _ => .localGet idx
  | .localSet idx _ => .localSet idx
  | .call idx _ => .call idx

inductive Body (ctx : Context) : ResultType → ResultType → Type where
  | nil (stack : ResultType) : Body ctx stack stack
  | step (pre : ResultType) {inputs outputs result : ResultType} :
      Instr ctx inputs outputs → Body ctx (pre ++ outputs) result → Body ctx (pre ++ inputs) result

def Body.erase {ctx inputs outputs} : Body ctx inputs outputs → V1.Expr
  | .nil _ => []
  | .step _ head tail => head.erase :: tail.erase

/-- Emit a Core expression in a single traversal using the existing V1
instruction injection. No validation or parsing runs during emission. -/
def Body.toCore {ctx inputs outputs} : Body ctx inputs outputs → Wasm.Expr
  | .nil _ => []
  | .step _ head tail => head.erase.toCore :: tail.toCore

structure Function (ctx : Context) (type : TypeIdx) (sig : FuncType) where
  resolved : ctx.types[type.toNat]? = some sig
  singleResult : Validation.FuncTypeValid sig
  locals : List ValType
  body : Body (functionContext ctx sig locals) [] sig.results

def Function.erase {ctx type sig} (term : Function ctx type sig) : V1.Func :=
  ⟨type, term.locals, term.body.erase⟩

def Function.toCore {ctx type sig} (term : Function ctx type sig) : Wasm.Func :=
  ⟨type, term.locals.map ValType.toCore, term.body.toCore⟩

/-- The signature is in both index spaces before the function body is built. -/
def closedContext (sig : FuncType) : Context := { types := [sig], funcs := [sig] }

/-- One definition and one export; no imports, state sections or start. -/
structure ClosedModule (sig : FuncType) where
  exportName : String
  fn : Function (closedContext sig) ⟨0⟩ sig

def ClosedModule.erase {sig} (term : ClosedModule sig) : V1.Module :=
  Wasm.Scalar.Module.ofFunction sig term.fn.locals term.fn.body.erase (some term.exportName)

def ClosedModule.toCore {sig} (term : ClosedModule sig) : Wasm.Module where
  types := [sig.toCoreRec]
  funcs := [term.fn.toCore]
  exports := [⟨term.exportName, .func ⟨0⟩⟩]

end Silmaril.Wasm.V1.Intrinsic.Scalar
