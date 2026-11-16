module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Execution.Core.Exec.ValCheck
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Closed modules through the native interpreter: the common case

`Silmaril.Wasm.Interp.native_adequacy` equates the Core 3.0 behaviours of an invocation with the
native interpreter's, under four hypotheses on a store. For the most common case, a module with
no imports run in the empty environment, this topic replaces those hypotheses by Boolean checks
that the kernel evaluates (`decide +kernel`), and a terminating interpreter run by the exact
behaviour set:

* `prep m`, `store m`: silmaril-lean's executable instantiation `prepare?` of `m` into the empty
  store, and the store it allocates;
* `closed? m`: `m` validates, has no imports, allocates, and has **no start function and no
  segment initialisation code** (so `store m` is the store of the instance, before any call);
* `nativeCheck m`: `closed? m`, and every function of `store m` is in the native integer
  fragment (`nativeFuncsB`) and passes the arity check (`storeChkB`);
* `callOk m a vs`: `nativeCheck m`, and `vs` are typed arguments of function `a`
  (`invokeOk?`);
* `export? m x`: the function address exported under the name `x`;
* `run m fuel a vs`: one run of the native interpreter with `fuel`, as a behaviour.

**Partiality.** `run` returns `none` when the fuel runs out (or the interpreter cannot proceed);
that says nothing about the call, and the theorems need a `some`. Divergence is not established
by evaluation. A module outside the fragment (floats, packed or bulk memory, `memory.grow`,
tables, references; imports; a start function or active segments) fails `nativeCheck` or
`closed?`, and nothing is claimed about it.

Theorems in `Silmaril.Wasm.Interp.Closed.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.Closed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The executable instantiation of `m` into the empty store (a default when it fails). -/
def prep (m : Module) : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) m []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `m`. -/
def store (m : Module) : Store Empty := (prep m).1.store

/-- `m` validates without imports, allocates into the empty store, and has no start function
and no segment initialisation code. -/
def closed? (m : Module) : Bool :=
  ((Validation.validate? m).map fun mt => mt.imports.isEmpty) == some true &&
    match prepare? evalConst? ({} : Store Empty) m [] with
    | some p => p.1.code.isEmpty && p.2.isNone
    | none => false

/-- `closed? m`, and the store's functions pass the native-profile and arity checks. -/
def nativeCheck (m : Module) : Bool :=
  closed? m && Interp.nativeFuncsB (store m).funcs && Interp.storeChkB (store m).funcs

/-- `nativeCheck m`, and `vs` are typed arguments of function `a`. -/
def callOk (m : Module) (a : Nat) (vs : List Val) : Bool :=
  nativeCheck m && invokeOk? (store m) a vs

/-- The function address exported under `x`. -/
def export? (m : Module) (x : String) : Option Nat :=
  Binaryen.exportFunc? (prep m).1.frame.module x

/-- One run of the native interpreter with `fuel`, as a behaviour (`none`: out of fuel or
stuck; this proves nothing). -/
def run (m : Module) (fuel a : Nat) (vs : List Val) : Option (Behaviour Val) :=
  (Binaryen.invokeRun fuel (store m) a vs).bind fun r => Binaryen.flowBeh r.2

end Silmaril.Wasm.Interp.Closed
