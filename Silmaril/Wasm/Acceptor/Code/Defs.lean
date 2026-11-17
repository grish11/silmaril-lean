module

public import Silmaril.Wasm.Execution.Core.Store
public import Silmaril.Wasm.Validation.DefTypes

/-!
# The acceptor kit: code and instance facts

An acceptor module is an existing verified checker module extended by the canonical-ABI glue
(the allocator, a memory, the exported entry points, which `call` the checker's functions). Its
proofs need, of the instantiated module, that every function of the store has the module's
code, module instance and type. `Instr` has no decidable equality, so these facts are kernel
evaluations of Boolean comparisons:

* `ibeq`, `ibeqs`: equality of instructions of the acceptors' fragment (integer constants,
  locals, globals, integer operators, loads and stores without packing, `br`, `br_if`, `call`,
  `drop`, `if`/`block`/`loop` without block type), `false` outside it (sound: `ibeqs_sound`,
  `Thms`);
* `codeMatches fi f`: the function instance has the code of the module function `f`;
* `fnOk S m mi tys j`: function `j` of the store `S` has the code of function `j` of `m`, the
  module instance `mi` and the type `tys[j]`. `(List.range n).all (fnOk S m mi tys)` is the one
  kernel check per acceptor; `fn_of_fnOk` (`Thms`) reads it back;
* `miOf S`: the module instance of the store's first function (the instance of every function
  of a module instantiated without imports);
* `callf j`: `call j`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- `call j`. -/
abbrev callf (j : Nat) : Instr := .call ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

mutual
/-- Equality of instructions of the acceptors' fragment (`false` outside it). -/
def ibeq : Instr → Instr → Bool
  | .intConst .i32 a, .intConst .i32 b => a == b
  | .intConst .i64 a, .intConst .i64 b => a == b
  | .localGet x, .localGet y => x == y
  | .localSet x, .localSet y => x == y
  | .globalGet x, .globalGet y => x == y
  | .globalSet x, .globalSet y => x == y
  | .intBinOp t o, .intBinOp t' p => t == t' && o == p
  | .intRelOp t o, .intRelOp t' p => t == t' && o == p
  | .intTestOp t o, .intTestOp t' p => t == t' && o == p
  | .intLoad t none x a, .intLoad t' none y b => t == t' && x == y && a == b
  | .intStore t none x a, .intStore t' none y b => t == t' && x == y && a == b
  | .brIf l, .brIf m => l == m
  | .br l, .br m => l == m
  | .call x, .call y => x == y
  | .drop, .drop => true
  | .if_ .empty t e, .if_ .empty t' e' => ibeqs t t' && ibeqs e e'
  | .block .empty b, .block .empty b' => ibeqs b b'
  | .loop .empty b, .loop .empty b' => ibeqs b b'
  | _, _ => false
/-- Equality of instruction lists of the acceptors' fragment. -/
def ibeqs : List Instr → List Instr → Bool
  | [], [] => true
  | a :: as, b :: bs => ibeq a b && ibeqs as bs
  | _, _ => false
end

/-- The function instance has the code (body, locals, type index) of the module function. -/
def codeMatches {H : Type} (fi : FuncInst H) (f : Func) : Bool :=
  match fi.code with
  | .wasm g => ibeqs g.body f.body && g.locals == f.locals && g.type == f.type
  | .host _ => false

/-- The module instance of the store's first function. -/
def miOf {H : Type} (S : Store H) : ModuleInst := ((S.funcs[0]?).map (·.module)).getD {}

/-- Function `j` of the store `S`, function `j` of the module `m` and the type `tys[j]` agree:
the code, the module instance `mi` and the expanded type. -/
def fnOk {H : Type} (S : Store H) (m : Module) (mi : ModuleInst) (tys : List CCompType)
    (j : Nat) : Bool :=
  match S.funcs[j]?, m.funcs[j]?, tys[j]? with
  | some fi, some f, some ty => codeMatches fi f && fi.module == mi && fi.type.expand? == some ty
  | _, _, _ => false

end Silmaril.Wasm.Acceptor
