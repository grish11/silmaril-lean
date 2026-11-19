module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Checkers.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Replay

/-!
# Executable AST reader checkers: examples (non-vacuity)

`addCheck_sound` (`Silmaril.Wasm.Game.HandleAccept.Ast.Checkers.Thms`) bounds the reader language
of `addCheck` by the trees `add(num a, num b)`. Here it is shown non-empty by running the module:
the call `check(0)` (candidate argument `0`, `Silmaril.Wasm.Resource.replayExport`) is replayed on
the verified interpreter with the import answers of a concrete handle table (`addScript`), by
kernel evaluation, and every decoded read is checked correct in a concrete environment, with
handle `0` accepted (`Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.mem_astLang_of_replay`).

**Profiles.** Every profile `P` admitting the deterministic steps of the interpreter (hypothesis
`hP`), in particular every specification profile `Profile.spec nd {}` (the `_spec` corollary).

* `addEnv a b`: handle `0` denotes `add(num a, num b)`, `1` the leaf `num a`, `2` the leaf
  `num b`; no other handle is defined.
* `add(num 1, num 2)` is accepted by `addCheck` (`addCheck_accepts_12`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Ast.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept.Ast.Examples

/-- The tree `add(num a, num b)`. -/
def addTree (a b : Int64) : AST arithSig.toAstSig :=
  TExpr.ofList (⟨ArithTag.add, ()⟩ : Σ t, arithSig.toAstSig.Arg t) [numLeaf a, numLeaf b]

/-- The handle table of `add(num a, num b)`: `tag` answers code `1` (`add`) for handle `0` and
code `0` (`num`) with the payload `a` or `b` for handles `1` and `2`; `count` answers `2` for `0`
and `0` otherwise; `child(h, i)` answers `i + 1`. -/
def addScript (a b : Int64) : Script := fun _ h args =>
  if h = arithRIx.child then
    match args with
    | [_, .num ⟨.int .i32, i⟩] => [Val.i32 (BitVec.ofNat 32 (i.toNat + 1))]
    | _ => []
  else
    match Silmaril.Wasm.Game.HandleAccept.i32Arg args with
    | none => []
    | some x =>
      if h = arithRIx.tag then
        if x = 0 then [Val.i32 1, Val.i64 0] else if x = 1 then [Val.i32 0, Val.i64 a.toBitVec]
        else [Val.i32 0, Val.i64 b.toBitVec]
      else if h = arithRIx.count then [Val.i32 (if x = 0 then 2 else 0)]
      else []

/-- The environment of `addScript`: handle `0` denotes `add(num a, num b)`. -/
def addEnv (a b : Int64) : Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig) :=
  fun h =>
    if h = 0 then some (addTree a b) else if h = 1 then some (numLeaf a)
    else if h = 2 then some (numLeaf b) else none

open Silmaril.Proofs.Wasm.Game.HandleAccept.Ast (mem_astLang_of_replay arithTagEq_sound)

theorem addCheck_accepts_12 {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    addTree 1 2 ∈ moduleAstLang P addCheck arithRIx .trap .callTrap {addEnv 1 2} :=
  mem_astLang_of_replay addCheck_instance hP arithRIx .trap .callTrap (Set.mem_singleton _)
    arithTagEq_sound (addScript 1 2) refFuel 16 ⟨0, by decide +kernel⟩ 0 0 rfl
    (by decide +kernel) (by decide +kernel)

theorem addCheck_accepts_12_spec (nd : Bool) :
    addTree 1 2 ∈
      moduleAstLang (Profile.spec nd {}) addCheck arithRIx .trap .callTrap {addEnv 1 2} :=
  addCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- `addTree 1 2` is a member of `addL`, the bound of `addCheck_sound`. -/
theorem addTree_mem_addL : addTree 1 2 ∈ addL := ⟨1, 2, rfl⟩

end Silmaril.Wasm.Game.HandleAccept.Ast.Checkers
