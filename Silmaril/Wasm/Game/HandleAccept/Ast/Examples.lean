module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Thms

/-!
# Tagged-AST APIs: examples

The arithmetic signature `arithSig`: `num(s64)` (no children), `add` (two children) and `neg`
(one child). The module `arithBuild` (imports `0 num : [i64] → [i32]`,
`1 add : [i32 i32] → [i32]`, `2 accept : [i32] → []`; export `run : [i64] → []`) accepts
`add(num(x), num(x))`. It validates and instantiates (`arithBuild_instance`), and every tree it
accepts is well-arity (`arithBuild_wellArity`, from `moduleAstWLang_wellArity`). Scalar payload
decoding is checked on concrete values (`ofVals_example`, `ofVals_bool`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Ast.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats Silmaril.Accept.Handle

/-- Tags of the arithmetic signature. -/
inductive ArithTag where
  | num
  | add
  | neg
  deriving DecidableEq

/-- **The arithmetic signature.** -/
def arithSig : WitSig where
  Tag := ArithTag
  params
    | .num => [.s64]
    | .add => []
    | .neg => []
  arity
    | .num => .fixed 0
    | .add => .fixed 2
    | .neg => .fixed 1

/-- `[i64] → [i32]`. -/
def tyNum : RecType := ⟨[⟨true, [], .func ⟨[.i64], [.i32]⟩⟩]⟩
/-- `[i32 i32] → [i32]`. -/
def tyAdd : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[i64] → []`. -/
def tyRun : RecType := ⟨[⟨true, [], .func ⟨[.i64], []⟩⟩]⟩

/-- **Accept `add(num(x), num(x))`.** -/
def arithBuild : Module where
  types := [tyNum, tyAdd, tyA, tyRun]
  imports := [⟨"ast", "num", .func ⟨0⟩⟩, ⟨"ast", "add", .func ⟨1⟩⟩, ⟨"ast", "accept", .func ⟨2⟩⟩]
  funcs := [⟨⟨3⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩, .localGet ⟨0⟩, .call ⟨0⟩, .call ⟨1⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Its imports as AST writer imports. -/
def arithIx : AstWImports arithSig where
  tagOf
    | 0 => some ArithTag.num
    | 1 => some ArithTag.add
    | _ => none
  accept := 2

theorem arithBuild_instance : (Verify.instance? arithBuild).isSome = true := by decide +kernel

/-- **`arithBuild` accepts only well-arity trees** (every profile, every policy without UB). -/
theorem arithBuild_wellArity (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : moduleAstWLang P arithBuild arithIx pol ⊆ {x | AST.WellArity x} :=
  moduleAstWLang_wellArity ha hw

/-- An `s64` and a `u32` payload, with one value left over (a child handle). -/
theorem ofVals_example :
    (ofVals? [.s64, .u32] [Val.i64 5, Val.i32 7, Val.i32 9]).map
      (fun p => ((p.1.1 : Int64).toBitVec, (p.1.2.1 : UInt32).toBitVec, p.2)) =
      some (5, 7, [Val.i32 9]) := by
  decide +kernel

/-- `bool` payloads: nonzero is true. -/
theorem ofVals_bool :
    (ofVals? [.bool, .bool] [Val.i32 0, Val.i32 2]).map
      (fun p => ((p.1.1 : Bool), (p.1.2.1 : Bool))) =
      some (false, true) := by
  decide +kernel

/-- Memory payloads are not decoded. -/
theorem ofVals_string : (ofVals? [.string] [Val.i32 0]).isNone = true := by decide +kernel

end Silmaril.Wasm.Game.HandleAccept.Ast.Examples
