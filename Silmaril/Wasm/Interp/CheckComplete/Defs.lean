module

public import Silmaril.Wasm.Interp.XProfile.Defs
public import Silmaril.Wasm.Interp.EHExt.Defs
public import Silmaril.Wasm.Validation.Instructions

/-!
# Relative completeness of the exception arity checker: definitions

The CFG, session and typed-category theorems assume the exception checker's acceptance
`Interp.StoreChkE (Interp.ehExt tags) s.funcs`. It is a fragment restriction, not a consequence
of validation: the checker (`Interp.chkE`, `Interp.flatChkE`) accepts only a fixed instruction
set (`XProfile.xInstr`). This topic proves the checker **complete relative to Core validation
and an explicit, computable instruction profile**:

* `supported1`, `supported`: the profile of a folded tree (sequence). Every flat instruction is in
  `XProfile.xInstr` (the native profile, the annotated `select`, the five call forms,
  `throw`/`throw_ref`), and `block`, `loop`, `if` and `try_table` recurse into their bodies.
  It is a `Bool`, decided by evaluation; it is checked on the whole tree, also on code after an
  instruction that never falls through (which the checker skips).
* `funcSupported`, `storeSupportedB`, `StoreSupported`: every Wasm function of a store has a
  supported body (`Binaryen.liftInstrs fn.body`, the tree the checker runs on).
* `CtxMatch tags F mi nl ret labels C`: the checker's parameters (tag instances, store
  functions, module instance, local count, result arity, label arities) read the validation
  context `C`: the same labels and return type (counted), locals below `nl`, the same type list,
  and the call and tag arities of `C`'s functions and tags.
* `floatBody`: `f32.const 0; drop`, a validated body outside the profile.

Theorems in `Silmaril.Wasm.Interp.CheckComplete.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.CheckComplete

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

variable {H : Type}

mutual
/-- **The checker's instruction profile** on a folded tree: flat instructions in
`XProfile.xInstr`, structured control recursively. -/
def supported1 : BExpr → Bool
  | .op i args => XProfile.xInstr i && supported args
  | .block _ b => supported b
  | .loop _ b => supported b
  | .if_ _ c t e => supported c && supported t && supported e
  | .tryTable _ _ b => supported b
/-- The checker's instruction profile on a sequence of trees. -/
def supported : List BExpr → Bool
  | [] => true
  | e :: es => supported1 e && supported es
end

/-- A function instance is in the profile: its Wasm body is (host functions are). -/
def funcSupported (fi : FuncInst H) : Bool :=
  match fi.code with
  | .wasm fn => supported (liftInstrs fn.body)
  | _ => true

/-- **Every function of a store is in the profile**, decided by evaluation. -/
def storeSupportedB (F : List (FuncInst H)) : Bool := F.all funcSupported

/-- **Every Wasm function of a store has a body in the profile.** -/
def StoreSupported (F : List (FuncInst H)) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (fn : Func), F[a]? = some fi → fi.code = .wasm fn →
    supported (liftInstrs fn.body) = true

/-- **The checker's parameters read the validation context `C`.** -/
structure CtxMatch (tags : List TagInst) (F : List (FuncInst H)) (mi : ModuleInst) (nl ret : Nat)
    (labels : List Nat) (C : Validation.Context) : Prop where
  /-- The label arities are those of `C`'s labels. -/
  labels : labels = C.labels.map List.length
  /-- The result arity is that of `C`'s return type, when it has one. -/
  ret : ∀ ts, C.return_ = some ts → ret = ts.length
  /-- Every local of `C` is below `nl`. -/
  locals : ∀ (x : Nat) (lt : Validation.LocalType), C.locals[x]? = some lt → x < nl
  /-- The module instance has `C`'s types. -/
  types : C.types = mi.types
  /-- Every function of `C` has its parameter and result counts in the store. -/
  funcs : ∀ (x : FuncIdx) (d : Validation.DefType) (ps rs : Validation.Ty (.list .val)),
    C.funcs[x.toNat]? = some d → Validation.Expand d (.func ps rs) →
      callArity F mi x = some (ps.toList.length, rs.toList.length)
  /-- Every tag of `C` has its field count in the tag instances. -/
  tags : ∀ (x : TagIdx) (d : Validation.DefType) (ts : Validation.Ty (.list .val)),
    C.tags[x.toNat]? = some d → Validation.Expand d (.func ts .nil) →
      tagFields tags mi x = some ts.toList.length

/-- **A validated body outside the profile**: `f32.const 0; drop`. -/
def floatBody : List Instr := [.floatConst .f32 0, .drop]

end Silmaril.Wasm.Interp.CheckComplete
