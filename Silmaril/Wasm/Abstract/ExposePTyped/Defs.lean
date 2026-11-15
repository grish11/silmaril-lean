module

public import Silmaril.Wasm.Abstract.ExposePStruct.Defs

/-!
# The Core-typed subcategory of the exact F5 denotation, and the answered stack tensor (F7)

`ExposePStruct` (#529) reads the exact denotation `ExposeP.denListXP` of the canonical F5
semantics as a category whose morphisms are **checked** code (`ExposePStruct.Mor`: the arity
check `chkE (ehExt tags)` from an interface `Iface`, stack heights and label arities). This topic
refines it in two directions.

**The typed subcategory.** An object `TIface` is a Core 3.0 validation context `C`
(`Validation.Context`: the module's types, functions, tables, tags and globals, the locals with
their initialisation state, the label result types, innermost first, and the return type), the
module instance `mi` the code runs in, and a stack of Core value types `ts`, **bottom first** (as
Core's instruction types; a run's stack is top first, so a stack `stk` has the types
`stk.reverse`). It forgets (`TIface.forget`) to #529's interface: the local count, the result
arity, the label arities and the stack height.

`TMor Γ I J ft es` (typed code): the lowered code `Binaryen.BExpr.lowerList es` has the Core
instruction type `I.ts →_{xs} J.ts` in `I.C` (`Validation.InstrsOk`, every initialised local in
bounds), `J`'s context is `I.C` with the locals `xs` initialised and `J`'s instance is `I`'s,
**and** `es` passes #529's arity check from `I.forget`, falling through at `J`'s height (`ft =
true`, `THom`) or never falling through (`ft = false`, `TStop`: a branch, `return`,
`unreachable`, a tail call, `throw`; Core types such code at any `J.ts`). Both halves are what a
typed problem (`Interp.TypedP`) asks of its code: the check, and Core typing in context. The
forgetful map to #529's checked category is the identity on code (`ftOut` reads `ft` as #529's
`Option Nat` end).

`Realizes Γ I s f stk`: a run state the typed interface describes: the store agrees with the
context `Γ` and is Core-typed (`StoreOk`), the frame is Core-typed (`FrameOk`) in the frame part
of `I.C` (`I.C` is that context with `I.C`'s labels and return type), runs in `I.mi`, the return
and label types are closed (valid in the empty context), and the stack has the types `I.ts`. At
every such state typed code is a typed problem (`ExposePTyped.Thms.tmor_typedP`).

**The answered stack tensor.** #529 proves the stack tensor (`whiskP`, read through `trimP`) as an
equation of `BodyM` computations for stack-pure code only: a call's answer is an arbitrary
`Store H × Flow` of `CallSig H`, so an answer with fewer values than the callee's results leaves
the stack below the checked height. With an oracle `C` that **respects arities** (`ArityResp`:
from a store agreeing with `Γ`, its answers keep agreeing with `Γ` — the functions and the tag
invariants `TagsOk` — and return at least the callee's declared result count), the tensor holds
for the answered semantics `CallXP.EvalOXP C` on **all** checked code, calls, tail calls,
`throw`, `throw_ref` and `try_table` included, relationally: `whiskO`, `trimO` and `GoodO` are
`whiskP`, `trimP` and `GoodR` on body results `POut`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposeP (ResP)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## The typed subcategory -/

/-- **A typed interface**: the module instance, a Core validation context and a stack of value
types, bottom first. -/
structure TIface where
  /-- The module instance the code runs in. -/
  mi : ModuleInst
  /-- The Core validation context: types, functions, tags, locals, labels, return type. -/
  C : Validation.Context
  /-- The value types of the stack, bottom first. -/
  ts : List Validation.CValType

/-- The static context #529's check reads off a typed interface. -/
def TIface.env (I : TIface) : Env :=
  ⟨I.mi, I.C.locals.length, (I.C.return_.getD []).length, I.C.labels.map List.length⟩

/-- **The forgetful map** to #529's interfaces. -/
def TIface.forget (I : TIface) : Iface := ⟨I.env, I.ts.length⟩

/-- The stack types are valid in the context. -/
def TIface.Ok (I : TIface) : Prop := Validation.ResultOk I.C.toTypeCtx I.ts

/-- #529's end of a morphism: falling through at height `n`, or never. -/
def ftOut : Bool → Nat → Option Nat
  | true, n => some n
  | false, _ => none

/-- **Typed code** from `I` to `J`: Core-typed from `I.ts` to `J.ts` in `I.C` (initialising the
locals `xs`, which `J.C` records), and checked from `I.forget`, falling through at `J`'s height
(`ft = true`) or never (`ft = false`). -/
def TMor (Γ : Ctx H) (I J : TIface) (ft : Bool) (es : List BExpr) : Prop :=
  J.mi = I.mi ∧ ∃ xs : List Nat, (∀ x ∈ xs, ∃ lt, I.C.locals[x]? = some lt) ∧
    J.C = I.C.initLocals xs ∧ Validation.InstrsOk I.C (BExpr.lowerList es) ⟨I.ts, xs, J.ts⟩ ∧
    Mor Γ I.forget (ftOut ft J.ts.length) es

/-- **The typed morphisms** `I ⟶ J`: typed code falling through at `J`. -/
abbrev THom (Γ : Ctx H) (I J : TIface) (es : List BExpr) : Prop := TMor Γ I J true es

/-- Typed code from `I` that never falls through, Core-typed at `J`'s stack. -/
abbrev TStop (Γ : Ctx H) (I J : TIface) (es : List BExpr) : Prop := TMor Γ I J false es

/-- **The image of typed code** under the denotation. -/
def DenTMor (Γ : Ctx H) (I J : TIface) (ft : Bool) : Set (PHom H Cfg ResP) :=
  {g | ∃ es, TMor Γ I J ft es ∧ g = denL es}

/-- **A run state the typed interface describes**: the store agrees with `Γ` and is Core-typed;
the frame is Core-typed in a context `C₀` that is `I.C` without its labels and return type, and
runs in `I.mi`; the return and label types are closed; the stack (top first) has the types
`I.ts` (bottom first). -/
def Realizes (Γ : Ctx H) (I : TIface) (s : Store H) (f : Frame) (stk : List Val) : Prop :=
  Γ.Good s ∧ StoreOk s ∧ f.module = I.mi ∧
    (∃ C₀, FrameOk s f C₀ ∧ I.C = { C₀ with labels := I.C.labels, return_ := I.C.return_ }) ∧
    (∃ R, I.C.return_ = some R ∧ Validation.ResultOk {} R) ∧
    (∀ L ∈ I.C.labels, Validation.ResultOk {} L) ∧
    List.Forall₂ (ValOk s) stk.reverse I.ts

/-! ## The answered stack tensor -/

/-- Append `rest` below a fallthrough's stack (`whiskP` on body results). -/
def whiskO (rest : List Val) : POut → POut
  | .flow (.normal vs) => .flow (.normal (vs ++ rest))
  | o => o

/-- Read a branch at its label's arity and a return at the result arity `ret` (`trimP` on body
results). -/
def trimO (labels : List Nat) (ret : Nat) : POut → POut
  | .flow (.brk l vs) => .flow (.brk l (match labels[l]? with
      | some n => vs.take n
      | none => vs))
  | .flow (.ret vs) => .flow (.ret (vs.take ret))
  | o => o

/-- The result invariant of code checked under labels of arities `labels` and result arity `ret`,
ending at `o` (`GoodR` on body results): a fallthrough at height `o`, a branch with at least its
label's arity, a return with at least the result arity. -/
def GoodO (labels : List Nat) (ret : Nat) (o : Option Nat) : POut → Prop
  | .flow (.normal vs) => o = some vs.length
  | .flow (.brk l vs) => ∃ n, labels[l]? = some n ∧ n ≤ vs.length
  | .flow (.ret vs) => ret ≤ vs.length
  | _ => True

/-- **An arity-respecting oracle** for the context `Γ`: from a store agreeing with `Γ`
(`Ctx.Good`: its functions and the tag invariants), every answer keeps agreeing with `Γ`, and
returns at least the callee's declared result count. -/
def ArityResp (Γ : Ctx H) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₂ : Store H) (a : Nat) (args : List Val) (fl : Flow), C s a args (s₂, fl) → Γ.Good s →
    Γ.Good s₂ ∧ ∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (vs : List Val),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
        fl.retVals = some vs → rs.length ≤ vs.length

end Silmaril.Wasm.Abstract.ExposePTyped
