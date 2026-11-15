module

public import Silmaril.Wasm.Abstract.ExposeP.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Wasm.Interp.EHExt.Thms
public import Silmaril.Wasm.Interp.PProgress.Thms

/-!
# The structure of the exact F5 denotation, and its typed subcategory (F7)

`ExposeP.denXP`/`denListXP` are the exact `BodyM` denotation of the canonical F5 semantics
(`CallXP.EvalOXP`; exactness `ExposeP.evalOXP_iff`). This topic reads them as morphisms of
the Kleisli category of `BodyM` and names the operations on morphisms that the syntax is
sent to.

**Morphisms.** A body on configurations is a `PHom H Cfg ResP`: from a frame and a top-first
stack (`Cfg`) to a body result (`ExposeP.ResP`: a frame with a flow or a pending tail call), in
`M (CallSig H) H`, every ordinary call a call event. `denL es` and `denT e` are the denotations
of a sequence and of a tree.

**Operations.**

* `idP`, `seqP`: the exit-aware Kleisli category. `seqP g₁ g₂` continues with `g₂` after a
  fallthrough of `g₁` (`ExposeP.thenKP`); a branch, a return, a trap, an exception and a
  pending tail call pass.
* `opP i g`: the operands `g`, then the operator `i` (`ExposeP.opCXP`).
* `blockP`, `ifP`/`ifKP`, `tryP`: the body on the parameters, then the exit copairing
  (`blockKP`, `tryKP` resolving a thrown exception by the clauses).
* `loopStepP`, `loopP`: a loop is the Elgot iteration of its step, `br 0` the continuing
  summand (`loopKP`).
* `whiskP rest`, `trimP labels ret`: the stack tensor. `whiskP rest` appends a passive stack
  `rest` below a fallthrough; `trimP` reads a branch and a return at the arity of their
  target, the only part of their stack their target reads (`blockKP`, `loopKP` and the frame
  take that many values). `wcfg rest` appends `rest` below a configuration's stack.
* `Lands P x`: the computation `x` factors through the subtype of `P` (every result satisfies
  `P`); `GoodR env o` is the result invariant of code checked in `env` ending at `o`;
  `LoopInv`, `BrkOk`: the invariant of a loop's states and what its body ensures on `br 0`.
* `stackPure`: code whose stack effect is static (no call form, tail call, `throw` or
  `try_table`): the fragment on which the stack tensor holds as an equation of computations
  (`ExposePStruct.Thms` states exactly where it fails beyond it).

**The typed subcategory.** The objects are interfaces `Iface`: the static context `Env`
(module instance, number of locals, function result arity, label arities) and a stack height.
The store is a fixed context `Ctx`: the tag instances and the functions, every function passing
the exception checker (`StoreChkE (ehExt tags)`); a run's store `s` agrees with it
(`Ctx.Good`: `s.funcs = F`, `TagsOk tags s`). The effects are those of `M (CallSig H) H`: call
events of `CallSig H`, the trap, and as values exceptions and pending tail calls.

`Mor Γ I o es`: the code `es` passes the arity check from `I` and ends at `o`: `some h'`
falls through at height `h'` (a morphism `I ⟶ ⟨I.env, h'⟩`, `Hom`), `none` never falls through
(a branch, `return`, `unreachable`, a tail call, `throw`: a morphism to the never-falls-through
target, which composition absorbs). `DenMor Γ I o` is the image: the denotations of such code.

**Scope of the fragment.** The checker and interpreter (`Interp.flatEff`, `Interp.flatChkE`,
`Binaryen.evalFlat`) accept: integer constants and unary, test, binary and comparison operators;
`nop`, `drop`, `select`; `local.get/set/tee`, `global.get/set`; unpacked integer `load`/`store`
(no `memarg` packing); `unreachable`, `block`, `loop`, `if`, `br`, `br_if`, `br_table`,
`return`; `call`, `call_indirect`, `call_ref`, `return_call`, `return_call_indirect`,
`return_call_ref`; `throw`, `throw_ref`, `try_table`. Every other instruction is rejected by the
checker (`flatEff` is `none`): float constants and float operators, vector instructions,
conversions, reinterpretations and extensions, reference instructions (`ref.null`, `ref.func`,
`ref.is_null`, `ref.as_non_null`, `br_on_null`, …), table instructions, `memory.size`,
`memory.grow`, bulk memory, packed loads and stores, the GC and the legacy exception
instructions. So this is **not** full Wasm: it is the checked integer/control/call/exception
fragment of the native interpreter.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## Morphisms and operations -/

/-- A configuration: the frame and the top-first stack. -/
abbrev Cfg : Type 1 := ULift.{1} (Frame × List Val)

/-- Bodies of the exposed semantics from `A` to `B` (`Body.Hom` at the call events). -/
abbrev PHom (H : Type) (A B : Type 1) : Type 1 := Body.Hom (CallSig H) (St H) PUnit.{2} A B

/-- The denotation of a sequence of trees, as a morphism. -/
noncomputable def denL (es : List BExpr) : PHom H Cfg ResP := fun c => denListXP es c.down.1 c.down.2

/-- The denotation of a tree, as a morphism. -/
noncomputable def denT (e : BExpr) : PHom H Cfg ResP := fun c => denXP e c.down.1 c.down.2

/-- The identity: fall through on the configuration. -/
noncomputable def idP : PHom H Cfg ResP := fun c => pure ⟨(c.down.1, .flow (.normal c.down.2))⟩

/-- Continue with `g` after a fallthrough. -/
noncomputable def contP (g : PHom H Cfg ResP) : ResP → M (CallSig H) H ResP :=
  thenKP fun f stk => g ⟨(f, stk)⟩

/-- **Exit-aware Kleisli composition**: `g₂` after a fallthrough of `g₁`. -/
noncomputable def seqP (g₁ g₂ : PHom H Cfg ResP) : PHom H Cfg ResP := fun c => g₁ c >>= contP g₂

/-- An operator after its operands `g`. -/
noncomputable def opP (i : Instr) (g : PHom H Cfg ResP) : PHom H Cfg ResP :=
  fun c => g c >>= thenKP (opCXP i)

/-- A `block`: the body on the parameters, then the exit copairing `blockKP`. -/
noncomputable def blockP (bt : BlockType) (g : PHom H Cfg ResP) : PHom H Cfg ResP := fun c =>
  match arity c.down.1 bt with
  | some (np, nr) => g ⟨(c.down.1, c.down.2.take np)⟩ >>= blockKP np nr c.down.2
  | none => stuck

/-- One step of a `loop`: the body on the parameters, then `loopKP` (`br 0` continues). -/
noncomputable def loopStepP (bt : BlockType) (g : PHom H Cfg ResP) : PHom H Cfg (ResP ⊕ Cfg) :=
  fun c =>
    match arity c.down.1 bt with
    | some (np, nr) => g ⟨(c.down.1, c.down.2.take np)⟩ >>= loopKP np nr c.down.2
    | none => stuck

/-- A `loop`: the Elgot iteration of its step. -/
noncomputable def loopP (bt : BlockType) (g : PHom H Cfg ResP) : PHom H Cfg ResP :=
  Silmaril.Elgot.iter (loopStepP bt g)

/-- The arms of an `if` after its condition's result. -/
noncomputable def ifKP (bt : BlockType) (gt ge : PHom H Cfg ResP) :
    ResP → M (CallSig H) H ResP
  | ⟨(f₁, .flow (.normal (cv :: stk₁)))⟩ =>
    match truthy cv, arity f₁ bt with
    | some b, some (np, nr) =>
      (if b then gt ⟨(f₁, stk₁.take np)⟩ else ge ⟨(f₁, stk₁.take np)⟩) >>= blockKP np nr stk₁
    | _, _ => stuck
  | ⟨(_, .flow (.normal []))⟩ => stuck
  | r => pure r

/-- An `if`: the condition, then an arm and the exit copairing. -/
noncomputable def ifP (bt : BlockType) (gc gt ge : PHom H Cfg ResP) : PHom H Cfg ResP :=
  fun c => gc c >>= ifKP bt gt ge

/-- A `try_table`: the body on the parameters, then `tryKP` (the clauses `cs` on a thrown
exception, the block's exits otherwise). -/
noncomputable def tryP (bt : BlockType) (cs : List Catch) (g : PHom H Cfg ResP) :
    PHom H Cfg ResP := fun c =>
  match arity c.down.1 bt with
  | some (np, nr) => g ⟨(c.down.1, c.down.2.take np)⟩ >>= tryKP np nr c.down.2 cs
  | none => stuck

/-! ## The stack tensor -/

/-- Append the passive stack `rest` below a fallthrough; every other result is unchanged. -/
def whiskP (rest : List Val) : ResP → ResP
  | ⟨(f, .flow (.normal vs))⟩ => ⟨(f, .flow (.normal (vs ++ rest)))⟩
  | r => r

/-- Read a branch at the arity of its label and a return at the result arity `ret`: the values
the target takes. Every other result is unchanged. -/
def trimP (labels : List Nat) (ret : Nat) : ResP → ResP
  | ⟨(f, .flow (.brk l vs))⟩ =>
    ⟨(f, .flow (.brk l (match labels[l]? with
      | some n => vs.take n
      | none => vs)))⟩
  | ⟨(f, .flow (.ret vs))⟩ => ⟨(f, .flow (.ret (vs.take ret)))⟩
  | r => r

/-- A body read through `trimP`. -/
noncomputable def obsP (labels : List Nat) (ret : Nat) (x : M (CallSig H) H ResP) :
    M (CallSig H) H ResP :=
  x >>= fun r => pure (trimP labels ret r)

/-! ## The typed subcategory -/

/-- The fixed store context: tag instances and functions, every function passing the
exception checker. -/
structure Ctx (H : Type) where
  /-- The tag instances (they do not change at run time). -/
  tags : List TagInst
  /-- The store's functions. -/
  funcs : List (FuncInst H)
  /-- Every function passes the arity check with exceptions in its own module. -/
  storeChk : StoreChkE (ehExt tags) funcs

/-- A run's store agrees with the context: its functions, and the tag invariants. -/
def Ctx.Good (Γ : Ctx H) (s : Store H) : Prop := s.funcs = Γ.funcs ∧ TagsOk Γ.tags s

/-- The static context of code: module instance, local count, function result arity and label
arities (innermost first). -/
structure Env where
  /-- The module instance. -/
  mi : ModuleInst
  /-- The number of locals (parameters included). -/
  nl : Nat
  /-- The function's result arity. -/
  ret : Nat
  /-- The label arities, innermost first. -/
  labels : List Nat

/-- An interface: a static context and a stack height. -/
structure Iface where
  /-- The static context. -/
  env : Env
  /-- The stack height. -/
  h : Nat

/-- The arity check in a context and an environment. -/
def chkIn (Γ : Ctx H) (env : Env) : Option Nat → List BExpr → Option (Option Nat) :=
  chkE (ehExt Γ.tags) Γ.funcs env.mi env.nl env.ret env.labels

/-- **Typed code** from the interface `I` ending at `o`: `some h'` falls through at height
`h'`, `none` never falls through. -/
def Mor (Γ : Ctx H) (I : Iface) (o : Option Nat) (es : List BExpr) : Prop :=
  chkIn Γ I.env (some I.h) es = some o

/-- **The morphisms `I ⟶ J`**: code typed from `I` falling through at `J`'s height, in `J`'s
static context, which is `I`'s. -/
def Hom (Γ : Ctx H) (I J : Iface) (es : List BExpr) : Prop := I.env = J.env ∧ Mor Γ I (some J.h) es

/-- The block body's environment: the label `n` pushed. -/
def Env.push (env : Env) (n : Nat) : Env := { env with labels := n :: env.labels }

/-- **The image of typed code** under the denotation. -/
def DenMor (Γ : Ctx H) (I : Iface) (o : Option Nat) : Set (PHom H Cfg ResP) :=
  {g | ∃ es, Mor Γ I o es ∧ g = denL es}

/-- The interface of a typed problem's configuration (`Interp.TypedP`) in the store `s`. -/
def ifaceOf (f : Frame) (ret : Nat) (labels : List Nat) (stk : List Val) : Iface :=
  ⟨⟨f.module, f.locals.length, ret, labels⟩, stk.length⟩

/-! ## Stack-polymorphic code and result invariants -/

/-- Append the passive stack `rest` below a configuration's stack. -/
def wcfg (rest : List Val) (c : Cfg) : Cfg := ⟨(c.down.1, c.down.2 ++ rest)⟩

/-- A computation lands in `P`: it factors through the subtype of `P`. -/
def Lands {X : Type 1} (P : X → Prop) (x : M (CallSig H) H X) : Prop :=
  ∃ y : M (CallSig H) H {a // P a}, x = Subtype.val <$> y

/-- The result invariant of code checked in `env` ending at `o`: a fallthrough is at height
`o` in a frame of the module instance; a branch carries at least its label's arity and a return
at least the result arity, in such a frame. Traps, exceptions and pending tail calls are
unconstrained. -/
def GoodR (env : Env) (o : Option Nat) : ResP → Prop
  | ⟨(f, .flow (.normal vs))⟩ => f.module = env.mi ∧ o = some vs.length
  | ⟨(f, .flow (.brk l vs))⟩ => f.module = env.mi ∧ ∃ n, env.labels[l]? = some n ∧ n ≤ vs.length
  | ⟨(f, .flow (.ret vs))⟩ => f.module = env.mi ∧ env.ret ≤ vs.length
  | _ => True

/-- The loop invariant of the stack tensor: the frame satisfies `Q`, the parameters are present
and the block type has the arity `(np, nr)` in the frame. -/
def LoopInv (Q : Frame → Prop) (bt : BlockType) (np nr : Nat) (c : Cfg) : Prop :=
  Q c.down.1 ∧ arity c.down.1 bt = some (np, nr) ∧ np ≤ c.down.2.length

/-- What a loop body must ensure of its `br 0`: the parameters are carried, and the frame
keeps the block type's arity. -/
def BrkOk (Q : Frame → Prop) (bt : BlockType) (np nr : Nat) (r : ResP) : Prop :=
  ∀ f vs, r = ⟨(f, .flow (.brk 0 vs))⟩ → Q f ∧ arity f bt = some (np, nr) ∧ np ≤ vs.length

/-- The operators whose stack effect does not depend on the store or on call answers: every
operator but the call forms (`call`, `call_indirect`, `call_ref`), the tail calls and `throw`. -/
def instrStackPure : Instr → Bool
  | .call _ | .callIndirect _ _ | .callRef _ | .returnCall _ | .returnCallIndirect _ _
  | .returnCallRef _ | .throw _ => false
  | _ => true

mutual
/-- Stack-pure code: stack-pure operators, `block`, `loop` and `if`; no `try_table`. -/
def stackPure : BExpr → Bool
  | .op i args => instrStackPure i && stackPureL args
  | .block _ body => stackPureL body
  | .loop _ body => stackPureL body
  | .if_ _ c t e => stackPureL c && stackPureL t && stackPureL e
  | .tryTable .. => false

/-- Stack-pure sequences. -/
def stackPureL : List BExpr → Bool
  | [] => true
  | e :: es => stackPure e && stackPureL es
end

end Silmaril.Wasm.Abstract.ExposePStruct
