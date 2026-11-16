module

public import Silmaril.Wasm.Abstract.TypedFunctor.Defs
public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs

/-!
# The typed premonoidal Elgot functor of the supported checked fragment, in a world (definitions)

A **world** is a context `Γ : Ctx H`: the tag instances `Γ.tags`, the store's functions
`Γ.funcs`, and the checker's acceptance `Γ.storeChk : StoreChkE (ehExt Γ.tags) Γ.funcs` of every
one of them. The checker (`Interp.chkE`) covers the integer, control, call and exception fragment
only, so a world is a store whose code lies in the **supported checked fragment**; Core-valid Wasm
outside it (floats, vectors, references, tables, memory, conversions, GC) is not in any world.

**World states.** `WSt Γ I s f stk`: the store agrees with the world (`Ctx.Good`: its functions
are `Γ.funcs`, and the tag invariants hold), the frame runs in the interface's instance with its
local count, and the stack has the interface's height. These are the states the checker's result
invariant speaks of (`ExposePTyped.evalOXP_goodO`); every typed state (`ExposePTyped.Realizes`)
is one (`WorldFunctor.Thms.realizes_wst`).

**The domain.** `WObj Γ`: typed interfaces with valid stack types (`TIface.Ok`) coherent with the
world (`TypedCat.Coh`). Its morphisms (`WorldFunctor.Thms`) are #572's `TypedFunctor.TQ`: typed
checked code modulo the open interaction equivalence `OpEquivP`.

**The codomain.** `RObj Γ`: the same objects; `RHom Γ I J`: relations of answered runs
(`TypedCat.ORel`) **supported** on the world states of `I`, **landing** (fallthroughs) in the
world states of `J`, and **trap-closed** (a trap's store and frame are not observed: whenever a
trap is related, it is related with every store and frame). `resR P g` restricts `g` to sources
in `P`; `trapR g` forgets the store and frame of `g`'s traps (the trap of the exact `BodyM`
denotation carries neither).

**Answering.** `Ans C k`: the answered runs of an arrow `k` of the exit monad under the oracle
`C`: the finished paths of `ofK k` whose call events are answered by `C`, ending in the result
(`ansEnd`: a trap is the trap effect). This is `ExposeP`'s exactness read backwards.

**Iteration on relations.** `LStep H`: a relational iteration body (`inl o` leaves with the result
`o`, `inr vs` continues on the stack `vs`); `iterR F` its least iteration (finite runs: leave
after finitely many continues); `unfoldR F g` one unfolding, `F` then `g` on a continue.
`loopStepR C bt body`: the step of `loop bt body` under `C` (`br 0` continues on the label's
parameters, every other result leaves as the loop leaves).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.WorldFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.TypedFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.BodyTrace (Path PathEnd)

variable {H : Type}

/-! ## World states -/

/-- **A world state** of the interface `I`: the store agrees with the world, the frame runs in
`I`'s instance with `I`'s local count, and the stack has `I`'s height. -/
def WSt (Γ : Ctx H) (I : TIface) (s : Store H) (f : Frame) (stk : List Val) : Prop :=
  Γ.Good s ∧ f.module = I.mi ∧ f.locals.length = I.C.locals.length ∧ stk.length = I.ts.length

/-! ## The domain -/

/-- **The objects of the world category**: typed interfaces with valid stack types, coherent
with the world. -/
def WObj (Γ : Ctx H) : Type := {I : TIface // I.Ok ∧ Coh Γ I}

/-! ## The codomain -/

/-- Restrict a relation to the sources satisfying `P`. -/
def resR (P : Store H → Frame → List Val → Prop) (g : ORel H) : ORel H :=
  fun s f stk s' f' o => P s f stk ∧ g s f stk s' f' o

/-- Forget the store and frame of a trap: a trap is related with every store and frame as soon as
it is related with one. -/
def trapR (g : ORel H) : ORel H := fun s f stk s' f' o =>
  match o with
  | .flow .trap => ∃ s'' f'', g s f stk s'' f'' (.flow .trap)
  | o => g s f stk s' f' o

/-- The objects of the codomain: those of the world category. -/
def RObj (Γ : Ctx H) : Type := {I : TIface // I.Ok ∧ Coh Γ I}

/-- **The morphisms of the codomain**: relations of answered runs supported on the world states
of `I`, landing in the world states of `J`, trap-closed. -/
@[ext] structure RHom (Γ : Ctx H) (I J : TIface) where
  /-- The relation. -/
  rel : ORel H
  /-- Supported on the world states of `I`. -/
  supp : ∀ s f stk s' f' o, rel s f stk s' f' o → WSt Γ I s f stk
  /-- Fallthroughs land in the world states of `J`. -/
  lands : ∀ s f stk s' f' vs, rel s f stk s' f' (.flow (.normal vs)) → WSt Γ J s' f' vs
  /-- A trap does not record its store and frame. -/
  trap : ∀ s f stk s' f' s'' f'', rel s f stk s' f' (.flow .trap) → rel s f stk s'' f'' (.flow .trap)

/-! ## Answering -/

/-- The path end of a result: a trap is the trap effect (no store, no frame). -/
def ansEnd (s' : Store H) (f' : Frame) : POut → PathEnd (Except PUnit.{2} (ResP × St H))
  | .flow .trap => .val (.error ⟨⟩)
  | o => .val (.ok (⟨(f', o)⟩, ⟨s'⟩))

/-- **Answering an arrow of the exit monad by an oracle**: the finished paths of `ofK k` whose
call events `C` answers, ending in the result. -/
def Ans (C : Abstract.CallRel H) (k : Cfg → PX H Cfg) : ORel H := fun s f stk s' f' o =>
  ∃ cs, Answered C cs ∧ Path (((ofK k ⟨(f, stk)⟩ : M (CallSig H) H ResP).run ⟨s⟩).run) cs
    (ansEnd s' f' o)

/-! ## Iteration on relations -/

/-- A relational iteration body: `inl o` leaves with `o`, `inr vs` continues on the stack `vs`. -/
abbrev LStep (H : Type) : Type :=
  Store H → Frame → List Val → Store H → Frame → POut ⊕ List Val → Prop

/-- **The iteration** of a relational body: finitely many continues, then a leave. -/
inductive iterR (F : LStep H) : Store H → Frame → List Val → Store H → Frame → POut → Prop
  /-- Leave. -/
  | done {s : Store H} {f : Frame} {stk : List Val} {s' : Store H} {f' : Frame} {o : POut} :
      F s f stk s' f' (.inl o) → iterR F s f stk s' f' o
  /-- Continue, then iterate. -/
  | back {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {s' : Store H} {f' : Frame}
      {o : POut} : F s f stk s₁ f₁ (.inr vs) → iterR F s₁ f₁ vs s' f' o → iterR F s f stk s' f' o

/-- One unfolding: the body, then `g` on a continue. -/
def unfoldR (F : LStep H) (g : ORel H) : ORel H := fun s f stk s' f' o =>
  F s f stk s' f' (.inl o) ∨ ∃ s₁ f₁ vs, F s f stk s₁ f₁ (.inr vs) ∧ g s₁ f₁ vs s' f' o

/-- The exits of a loop body with block arities `np → nr` on the entry stack `stk`
(`ExposeP.loopKP`): a fallthrough leaves, `br 0` continues on the label's parameters, an outer
branch leaves one label further out, every other result leaves. -/
def loopOutR (np nr : Nat) (stk : List Val) : POut → POut ⊕ List Val
  | .flow (.normal vs) => .inl (.flow (.normal (vs.take nr ++ stk.drop np)))
  | .flow (.brk 0 vs) => .inr (vs.take np ++ stk.drop np)
  | .flow (.brk (k + 1) vs) => .inl (.flow (.brk k vs))
  | o => .inl o

/-- **The step of `loop bt body`** under the oracle `C`. -/
def loopStepR (C : Abstract.CallRel H) (bt : BlockType) (body : List BExpr) : LStep H :=
  fun s f stk s' f' x => ∃ np nr o, arity f bt = some (np, nr) ∧
    EvalOXP C s f (stk.take np) body (s', f', o) ∧ x = loopOutR np nr stk o

end Silmaril.Wasm.Abstract.WorldFunctor
