module

public import Silmaril.Wasm.Abstract.Body.Defs
public import Silmaril.Wasm.Binaryen.Interp

/-!
# Folded Wasm bodies over the actual store (F3, primitives)

The abstract body of a folded Binaryen tree (`Silmaril.Wasm.Binaryen.BExpr`)
whose module state is the **actual Core 3.0 store** (`Store H`, memories,
globals, tables, functions) and whose activation state is the actual Core frame
(`Frame`: locals and module instance), threaded through the object.

**Primitives are lifted, not reimplemented.** Every flat instruction is
`flatK i`: it reads the store, runs silmaril's native interpreter step
`Binaryen.evalFlat` on it, and writes the resulting store back (`ofEval`). The
three outcomes of `evalFlat` are read off exactly: a result is returned with the
new store, `.trap` is the `BodyM` trap effect, and `none` (an operand or index
the interpreter does not accept) is explicit silent divergence, `stuck`; on
typed code typed progress rules `stuck` out. So the store effects of
`global.get/set` and of integer `load`/`store` are exactly those of `evalFlat`,
which is adequate for Core 3.0 (`Binaryen.NativeProfile`).

**Structure.** `den`/`denList` follow the native interpreter `Binaryen.run`
constructor by constructor: operands then the operator (Kleisli composition),
`block`/`if` compose with the label-exit copairing `blockK`, and `loop` is the
Elgot iteration of its body with `br 0` the continuing summand (`loopK`); as in
the interpreter, each iteration reads the block type's arity in its frame.
Exits are the interpreter's flows (`Flow`): fallthrough with the stack, a
branch, a return, a thrown exception address.

**Not covered here.** Calls (`call` is `stuck`; F4), `try_table` (`stuck`;
F5), and block types with parameters beyond what `arity` gives.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.StoreBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core

variable {E : Sig.{0}} {H : Type}

/-- The module state: the actual store. -/
abbrev St (H : Type) : Type 1 := ULift.{1} (Store H)

/-- Bodies over the actual store; traps carry no payload. -/
abbrev M (E : Sig.{0}) (H : Type) : Type 1 → Type 1 := BodyM E (St H) PUnit.{2}

/-- The result object: the frame and the flow. -/
abbrev Res : Type 1 := ULift.{1} (Frame × Flow)

/-- No run: silent divergence. -/
noncomputable def stuck {X : Type 1} : M E H X :=
  fun _ => ExceptT.mk Silmaril.Elgot.ITree.diverge

/-- An interpreter step outcome as a body: the new store is written, a trap is
the trap effect, no outcome is `stuck`. -/
noncomputable def ofEval : Option (Store H × Frame × Flow) → M E H Res
  | some (_, _, .trap) => trap ⟨⟩
  | some (s', f', fl) => setState ⟨s'⟩ >>= fun _ => pure ⟨(f', fl)⟩
  | none => stuck

/-- **A flat instruction, lifted.** `evalFlat` on the current store. -/
noncomputable def flatK (i : Instr) (f : Frame) (stk : List Val) : M E H Res :=
  getState >>= fun s => ofEval (evalFlat s.down f stk i)

/-- Continue with `k` after a fallthrough; other flows pass. -/
noncomputable def thenK (k : Frame → List Val → M E H Res) : Res → M E H Res
  | ⟨(f, .normal stk)⟩ => k f stk
  | r => pure r

/-- The exits of a `block`/`if` body run on the stack `stk` with arity `(np, nr)`:
fallthrough and `br 0` complete with the results over the passive stack, other
labels shift. -/
noncomputable def blockK (np nr : Nat) (stk : List Val) : Res → M E H Res
  | ⟨(f, .normal vs)⟩ => pure ⟨(f, .normal (vs.take nr ++ stk.drop np))⟩
  | ⟨(f, .brk 0 vs)⟩ => pure ⟨(f, .normal (vs.take nr ++ stk.drop np))⟩
  | ⟨(f, .brk (k + 1) vs)⟩ => pure ⟨(f, .brk k vs)⟩
  | r => pure r

/-- The exits of a `loop` body: `br 0` continues (right) with the parameters over
the passive stack, the rest leave (left). -/
noncomputable def loopK (np nr : Nat) (stk : List Val) :
    Res → M E H (Res ⊕ ULift.{1} (Frame × List Val))
  | ⟨(f, .normal vs)⟩ => pure (.inl ⟨(f, .normal (vs.take nr ++ stk.drop np))⟩)
  | ⟨(f, .brk 0 vs)⟩ => pure (.inr ⟨(f, vs.take np ++ stk.drop np)⟩)
  | ⟨(f, .brk (k + 1) vs)⟩ => pure (.inl ⟨(f, .brk k vs)⟩)
  | r => pure (.inl r)

/-- A direct call (not a primitive: F4). -/
def isCall : Instr → Bool
  | .call _ => true
  | _ => false

mutual

/-- The abstract body of a folded tree, on a frame and a top-first stack. -/
noncomputable def den : BExpr → Frame → List Val → M E H Res
  | .op i args, f, stk => if isCall i then stuck else denList args f stk >>= thenK (flatK i)
  | .block bt body, f, stk =>
    match arity f bt with
    | some (np, nr) => denList body f (stk.take np) >>= blockK np nr stk
    | none => stuck
  | .loop bt body, f, stk =>
    Silmaril.Elgot.iter (fun c : ULift.{1} (Frame × List Val) =>
      match arity c.down.1 bt with
      | some (np, nr) => denList body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
      | none => stuck) ⟨(f, stk)⟩
  | .if_ bt c t el, f, stk =>
    denList c f stk >>= fun r =>
      match r with
      | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          (if b then denList t f₁ (stk₁.take np) else denList el f₁ (stk₁.take np)) >>=
            blockK np nr stk₁
        | _, _ => stuck
      | ⟨(_, .normal [])⟩ => stuck
      | r => pure r
  | .tryTable .., _, _ => stuck

/-- The abstract body of a list of trees, left to right. -/
noncomputable def denList : List BExpr → Frame → List Val → M E H Res
  | [], f, stk => pure ⟨(f, .normal stk)⟩
  | e :: es, f, stk => den e f stk >>= thenK (denList es)

end

/-- The body of a loop's iteration. -/
noncomputable def loopBody (bt : BlockType) (body : List BExpr) :
    ULift.{1} (Frame × List Val) → M E H (Res ⊕ ULift.{1} (Frame × List Val)) :=
  fun c =>
    match arity c.down.1 bt with
    | some (np, nr) => denList body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
    | none => stuck

mutual

/-- No `call` (F4) and no `try_table` (F5) in the tree. -/
def callFree : BExpr → Bool
  | .op i args => !isCall i && callFreeL args
  | .block _ body => callFreeL body
  | .loop _ body => callFreeL body
  | .if_ _ c t e => callFreeL c && callFreeL t && callFreeL e
  | .tryTable .. => false

/-- `callFree` on every tree of a list. -/
def callFreeL : List BExpr → Bool
  | [] => true
  | e :: es => callFree e && callFreeL es

end

/-- The interaction tree of an interpreter step outcome from the store it ran on. -/
def evalTree (o : Option (Store H × Frame × Flow)) :
    Silmaril.Elgot.ITree.Tree (SigEv E) (Except PUnit.{2} (Res × St H)) :=
  match o with
  | some (_, _, .trap) => Silmaril.Elgot.ITree.ret (.error ⟨⟩)
  | some (s', f', fl) => Silmaril.Elgot.ITree.ret (.ok (⟨(f', fl)⟩, ⟨s'⟩))
  | none => Silmaril.Elgot.ITree.diverge

/-! ## Invocations -/

/-- The call outcome of a function body: fallthrough, `return` and `br 0`
deliver the last `nr` values (bottom-first), a thrown exception passes, other
branches are stuck. As `Binaryen.invokeRun`. -/
noncomputable def invokeK (nr : Nat) : Res → M E H (ULift.{1} Flow)
  | ⟨(_, .normal ws)⟩ => pure ⟨.normal (ws.take nr).reverse⟩
  | ⟨(_, .ret ws)⟩ => pure ⟨.normal (ws.take nr).reverse⟩
  | ⟨(_, .brk 0 ws)⟩ => pure ⟨.normal (ws.take nr).reverse⟩
  | ⟨(_, .throw x)⟩ => pure ⟨.throw x⟩
  | _ => stuck

/-- **The abstract invocation** of the function at address `a` of the current
store on bottom-first arguments `vs`: its body's abstract body in the callee
frame (`Frame.forCall`), then the call outcome. -/
noncomputable def denInvoke (a : Nat) (vs : List Val) : M E H (ULift.{1} Flow) :=
  getState >>= fun s =>
    match s.down.funcs[a]? with
    | some fi =>
      match fi.code, Validation.DefType.funcType? fi.type with
      | .wasm fn, some (_, rs) =>
        denList (liftInstrs fn.body) (Frame.forCall fi.module vs fn.locals) [] >>=
          invokeK rs.length
      | _, _ => stuck
    | none => stuck

/-- The interaction tree of an invocation outcome. -/
def invTree (o : Option (Store H × Flow)) :
    Silmaril.Elgot.ITree.Tree (SigEv E) (Except PUnit.{2} (ULift.{1} Flow × St H)) :=
  match o with
  | some (_, .trap) => Silmaril.Elgot.ITree.ret (.error ⟨⟩)
  | some (s', fl) => Silmaril.Elgot.ITree.ret (.ok (⟨fl⟩, ⟨s'⟩))
  | none => Silmaril.Elgot.ITree.diverge

/-- The function at `a` is Wasm code with a call-free body (the F3 scope). -/
def CallFreeAt (s : Store H) (a : Nat) : Prop :=
  ∀ fi fn, s.funcs[a]? = some fi → fi.code = .wasm fn → callFreeL (liftInstrs fn.body) = true

end Silmaril.Wasm.Abstract.StoreBody
