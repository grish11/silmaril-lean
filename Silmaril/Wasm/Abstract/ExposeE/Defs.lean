module

public import Silmaril.Wasm.Abstract.CallXE.Defs

/-!
# The exposed body of the relation with exceptions (F5, exposure)

`denXE`/`denListXE` extend `CallX`'s exposed body `denX`/`denListX` by the exception forms,
in the same monad (`M (CallSig H) H`, every call form a call event):

* an exception is a **value** of the result object: a `Res` with flow `.throw a`, `a` the
  exception's address in the store; it passes through operator sequencing (`thenK`), blocks,
  loops and conditionals as every non-normal flow does;
* `throw x` resolves its tag as `EvalOXE.throw` does (`resolveThrow`, classically: the unique
  resolution, or none), allocates the exception with the tag's fields (bottom first) and
  returns the throw (`throwEv`);
* `throw_ref` traps on null and rethrows an exception reference (`throwRefEv`);
* `try_table bt cs body` runs its body as a block; a thrown exception is resolved by the
  first-match handler resolution `Cfg.Region.Catches` (`resolveCatch`, `tryK`): a match is a
  branch to the clause's label from outside the block, no match rethrows.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.ExposeE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX
open Silmaril.Wasm.Abstract.Body (getState setState trap)

variable {H : Type}

/-- The resolution of `throw x` on a stack (top first): the tag's address and its field
count, which the stack covers. -/
def ThrowResS (s : Store H) (f : Frame) (x : TagIdx) (stk : List Val) : Nat × Nat → Prop :=
  fun p => ∃ (ti : TagInst) (ts : Validation.Ty (.list .val)), s.tag? f x = some (p.1, ti) ∧
    Validation.Expand ti.type (.func ts .nil) ∧ ts.length = p.2 ∧ p.2 ≤ stk.length

open Classical in
/-- The resolution of `throw x` on a stack, if any. -/
noncomputable def resolveThrow (s : Store H) (f : Frame) (x : TagIdx) (stk : List Val) :
    Option (Nat × Nat) :=
  if h : ∃ p, ThrowResS s f x stk p then some (Classical.choose h) else none

/-- `throw x`, exposed: the exception is allocated with the tag's fields (bottom first) and
thrown, at its address. -/
noncomputable def throwEv (x : TagIdx) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  getState >>= fun s =>
    match resolveThrow s.down f x stk with
    | some (ta, n) =>
      setState ⟨s.down.addExn ⟨ta, (stk.take n).reverse⟩⟩ >>= fun _ =>
        pure ⟨(f, .throw s.down.exns.length)⟩
    | none => stuck

/-- `throw_ref`, exposed: null traps, an exception reference is thrown again. -/
noncomputable def throwRefEv (f : Frame) : List Val → M (CallSig H) H Res
  | .ref .null :: _ => trap ⟨⟩
  | .ref (.exn a) :: _ => pure ⟨(f, .throw a)⟩
  | _ => stuck

open Classical in
/-- The handler resolution of the exception `a` by the clauses `cs` (`Cfg.Region.Catches`,
total and unique). -/
noncomputable def resolveCatch (s : Store H) (f : Frame) (a : Nat) (cs : List Catch) :
    Option (Option (List Val × LabelIdx)) :=
  if h : ∃ r, Cfg.Region.Catches s f a cs r then some (Classical.choose h) else none

/-- The exits of a `try_table` body run on the stack `stk` with arity `(np, nr)`: a thrown
exception is resolved by the clauses `cs` (a branch from outside the block with the clause's
values over the passive stack, or a rethrow); every other exit is a block's (`blockK`). -/
noncomputable def tryK (np nr : Nat) (stk : List Val) (cs : List Catch) :
    Res → M (CallSig H) H Res
  | ⟨(f, .throw a)⟩ =>
    getState >>= fun s =>
      match resolveCatch s.down f a cs with
      | some (some (us, l)) => pure ⟨(f, .brk l.toNat (us.reverse ++ stk.drop np))⟩
      | some none => pure ⟨(f, .throw a)⟩
      | none => stuck
  | r => blockK np nr stk r

/-- An operator, exposed: the exception operators, then `CallX`'s operators. -/
noncomputable def opCXE (i : Instr) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  match i with
  | .throw x => throwEv x f stk
  | .throwRef => throwRefEv f stk
  | _ => opCX i f stk

mutual

/-- The exposed abstract body of a folded tree, with exceptions. -/
noncomputable def denXE : BExpr → Frame → List Val → M (CallSig H) H Res
  | .op i args, f, stk => denListXE args f stk >>= thenK (opCXE i)
  | .block bt body, f, stk =>
    match arity f bt with
    | some (np, nr) => denListXE body f (stk.take np) >>= blockK np nr stk
    | none => stuck
  | .loop bt body, f, stk =>
    Silmaril.Elgot.iter (fun c : ULift.{1} (Frame × List Val) =>
      match arity c.down.1 bt with
      | some (np, nr) => denListXE body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
      | none => stuck) ⟨(f, stk)⟩
  | .if_ bt c t el, f, stk =>
    denListXE c f stk >>= fun r =>
      match r with
      | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          (if b then denListXE t f₁ (stk₁.take np) else denListXE el f₁ (stk₁.take np)) >>=
            blockK np nr stk₁
        | _, _ => stuck
      | ⟨(_, .normal [])⟩ => stuck
      | r => pure r
  | .tryTable bt cs body, f, stk =>
    match arity f bt with
    | some (np, nr) => denListXE body f (stk.take np) >>= tryK np nr stk cs
    | none => stuck

/-- The exposed abstract body of a list of trees, with exceptions. -/
noncomputable def denListXE : List BExpr → Frame → List Val → M (CallSig H) H Res
  | [], f, stk => pure ⟨(f, .normal stk)⟩
  | e :: es, f, stk => denXE e f stk >>= thenK (denListXE es)

end

/-- The body of one loop iteration, exposed, with exceptions. -/
noncomputable def loopBodyXE (bt : BlockType) (body : List BExpr) :
    ULift.{1} (Frame × List Val) → M (CallSig H) H (Res ⊕ ULift.{1} (Frame × List Val)) :=
  fun c =>
    match arity c.down.1 bt with
    | some (np, nr) => denListXE body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
    | none => stuck

end Silmaril.Wasm.Abstract.ExposeE
