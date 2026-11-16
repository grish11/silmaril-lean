module

public import Silmaril.Wasm.Abstract.ExposePTyped.Defs

/-!
# The typed subcategory with its premises discharged, the typed frame rule and premonoidal strength

`ExposePTyped` (#540) defines the Core-typed subcategory of the exact F5 denotation (`TIface`,
`TMor`, `THom`, `TStop`) and the answered stack tensor (`evalOXP_tensor`, `tmor_tensor`) under an
arity-respecting oracle (`ArityResp`). Its closure lemmas take the checker's run-time arities as
premises (`callArity`, `typeArity`, `tagFields`, `clauseCount`/`catchOk`, and the instance's
types for block arities). This topic discharges them and studies the monoidal structure.

**Coherence** (`Coh Γ I`): the typed interface agrees with the store context `Γ`, as Core 3.0's
module-instance typing `ModuleInstOk` says of a store:

* the context's types are the instance's (`types`);
* the function `x` of the context, of type `d`, is at an address `a` of the instance whose store
  function `Γ.funcs[a]` has a valid closed type that is `d` or a subtype of `d` (`funcs`;
  `Externaddr_ok/func` with `Externaddr_ok/sub`);
* the tag `x` of the context, of type `d`, is at an address of the instance whose tag instance in
  `Γ.tags` has type `d` (`tags`; tag subtyping in the empty context is equality).

Every state a typed interface describes (`ExposePTyped.Realizes`) makes it coherent
(`TypedCat.Thms.realizes_coh`, from `StoreOk`, `FrameOk`/`ModuleInstOk` and `Ctx.Good`).

**The typed frame rule.** `I.withBelow R` puts the value types `R` below the stack of `I`.

**Typed answers.** `TypedAns Γ C`: from a store agreeing with `Γ`, `C`'s answers agree with `Γ`
and their returned values (top first) carry the callee's result types. `fitP C` restricts an
oracle to calls passing the callee's parameter count (the only calls checked code makes).

**Relations of answered runs** (`ORel`): from a store, a frame and a top-first stack, to a store,
a frame and a body result `POut`. `denR C es` is `EvalOXP C` on `es`; `idR` and `seqR` (exit-aware
relational composition) make the category; `whiskR rest` puts the passive values `rest` below
(`whiskO` on the result), `trimR` reads branches and returns at their target's arity (`trimO`).

**Premonoidal structure.** `leftR n g` runs `g` on the top `n` values, the rest passive below (the
whiskering code has, `g ⋉ -`); `rightR m g` runs `g` below the top `m` values, which stay above
(`- ⋊ g`, a semantic operation only: code reaches only the top of the stack). `Interchange n n' g₁
g₂` is the interchange law for `g₁` (`n` values to `n'`) on top of `g₂`. `PureAt n φ g`: `g` is the
pure, total, effect-free stack function `φ` on stacks of height `n` (no store, frame, trap or
call effect); such morphisms are central.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Validation (DefType CValType TyOk Sub)

variable {H : Type}

/-! ## Coherence of a typed interface with the store context -/

/-- **Coherence** of a typed interface with the store context: the context's types, functions and
tags are those of the instance in the store, as module-instance typing says. -/
structure Coh (Γ : Ctx H) (I : TIface) : Prop where
  /-- The context's types are the instance's. -/
  types : I.C.types = I.mi.types
  /-- A context function is an instance function whose store type is it, or a subtype of it. -/
  funcs : ∀ (x : Nat) (d : DefType), I.C.funcs[x]? = some d →
    ∃ a fi, I.mi.funcs[x]? = some a ∧ Γ.funcs[a]? = some fi ∧ TyOk {} fi.type ∧
      (d = fi.type ∨ (TyOk {} d ∧ Sub {} fi.type d))
  /-- A context tag is an instance tag whose store tag instance has its type. -/
  tags : ∀ (x : Nat) (d : DefType), I.C.tags[x]? = some d →
    ∃ a ti, I.mi.tags[x]? = some a ∧ Γ.tags[a]? = some ti ∧ ti.type = d

/-- The interface with the value types `R` below its stack (bottom first). -/
def _root_.Silmaril.Wasm.Abstract.ExposePTyped.TIface.withBelow (I : TIface)
    (R : List CValType) : TIface :=
  ⟨I.mi, I.C, R ++ I.ts⟩

/-! ## Typed answers -/

/-- **Typed answers**: from a store agreeing with `Γ`, every answer agrees with `Γ` and returns, on
top, values of the callee's result types. -/
def TypedAns (Γ : Ctx H) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₂ : Store H) (a : Nat) (args : List Val) (fl : Flow), C s a args (s₂, fl) → Γ.Good s →
    Γ.Good s₂ ∧ ∀ (fi : FuncInst H) (ps rs : List CValType) (vs : List Val),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
        fl.retVals = some vs → List.Forall₂ (ValOk s₂) (vs.take rs.length).reverse rs

/-- The calls passing the callee's parameter count. -/
def ArgsFit (s : Store H) (a : Nat) (args : List Val) : Prop :=
  ∀ (fi : FuncInst H) (ps rs : List CValType), s.funcs[a]? = some fi →
    Validation.DefType.funcType? fi.type = some (ps, rs) → args.length = ps.length

/-- An oracle restricted to calls passing the callee's parameter count. -/
def fitP (C : Abstract.CallRel H) : Abstract.CallRel H := fun s a args out =>
  C s a args out ∧ ArgsFit s a args

/-! ## Relations of answered runs -/

/-- Relations of answered runs: from a store, frame and top-first stack to a store, frame and body
result. -/
abbrev ORel (H : Type) : Type := Store H → Frame → List Val → Store H → Frame → POut → Prop

/-- The answered runs of `es`. -/
def denR (C : Abstract.CallRel H) (es : List BExpr) : ORel H := fun s f stk s' f' o =>
  EvalOXP C s f stk es (s', f', o)

/-- The identity: fall through on the configuration. -/
def idR : ORel H := fun s f stk s' f' o => s' = s ∧ f' = f ∧ o = .flow (.normal stk)

/-- **Exit-aware composition**: `g₂` after a fallthrough of `g₁`; every other result of `g₁`
passes. -/
def seqR (g₁ g₂ : ORel H) : ORel H := fun s f stk s' f' o =>
  (∃ s₁ f₁ vs, g₁ s f stk s₁ f₁ (.flow (.normal vs)) ∧ g₂ s₁ f₁ vs s' f' o) ∨
    (g₁ s f stk s' f' o ∧ ¬ o.IsNormal)

/-- **The whiskering** by passive values `rest` below the stack: `whiskO rest` on the result. -/
def whiskR (rest : List Val) (g : ORel H) : ORel H := fun s f stk' s' f' o' =>
  ∃ stk o, stk' = stk ++ rest ∧ g s f stk s' f' o ∧ o' = whiskO rest o

/-- Read branches and returns at their target's arity. -/
def trimR (labels : List Nat) (ret : Nat) (g : ORel H) : ORel H := fun s f stk s' f' X =>
  ∃ o, g s f stk s' f' o ∧ trimO labels ret o = X

/-! ## The premonoidal structure -/

/-- Put `top` above a fallthrough's stack; every other result is unchanged. -/
def aboveO (top : List Val) : POut → POut
  | .flow (.normal vs) => .flow (.normal (top ++ vs))
  | o => o

/-- `g` on the top `n` values, the rest passive below (`g ⋉ -`). -/
def leftR (n : Nat) (g : ORel H) : ORel H := fun s f stk s' f' o' =>
  n ≤ stk.length ∧ ∃ o, g s f (stk.take n) s' f' o ∧ o' = whiskO (stk.drop n) o

/-- `g` below the top `m` values, which stay above (`- ⋊ g`). -/
def rightR (m : Nat) (g : ORel H) : ORel H := fun s f stk s' f' o' =>
  m ≤ stk.length ∧ ∃ o, g s f (stk.drop m) s' f' o ∧ o' = aboveO (stk.take m) o

/-- **The interchange law** for `g₁` (from `n` values to `n'`) on top of `g₂`: running `g₁` first
or `g₂` first is the same relation. -/
def Interchange (n n' : Nat) (g₁ g₂ : ORel H) : Prop :=
  seqR (leftR n g₁) (rightR n' g₂) = seqR (rightR n g₂) (leftR n g₁)

/-- `g` is the pure stack function `φ` on stacks of height `n`, to stacks of height `n'`: total,
deterministic, keeping the store and the frame, independent of both. -/
def PureAt (n n' : Nat) (φ : List Val → List Val) (g : ORel H) : Prop :=
  (∀ stk, stk.length = n → (φ stk).length = n') ∧
    ∀ s f stk s' f' o, stk.length = n →
      (g s f stk s' f' o ↔ s' = s ∧ f' = f ∧ o = .flow (.normal (φ stk)))

end Silmaril.Wasm.Abstract.TypedCat
