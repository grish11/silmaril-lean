module

public import Silmaril.Wasm.Interp.CheckComplete.Defs
public import Silmaril.Wasm.Interp.EHExt.Thms
public import Silmaril.Wasm.Abstract.TypedCatValid.Thms
import Silmaril.Proofs.Wasm.Interp.CheckComplete

/-!
# Relative completeness of the exception arity checker: theorems

The exception checker's acceptance `StoreChkE (ehExt tags) s.funcs`, assumed by the CFG,
session and typed-category theorems, is **not** a consequence of validation: the checker
accepts only the instruction profile `supported` (`XProfile.xInstr_of_flatChkE`), and validated
code outside it is rejected (§3). It is a consequence of validation **and** the profile:

**1. Relative completeness** (`chkE_complete`). If the checker's parameters read a validation
context `C` (`CtxMatch`), every instruction sequence valid in `C` at `t₁ →_{xs} t₂`
(`Validation.InstrsOk`, with all its rules: `seq`, subsumption and frames) whose lifted tree is
`supported` is accepted from every height `t₁.length + k`, never falling through or falling
through at `t₂.length + k`. For an expression (`exprOk_endsAt`): `Expr_ok C e ts` gives
`endsAt … ts.length`. No tag, store or typing assumption beyond `CtxMatch`.

**2. Stores** (`storeChkE_of_storeOk`). In a Core-typed store (`StoreOk s`), the body context of
every Wasm function's `Func_ok` matches the checker's parameters for that function (with the
store's own tags: `ctxMatch_funcBody`, from `Moduleinst_ok`: callees through `Externaddr_ok`
and the function subtyping arity, tags exactly), so `StoreOk s` and `StoreSupported s.funcs`
give `StoreChkE (ehExt s.tags) s.funcs`. `StoreSupported` is decided by `storeSupportedB`
(`storeSupportedB_iff`), so `storeChkE_of_storeSupportedB` is a computable certificate. With
`TagsOk tags s` the tags are the store's (`storeChkE_of_tagsOk`). The typed-category corollary
`TypedCatValid.typed_invocation_self` then needs no checker hypothesis
(`typed_invocation_supported`).

**3. The restriction is real.** `floatBody` (`f32.const 0; drop`) is valid in every context at
`[] → []` (`floatBody_ok`), outside the profile (`floatBody_unsupported`), and rejected by the
checker for every extension, store, instance and height (`floatBody_rejected`); no store holding
it as a `[] → []` function passes `StoreChkE` (`not_storeChkE_floatBody`).

**Not proved.** The converse (acceptance implies `supported`) holds only on reachable code: the
checker does not look at code after an instruction that never falls through, `supported` does.
Completeness is relative to `InstrsOk`/`ExprOk`; stores are covered through `StoreOk`.
-/

public section

namespace Silmaril.Wasm.Interp.CheckComplete

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Validation (Context InstrOk InstrsOk ExprOk CValType LocalType)

variable {H : Type}

/-! ## 1. Relative completeness -/

/-- **Relative completeness of the exception checker**: a valid, supported instruction sequence
is accepted from every height above its parameters, never falling through or falling through at
its results above the same frame. -/
theorem chkE_complete {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {C : Context} {is : List Instr} {t₁ t₂ : List CValType}
    {xs : List Nat} (hm : CtxMatch tags F mi nl ret labels C) (h : InstrsOk C is ⟨t₁, xs, t₂⟩)
    (hsup : supported (liftInstrs is) = true) (k : Nat) :
    ∃ o, chkE (ehExt tags) F mi nl ret labels (some (t₁.length + k)) (liftInstrs is) = some o ∧
      (o = none ∨ o = some (t₂.length + k)) :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.chkE_complete hm h hsup k

/-- **A valid, supported expression is accepted at its result count.** -/
theorem exprOk_endsAt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {C : Context} {e : List Instr} {ts : List CValType}
    (hm : CtxMatch tags F mi nl ret labels C) (h : ExprOk C e ts)
    (hsup : supported (liftInstrs e) = true) :
    endsAt (chkE (ehExt tags) F mi nl ret labels (some 0) (liftInstrs e)) ts.length = true :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.exprOk_endsAt hm h hsup

/-! ## 2. Stores -/

/-- **A function body's `Func_ok` context matches the checker's parameters**, in a typed store
with its own tags. -/
theorem ctxMatch_funcBody {s : Store H} {mi : ModuleInst} {C : Context} (hs : StoreOk s)
    (hmi : ModuleInstOk s mi C) {ps rs : List CValType} {lts : List LocalType} {nl : Nat}
    (hnl : nl = ps.length + lts.length) :
    CtxMatch s.tags s.funcs mi nl rs.length [rs.length] (C.funcBody ps rs lts) :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.ctxMatch_funcBody hs hmi hnl

/-- **A typed store whose Wasm functions are supported is accepted by the exception checker.** -/
theorem storeChkE_of_storeOk {s : Store H} (hs : StoreOk s) (hsup : StoreSupported s.funcs) :
    StoreChkE (ehExt s.tags) s.funcs :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.storeChkE_of_storeOk hs hsup

/-- `storeSupportedB` decides `StoreSupported`. -/
theorem storeSupportedB_iff {F : List (FuncInst H)} : storeSupportedB F = true ↔ StoreSupported F :=
  ⟨Silmaril.Proofs.Wasm.Interp.CheckComplete.storeSupported_of_B,
    Silmaril.Proofs.Wasm.Interp.CheckComplete.storeSupportedB_of⟩

/-- **The computable certificate**: a typed store passing `storeSupportedB` is accepted. -/
theorem storeChkE_of_storeSupportedB {s : Store H} (hs : StoreOk s)
    (hb : storeSupportedB s.funcs = true) : StoreChkE (ehExt s.tags) s.funcs :=
  storeChkE_of_storeOk hs (storeSupportedB_iff.1 hb)

/-- With the tag invariants `TagsOk tags s`, the checker at `tags` accepts the store. -/
theorem storeChkE_of_tagsOk {tags : List TagInst} {s : Store H} (hs : StoreOk s)
    (hts : TagsOk tags s) (hsup : StoreSupported s.funcs) : StoreChkE (ehExt tags) s.funcs :=
  hts.1 ▸ storeChkE_of_storeOk hs hsup

/-- **The typed-category corollary without the checker hypothesis**: in a typed store whose
Wasm functions are supported, every Wasm function invoked on typed arguments has a typed body. -/
theorem typed_invocation_supported {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} (hs : StoreOk s) (hsup : StoreSupported s.funcs) (hinv : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    ∃ (hchk : StoreChkE (ehExt s.tags) s.funcs) (C : Context) (ps rs : Validation.Ty (.list .val))
      (lts : List LocalType) (ft : Bool),
      Abstract.TypedCatValid.BodyOk s fi fn C ps rs lts ∧
      (∀ ps₀ rs₀, Validation.DefType.funcType? fi.type = some (ps₀, rs₀) →
        ps.toList.length = ps₀.length ∧ rs.toList.length = rs₀.length) ∧
      Abstract.TypedCatValid.TypedBody (Abstract.TypedCatValid.storeCtx s.tags s hchk)
        (Abstract.TypedCatValid.bodyIface fi.module C ps.toList rs.toList lts)
        (Abstract.TypedCatValid.bodyEnd fi.module C ps.toList rs.toList lts) ft s
        (Frame.forCall fi.module vs fn.locals) (liftInstrs fn.body) :=
  ⟨storeChkE_of_storeOk hs hsup, Abstract.TypedCatValid.typed_invocation_self hs hinv hfi hcode _⟩

/-! ## 3. The restriction is real -/

/-- `floatBody` is valid at `[] → []` in every context. -/
theorem floatBody_ok (C : Context) : ExprOk C floatBody [] :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.floatBody_ok C

/-- `floatBody` is outside the profile. -/
theorem floatBody_unsupported : supported (liftInstrs floatBody) = false :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.floatBody_unsupported

/-- **The checker rejects `floatBody`** for every extension, store, instance and height. -/
theorem floatBody_rejected (ext : ExtArity H) (F : List (FuncInst H)) (mi : ModuleInst)
    (nl ret : Nat) (labels : List Nat) (h : Nat) :
    chkE ext F mi nl ret labels (some h) (liftInstrs floatBody) = none :=
  Silmaril.Proofs.Wasm.Interp.CheckComplete.floatBody_rejected ext F mi nl ret labels h

/-- **No store holding `floatBody` as a function passes the store check.** -/
theorem not_storeChkE_floatBody (ext : ExtArity H) {F : List (FuncInst H)} {a : Nat}
    {fi : FuncInst H} {fn : Func} {ps rs : List CValType} (hfi : F[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hbody : fn.body = floatBody)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) : ¬ StoreChkE ext F := by
  intro h
  have := h a fi fn ps rs hfi hcode hty
  rw [hbody, floatBody_rejected] at this
  exact Bool.false_ne_true this

end Silmaril.Wasm.Interp.CheckComplete
