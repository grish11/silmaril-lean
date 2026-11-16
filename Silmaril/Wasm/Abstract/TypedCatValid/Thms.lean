module

public import Silmaril.Wasm.Abstract.TypedCatValid.Defs
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms
import Silmaril.Proofs.Wasm.Abstract.TypedCatValid.Bridge
import Silmaril.Proofs.Wasm.Abstract.TypedCatValid.Corollary

/-!
# The validation bridge for the typed category: theorems

**1. Validated bodies.** `StoreOk` gives every Wasm function of the store its `Funcinst_ok`
(`bodyOk_of_storeOk`): a module context `C`, the body's function type `ps → rs` and local types
`lts` (`BodyOk`). The store's type `fi.type` of the function is then a function type
(`bodyOk_funcType`: a supertype of a function type is one, subtyping keeping the kind) with the
body's parameter and result counts (`bodyOk_counts`), its parameters below and its results above
the body's.

**2. Typed invocations realize the body's interface.** For a typed invocation (`InvokeOk s a vs`:
arguments of the store type's parameter types) the callee frame `Frame.forCall fi.module vs
fn.locals` is Core-typed in the frame context of `C` (the arguments are retyped at the body's
parameters by contravariance, the declared locals are their defaults, as `PC.pres_callRefFunc`
types them), so the entry state is a typed state of `bodyIface` in the store context
(`realizes_body`), hence coherent (`coh_body`).

**3. Validated bodies are typed morphisms.** The lowering of the body is the body
(`Binaryen.lowerList_liftInstrs`), valid at `[] → rs` by `Func_ok`, and the checker's acceptance
`StoreChkE` of the store function, at the store type's counts, is the body's check from
`bodyIface` (the counts agree by (1)): `tmor_body`, from `bodyIface` to `bodyEnd`, falling
through at `rs` or never.

**4. The oracle.** The store context agrees with the store exactly when its tag invariants hold
(`storeCtx_good`); a typed store has them for its own tags (`tagsOk_of_storeOk`, from
`Exninst_ok`). The closure on fitting calls respects arities for any context
(`TypedCat.arityResp_fitClosed`): its answers keep `Ctx.Good` and return at least the callee's
result count, with no assumption; so `arityResp_storeCtx`, and by `TypedCatFit` the unrestricted
closure is an oracle for the tensor on checked code.

**5. The corollary** (`typedBody_of_invoke`, `typed_invocation`, and `typed_invocation_self` with
the store's own tags): every Wasm function of a typed store, invoked on typed arguments, has a
`TypedBody`: the typed entry state, coherence at both ends, the typed morphism, the typed problem
(`Interp.TypedP`), the typed frame rule and the answered tensor with the closure as oracle.

**The remaining hypothesis**: `StoreChkE (ehExt tags) s.funcs`, the exception checker's
acceptance of every function of the store. It is not a consequence of Core validation: the checker
(`Interp.chkE`) covers only the integer, control, call and exception fragment of the native
interpreter and rejects every other validated instruction (float, vector, reference, table, memory
size and bulk instructions, conversions, packed and GC instructions; see `ExposePStruct.Defs`). It
is also a field of the context `Ctx` the typed category is stated over. `InvokeOk` is used only
for the arguments' types; `TagsOk tags s` only fixes `tags`, which `typed_invocation_self` takes
to be `s.tags`. Only the conditional, answered tensor is stated; no typed premonoidal functor.
-/

public section

namespace Silmaril.Wasm.Abstract.TypedCatValid

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)

variable {H : Type}

/-! ## 1. Validated bodies -/

/-- **`StoreOk` validates every Wasm function's body.** -/
theorem bodyOk_of_storeOk {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    ∃ C ps rs lts, BodyOk s fi fn C ps rs lts :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.bodyOk_of_storeOk hs hfi hcode

/-- **The store's type of a validated body is a function type above the body's.** -/
theorem bodyOk_funcType {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts) :
    ∃ ps₀ rs₀, DefType.funcType? fi.type = some (ps₀, rs₀) ∧ ResultSub {} ps₀ ps.toList ∧
      ResultSub {} rs.toList rs₀ :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.bodyOk_funcType hs hfi hb

/-- **A validated body has the store type's parameter and result counts.** -/
theorem bodyOk_counts {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts) {ps₀ rs₀ : List CValType}
    (hty : DefType.funcType? fi.type = some (ps₀, rs₀)) :
    ps.toList.length = ps₀.length ∧ rs.toList.length = rs₀.length :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.bodyOk_counts hs hfi hb hty

/-! ## 2. Typed invocations realize the body's interface -/

/-- **The entry of a typed invocation is a typed state** of the body's interface. -/
theorem realizes_body {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType}
    (hs : StoreOk s) (hinv : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) (hts : TagsOk tags s)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    Realizes (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts) s
      (Frame.forCall fi.module vs fn.locals) [] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.realizes_body hs hinv hfi hb hts hchk

/-- **The body's interface is coherent** with the store context. -/
theorem coh_body {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType}
    (hs : StoreOk s) (hinv : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) (hts : TagsOk tags s)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    Coh (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts) :=
  realizes_coh (realizes_body hs hinv hfi hb hts hchk)

/-- What the check reads off the body's interface. -/
theorem bodyIface_env (mi : ModuleInst) (C : Context) (ps rs : List CValType)
    (lts : List LocalType) :
    (bodyIface mi C ps rs lts).env = ⟨mi, ps.length + lts.length, rs.length, [rs.length]⟩ := by
  simp [TIface.env, bodyIface, Context.funcBody]

/-! ## 3. Validated bodies are typed morphisms -/

/-- **A validated, checked body is a typed morphism**, in any context holding the function. -/
theorem tmor_body {Γ : Ctx H} {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func}
    {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hΓ : Γ.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) :
    ∃ ft, TMor Γ (bodyIface fi.module C ps.toList rs.toList lts)
      (bodyEnd fi.module C ps.toList rs.toList lts) ft (liftInstrs fn.body) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.tmor_body hs hfi hΓ hb

/-- **A validated body is a typed morphism in the store context.** -/
theorem tmor_body_storeCtx {tags : List TagInst} {s : Store H} {a : Nat} {fi : FuncInst H}
    {fn : Func} {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    ∃ ft, TMor (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts)
      (bodyEnd fi.module C ps.toList rs.toList lts) ft (liftInstrs fn.body) :=
  tmor_body hs hfi hfi hb

/-! ## 4. The oracle -/

/-- The store context agrees with the store exactly under the tag invariants. -/
theorem storeCtx_good {tags : List TagInst} {s : Store H}
    (hchk : StoreChkE (ehExt tags) s.funcs) : (storeCtx tags s hchk).Good s ↔ TagsOk tags s :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- **A typed store's exceptions have their tag's field count.** -/
theorem exnsOk_of_storeOk {s : Store H} (hs : StoreOk s) : ExnsOk s.tags s :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.exnsOk_of_storeOk hs

/-- **A typed store has the tag invariants of its own tags.** -/
theorem tagsOk_of_storeOk {s : Store H} (hs : StoreOk s) : TagsOk s.tags s :=
  ⟨rfl, exnsOk_of_storeOk hs⟩

/-- **The closure on fitting calls respects arities in the store context.** -/
theorem arityResp_storeCtx {tags : List TagInst} {s : Store H}
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    ArityResp (storeCtx tags s hchk) (fitP closedCallXP) :=
  arityResp_fitClosed _

/-! ## 5. Typed bodies of validated invocations -/

/-- **A typed invocation's validated body is a typed body.** -/
theorem typedBody_of_invoke {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType}
    (hs : StoreOk s) (hinv : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) (hts : TagsOk tags s)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    ∃ ft, TypedBody (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts)
      (bodyEnd fi.module C ps.toList rs.toList lts) ft s (Frame.forCall fi.module vs fn.locals)
      (liftInstrs fn.body) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.typedBody_of_invoke hs hinv hfi hb hts hchk

/-- **Every Wasm function of a typed store, invoked on typed arguments, has a typed body**, at
the body's validation (with the store type's counts). -/
theorem typed_invocation {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} (hs : StoreOk s) (hinv : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) (hts : TagsOk tags s)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    ∃ (C : Context) (ps rs : Ty (.list .val)) (lts : List LocalType) (ft : Bool),
      BodyOk s fi fn C ps rs lts ∧
      (∀ ps₀ rs₀, DefType.funcType? fi.type = some (ps₀, rs₀) →
        ps.toList.length = ps₀.length ∧ rs.toList.length = rs₀.length) ∧
      TypedBody (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts)
        (bodyEnd fi.module C ps.toList rs.toList lts) ft s (Frame.forCall fi.module vs fn.locals)
        (liftInstrs fn.body) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatValid.typed_invocation hs hinv hfi hcode hts hchk

/-- **The corollary with the store's own tags**: only `StoreOk`, `InvokeOk` and the checker's
acceptance. -/
theorem typed_invocation_self {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} (hs : StoreOk s) (hinv : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hchk : StoreChkE (ehExt s.tags) s.funcs) :
    ∃ (C : Context) (ps rs : Ty (.list .val)) (lts : List LocalType) (ft : Bool),
      BodyOk s fi fn C ps rs lts ∧
      (∀ ps₀ rs₀, DefType.funcType? fi.type = some (ps₀, rs₀) →
        ps.toList.length = ps₀.length ∧ rs.toList.length = rs₀.length) ∧
      TypedBody (storeCtx s.tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts)
        (bodyEnd fi.module C ps.toList rs.toList lts) ft s (Frame.forCall fi.module vs fn.locals)
        (liftInstrs fn.body) :=
  typed_invocation hs hinv hfi hcode (tagsOk_of_storeOk hs) hchk

end Silmaril.Wasm.Abstract.TypedCatValid
