module

public import Silmaril.Proofs.Wasm.Abstract.TypedCatValid.Bridge
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCatValid.Thms`: the store's function type of a validated
body has the body's parameter and result counts (`bodyOk_funcType`, `bodyOk_counts`), and a typed
invocation's body is a typed body (`typedBody_of_invoke`): the entry state from `realizes_body`,
the morphism from `tmor_body`, and the rest from `TypedCat` and `TypedCatFit`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCatValid

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCatValid
open Silmaril.Wasm.Abstract.TypedCat (realizes_coh coh_of_tmor tmor_frame arityResp_fitClosed)
open Silmaril.Wasm.Abstract.TypedCatFit (tmor_tensor_closed)

variable {H : Type}

/-- **The store's function type of a validated body**, above the body's. -/
theorem bodyOk_funcType {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts) :
    ∃ ps₀ rs₀, DefType.funcType? fi.type = some (ps₀, rs₀) ∧ ResultSub {} ps₀ ps.toList ∧
      ResultSub {} rs.toList rs₀ := by
  obtain ⟨ps₀, rs₀, he₀⟩ := expand_of_bodyOk hs hfi hb
  obtain ⟨hps, hrs, -, -⟩ := bodyOk_sub hs hfi hb he₀
  exact ⟨ps₀.toList, rs₀.toList, by unfold DefType.funcType?; rw [Expand.iff.mp he₀], hps, hrs⟩

/-- **A validated body has the store type's parameter and result counts.** -/
theorem bodyOk_counts {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts) {ps₀ rs₀ : List CValType}
    (hty : DefType.funcType? fi.type = some (ps₀, rs₀)) :
    ps.toList.length = ps₀.length ∧ rs.toList.length = rs₀.length := by
  obtain ⟨ps₁, rs₁, hty₁, hps, hrs⟩ := bodyOk_funcType hs hfi hb
  rw [hty] at hty₁
  cases hty₁
  exact ⟨(List.Forall₂.length_eq hps).symm, List.Forall₂.length_eq hrs⟩

/-- **A typed store's exceptions have their tag's field count**: `Exninst_ok` types the fields
by the tag's parameters. -/
theorem exnsOk_of_storeOk {s : Store H} (hs : StoreOk s) : ExnsOk s.tags s := by
  intro a e he mi x hx
  obtain ⟨ti, ts, hti, hexp, hf⟩ := hs.exns e (List.mem_of_getElem? he)
  have hty : DefType.funcType? ti.type = some (ts.toList, []) := by
    unfold DefType.funcType?
    rw [Expand.iff.mp hexp]
    rfl
  simp [tagFields, hx, hti, hty, List.Forall₂.length_eq hf]

/-- **A typed invocation's body is a typed body.** -/
theorem typedBody_of_invoke {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType}
    (hs : StoreOk s) (hinv : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) (hts : TagsOk tags s)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    ∃ ft, TypedBody (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts)
      (bodyEnd fi.module C ps.toList rs.toList lts) ft s (Frame.forCall fi.module vs fn.locals)
      (liftInstrs fn.body) := by
  obtain ⟨ft, hm⟩ := tmor_body (Γ := storeCtx tags s hchk) hs hfi hfi hb
  have hr := realizes_body hs hinv hfi hb hts hchk
  obtain ⟨ps₀, rs₀, he₀⟩ := expand_of_bodyOk hs hfi hb
  obtain ⟨-, -, -, hrok⟩ := bodyOk_sub hs hfi hb he₀
  have hco := realizes_coh hr
  have hI : (bodyIface fi.module C ps.toList rs.toList lts).Ok := fun t ht => by
    simp [bodyIface] at ht
  have hJ : (bodyEnd fi.module C ps.toList rs.toList lts).Ok := fun t ht =>
    TyOk.of_empty _ (hrok t ht)
  exact ⟨ft, hr, hco, hm, coh_of_tmor hm hco, tmor_typedP hm hr hI hJ,
    fun R hR => tmor_frame hm hR, arityResp_fitClosed _,
    fun rest s' f' X => by
      simpa only [List.nil_append] using tmor_tensor_closed hm hr rest s' f' X⟩

/-- **Every Wasm function of a typed store, invoked on typed arguments, has a typed body.** -/
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
        (liftInstrs fn.body) := by
  obtain ⟨C, ps, rs, lts, hb⟩ := bodyOk_of_storeOk hs hfi hcode
  obtain ⟨ft, ht⟩ := typedBody_of_invoke hs hinv hfi hb hts hchk
  exact ⟨C, ps, rs, lts, ft, hb, fun _ _ hty => bodyOk_counts hs hfi hb hty, ht⟩

end Silmaril.Proofs.Wasm.Abstract.TypedCatValid
