module

public import Silmaril.Wasm.Abstract.TypedCatValid.Defs
public import Silmaril.Wasm.Abstract.TypedCat.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCatValid.Thms`: `StoreOk` gives each Wasm function of the
store its `Funcinst_ok` (`bodyOk_of_storeOk`); the store's type of a validated body is a function
type above the body's (`expand_func_of_super`, `bodyOk_sub`); the callee frame of a typed
invocation is typed in the body context (as `PC.pres_callRefFunc` types it), so the entry state
is a typed state (`realizes_body`); and the body, lowered back, is the validated body, accepted by
the checker at the result count (`tmor_body`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCatValid

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.PC
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCatValid

variable {H : Type}

/-- **A supertype of a function type is a function type** (in `{}`): subtyping keeps the kind. -/
theorem expand_func_of_super {d₁ d₂ : DefType} (h1 : TyOk {} d₁) (h2 : TyOk {} d₂)
    (hs : Sub {} (Ty.use (.dt d₁) : CHeapType) (.use (.dt d₂))) {p r : Ty (.list .val)}
    (he : Expand d₁ (.func p r)) : ∃ p' r', Expand d₂ (.func p' r') := by
  have hc := Sub.complete TypeCtx.ok_empty rfl hs (.use (.dt h1)) (.use (.dt h2))
  simp only [Sub.checkK, TypeCtx.checkHeap, TypeCtx.resolve] at hc
  have hk := TypeCtx.checkDef_kind TypeCtx.ok_empty h1 hc
  obtain ⟨hu⟩ := he
  cases hu2 : unrolldt d₂ with
  | none => simp [Validation.defKind, hu, hu2] at hk
  | some st =>
    cases st with
    | sub fin sups ct =>
      cases ct with
      | func p' r' => exact ⟨p', r', ⟨hu2⟩⟩
      | struct _ => simp [Validation.defKind, hu, hu2, compAbs, Ty.body] at hk
      | array _ => simp [Validation.defKind, hu, hu2, compAbs, Ty.body] at hk

/-- **`StoreOk` validates every Wasm function's body.** -/
theorem bodyOk_of_storeOk {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    ∃ C ps rs lts, BodyOk s fi fn C ps rs lts := by
  have hfo := hs.funcs fi (List.mem_of_getElem? hfi)
  cases hfo with
  | host _ _ hcode' => rw [hcode] at hcode'; cases hcode'
  | @wasm C₁ code' d' _ hm hcode' hfo hsd =>
    rw [hcode] at hcode'; cases hcode'
    cases hfo with
    | @mk ps' rs' lts hd' he' hl hb =>
      exact ⟨C₁, ps', rs', lts, hcode, hm, ⟨d', hd', he', hsd⟩, hl, hb⟩

/-- The body's type, closed, below the store's type. -/
theorem bodyOk_heap {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts) :
    ∃ d, TyOk {} d ∧ Expand d (.func ps rs) ∧ TyOk {} fi.type ∧
      Sub {} (Ty.use (.dt d) : CHeapType) (.use (.dt fi.type)) := by
  obtain ⟨-, hm, ⟨d, hd, he, hsd⟩, -, -⟩ := hb
  have hΔ := ModuleInstOk.typesOk' hm
  have hdok : TyOk {} d := hΔ.get hd
  have hfit := StoreOk.func_tyOk hs hfi
  exact ⟨d, hdok, he, hfit, (heap_toEmpty hΔ (.defDef hsd) (a := Ty.use (.dt d)) hdok
    (.use (.dt hfit))).1⟩

/-- **The store's type of a validated body is a function type.** -/
theorem expand_of_bodyOk {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts) :
    ∃ ps₀ rs₀ : Ty (.list .val), Expand fi.type (.func ps₀ rs₀) := by
  obtain ⟨d, hdok, he, hfit, hsub⟩ := bodyOk_heap hs hfi hb
  exact expand_func_of_super hdok hfit hsub he

/-- **The store's function type is a supertype of the body's**: contravariant parameters,
covariant results, all closed. -/
theorem bodyOk_sub {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {C : Context}
    {ps rs ps₀ rs₀ : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hb : BodyOk s fi fn C ps rs lts)
    (he₀ : Expand fi.type (.func ps₀ rs₀)) :
    ResultSub {} ps₀.toList ps.toList ∧ ResultSub {} rs.toList rs₀.toList ∧
      ResultOk {} ps.toList ∧ ResultOk {} rs.toList := by
  obtain ⟨d, hdok, he, hfit, hsub⟩ := bodyOk_heap hs hfi hb
  obtain ⟨hps, hrs⟩ := ds_func hdok hfit hsub he he₀
  have hpr := Expand.func_ok hdok he
  exact ⟨hps, hrs, hpr.1, hpr.2⟩

/-- The callee frame's context: the module context with the parameters and declared locals. -/
def frameCtx (C : Context) (ps : List CValType) (lts : List LocalType) : Context :=
  { C with locals := C.locals ++ (ps.map (fun t => (⟨.set, t⟩ : LocalType)) ++ lts) }

/-- The body context is the frame context with the body's label and return type. -/
theorem funcBody_eq {s : Store H} {mi : ModuleInst} {C : Context} {ps rs : List CValType}
    {lts : List LocalType} (hm : ModuleInstOk s mi C) :
    (bodyIface mi C ps rs lts).C = { frameCtx C ps lts with
      labels := (bodyIface mi C ps rs lts).C.labels,
      return_ := (bodyIface mi C ps rs lts).C.return_ } := by
  obtain ⟨hloc0, -, -, -⟩ := ModuleInstOk.ctx_fields hm
  simp [bodyIface, frameCtx, Context.funcBody, hloc0]

/-- **The entry of a typed invocation is a typed state** of the body's interface. -/
theorem realizes_body {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType}
    (hs : StoreOk s) (hinv : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) (hts : TagsOk tags s)
    (hchk : StoreChkE (ehExt tags) s.funcs) :
    Realizes (storeCtx tags s hchk) (bodyIface fi.module C ps.toList rs.toList lts) s
      (Frame.forCall fi.module vs fn.locals) [] := by
  obtain ⟨fi', ps₁, rs₁, hfi', he₁, hvs⟩ := hinv
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨hps, -, hpok, hrok⟩ := bodyOk_sub hs hfi hb he₁
  have hsT : PC.StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hargs := valsOk_transfer hs hsT typesOk_empty hvs hps hpok
  obtain ⟨-, hm, -, hl, -⟩ := hb
  have hΔ := ModuleInstOk.typesOk' hm
  obtain ⟨-, -, -, htypes⟩ := ModuleInstOk.ctx_fields hm
  have hloc : List.Forall₂ (LocalValOk s) (Frame.forCall fi.module vs fn.locals).locals
      (ps.toList.map (fun t => (⟨.set, t⟩ : LocalType)) ++ lts) := by
    simp only [Frame.forCall]
    refine forall₂_append (locals_set_ok hargs) ?_
    have := locals_default_ok (s := s) hΔ hl
    simpa [Context.closeVal, htypes] using this
  refine ⟨⟨rfl, hts⟩, hs, rfl, ⟨frameCtx C ps.toList lts, ⟨C, _, hm, hloc, rfl⟩, funcBody_eq hm⟩,
    ⟨rs.toList, rfl, hrok⟩, ?_, .nil⟩
  intro L hL
  simp only [bodyIface, Context.funcBody, List.mem_singleton] at hL
  subst hL
  exact hrok

/-- **A validated, checked body is a typed morphism** from its entry to its exit interface. -/
theorem tmor_body {Γ : Ctx H} {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func}
    {C : Context} {ps rs : Ty (.list .val)} {lts : List LocalType} (hs : StoreOk s)
    (hfi : s.funcs[a]? = some fi) (hΓ : Γ.funcs[a]? = some fi)
    (hb : BodyOk s fi fn C ps rs lts) :
    ∃ ft, TMor Γ (bodyIface fi.module C ps.toList rs.toList lts)
      (bodyEnd fi.module C ps.toList rs.toList lts) ft (liftInstrs fn.body) := by
  obtain ⟨ps₀, rs₀, he₀⟩ := expand_of_bodyOk hs hfi hb
  obtain ⟨hps, hrs, -, -⟩ := bodyOk_sub hs hfi hb he₀
  have hty : DefType.funcType? fi.type = some (ps₀.toList, rs₀.toList) := by
    unfold DefType.funcType?
    rw [Expand.iff.mp he₀]
  obtain ⟨ob, hc, hob⟩ := endsAt_eq (Γ.storeChk a fi fn _ _ hΓ hb.code hty)
  have hpl : ps₀.toList.length = ps.toList.length := List.Forall₂.length_eq hps
  have hrl : rs.toList.length = rs₀.toList.length := List.Forall₂.length_eq hrs
  have hll : fn.locals.length = lts.length := List.Forall₂.length_eq hb.locals
  have hF : (bodyIface fi.module C ps.toList rs.toList lts).forget =
      ⟨⟨fi.module, ps₀.toList.length + fn.locals.length, rs₀.toList.length,
        [rs₀.toList.length]⟩, 0⟩ := by
    simp [TIface.forget, TIface.env, bodyIface, Context.funcBody, hpl, hrl, hll]
  have hI : InstrsOk (bodyIface fi.module C ps.toList rs.toList lts).C
      (BExpr.lowerList (liftInstrs fn.body)) ⟨[], [], rs.toList⟩ := by
    rw [lowerList_liftInstrs]; exact hb.body
  rcases hob with rfl | rfl
  · refine ⟨false, rfl, [], by simp, rfl, hI, ?_⟩
    unfold Mor chkIn
    rw [hF]
    exact hc
  · refine ⟨true, rfl, [], by simp, rfl, hI, ?_⟩
    unfold Mor chkIn
    rw [hF]
    simpa [ftOut, bodyEnd, hrl] using hc

end Silmaril.Proofs.Wasm.Abstract.TypedCatValid
