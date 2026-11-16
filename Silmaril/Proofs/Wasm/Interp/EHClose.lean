module

public import Silmaril.Proofs.Wasm.Interp.EHSim
public import Silmaril.Wasm.Abstract.XRecursionE.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms

/-!
# The closure with exceptions is a sound oracle (F5, proofs)

`closedE tags` answers calls by the closure `XRecursionE.closedCallXE` (callee bodies run in
`EvalOXE`, so they may throw, catch and rethrow), on stores whose native bodies have no extended
call forms (`StoreXFree`) and which satisfy the tag invariants (`TagsOk tags`). It is sound with
exceptions on (`oracleSoundE_closedE`, `oracleThrowsE_closedE`, `oracleTagsE_closedE`), by
least-fixpoint induction: a callee's body is a Core run by `evalOXE_goodEH`, and its frame is left
by a return, a trap or a throw (`throw_ref-label`, `throw_ref-frame`). Hence `evalOXE_closed_good`:
closed runs with exceptions are Core 3.0 runs, no oracle assumed.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Abstract.XRecursionE
open Silmaril.Wasm.Abstract.XRecursion (StoreXFree)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Restricting the oracle to an invariant of the run -/

/-- **Restriction to a run invariant**: if `I` is kept by flat instructions (`hF`), by `throw` and by
the oracle's answers, then a run from a store satisfying `I` ends in one, and is a run against
the oracle restricted to stores satisfying `I`. -/
theorem EvalOXE.restrictI {C : Abstract.CallRel H} {I : Store H → Prop}
    (hF : ∀ {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Binaryen.Flow},
      Binaryen.evalFlat s f stk i = some (s', f', fl) → I s → I s')
    (hthrow : ∀ {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
      {ts : Validation.Ty (.list .val)} {vs : List Val}, s.tag? f x = some (ta, ti) →
      Validation.Expand ti.type (.func ts .nil) → vs.length = ts.length → I s →
      I (s.addExn ⟨ta, vs⟩))
    (hC : ∀ s a us out, C s a us out → I s → I out.1)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOXE C s f stk es r) :
    I s → I r.1 ∧ EvalOXE (fun s a us out => I s ∧ C s a us out) s f stk es r := by
  induction h with
  | nil => exact fun hI => ⟨hI, .nil⟩
  | argsAbort _ hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .argsAbort d1 hfl⟩
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hC _ _ _ _ hcall h1)
    exact ⟨h2, .callOk d1 hfi hty ⟨h1, hcall⟩ hvs d2⟩
  | callTrap _ hfi hty hcall ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callTrap d1 hfi hty ⟨h1, hcall⟩⟩
  | callThrow _ hfi hty hcall ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callThrow d1 hfi hty ⟨h1, hcall⟩⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hF hflat h1)
    exact ⟨h2, .opOk hi d1 hflat d2⟩
  | opStop hi _ hflat hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hF hflat h1, .opStop hi d1 hflat hfl⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .blockOk har d1 hvs d2⟩
  | blockBrk har _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .blockBrk har d1⟩
  | blockEsc har _ hfl ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .blockEsc har d1 hfl⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .loopOk har d1 d2⟩
  | loopBack har _ _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .loopBack har d1 d2⟩
  | loopBrk har _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .loopBrk har d1⟩
  | loopEsc har _ hfl ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .loopEsc har d1 hfl⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1; obtain ⟨h3, d3⟩ := ih₃ h2
    exact ⟨h3, .ifOk d1 hb har d2 hvs d3⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .ifBrk d1 hb har d2⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .ifEsc d1 hb har d2 hfl⟩
  | ifAbort _ hfl ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .ifAbort d1 hfl⟩
  | callIndOk _ hres hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hC _ _ _ _ hcall h1)
    exact ⟨h2, .callIndOk d1 hres hfi hty ⟨h1, hcall⟩ hvs d2⟩
  | callIndRes _ hres ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .callIndRes d1 hres⟩
  | callIndStop _ hres hfi hty hcall hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callIndStop d1 hres hfi hty ⟨h1, hcall⟩ hfl⟩
  | callRefOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hC _ _ _ _ hcall h1)
    exact ⟨h2, .callRefOk d1 hfi hty ⟨h1, hcall⟩ hvs d2⟩
  | callRefNull _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .callRefNull d1⟩
  | callRefStop _ hfi hty hcall hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callRefStop d1 hfi hty ⟨h1, hcall⟩ hfl⟩
  | tail _ hres hfi hty hcall hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .tail d1 hres hfi hty ⟨h1, hcall⟩ hfl⟩
  | tailRes _ hres ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tailRes d1 hres⟩
  | throw _ ht he hn ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hthrow ht he (by simp only [List.length_reverse, List.length_take]; omega) h1,
      .throw d1 ht he hn⟩
  | throwRefNull _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .throwRefNull d1⟩
  | throwRefExn _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .throwRefExn d1⟩
  | tryOk har _ hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .tryOk har d1 hvs d2⟩
  | tryBrk har _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryBrk har d1⟩
  | tryEsc har _ hfl hnt ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryEsc har d1 hfl hnt⟩
  | tryCatch har _ hc ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryCatch har d1 hc⟩
  | tryRethrow har _ hc ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryRethrow har d1 hc⟩

/-! ## Sound answers -/

/-- **A sound answer with exceptions**, for the checker `ehExt tags`: it keeps the tag invariants,
and in every `call_ref` form it satisfies the clauses of `OracleSoundE … true` and
`OracleThrowsE`. -/
def SoundAnsE (tags : List TagInst) (P : Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (a : Nat) (us : List Val) (out : Store H × Binaryen.Flow) : Prop :=
  TagsOk tags out.1 ∧
  ∀ (f : Frame) (fi : FuncInst H) (ps rs : List Validation.CValType) (c : Admin),
    StoreChkE (ehExt tags) s.funcs → s.funcs[a]? = some fi →
    Validation.DefType.funcType? fi.type = some (ps, rs) → us.length = ps.length → c.IsCallRef →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOkE true [rs.length] rs.length ob out.2 ∧
        FuncsGoodE (ehExt tags) s.funcs out.1.funcs) ∧
      (∀ vs, out.2.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, vals (vs.take rs.length).reverse⟩) ∧
      (out.2 = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, [.trap]⟩) ∧
      (∀ t, out.2 = .throw t → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, throwing t⟩)

/-- **A callee whose body has a sound run answers soundly**, a thrown exception leaving the
callee's label and frame (`throw_ref-label`, `throw_ref-frame`). -/
theorem soundAnsE_of_body {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : OracleSoundE (ehExt tags) P host C true) (hT : OracleThrowsE (ehExt tags) P host C)
    (hG : OracleTagsE tags C) {s s₂ : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {f₂ : Frame} {fl : Binaryen.Flow} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hx : xFreeL (Binaryen.liftInstrs fn.body) = true)
    (hts : TagsOk tags s)
    (d : EvalOXE C s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl)) :
    SoundAnsE tags P host s a us (s₂, fl) := by
  obtain ⟨ht₂, hA, hCore⟩ := evalOXE_goodEH (P := P) (host := host) hC hT hG d hx hts
  refine ⟨ht₂, ?_⟩
  intro f fi' ps rs c hS hfi' hty hn hcr
  rw [hfi] at hfi'; cases hfi'
  have hend := hS a fi fn ps rs hfi hcode hty
  obtain ⟨ob, hb, hob⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length = ps.length + fn.locals.length :=
    forCall_length _ _ hn
  have hb' : chkE (ehExt tags) s.funcs (Frame.forCall fi.module us fn.locals).module
      (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlen]; exact hb
  obtain ⟨hok, hinv⟩ := hA hS hb'
  have hwb := hCore hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hwb
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := by rw [hn, ← hpl]
  have hrl' : rs'.length = rs.length := by rw [← hrl]
  have enter : Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module us fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
    rw [← hrl']
    exact .single (Step.callRefFunc hcr hfi hex hn' hcode)
  have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
    (Steps.label rs.length [] (by simpa [vals] using hrun))
  refine ⟨⟨ob, hob, hok, hinv.1⟩, fun vs hvs => ?_, fun htr => ?_, fun t hth => ?_⟩
  · have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
      rintro ws rfl
      exact length_of_ends hok hob
    obtain ⟨s', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
      (funcPost_of_match (s₂ := s₂) (F := f₂) hm hvs hrs hnorm)
    obtain ⟨rfl, rfl⟩ := hK
    exact enter.trans (inner.trans hret)
  · subst htr
    have hc : c' = [.trap] := by
      rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
      exact he
    subst hc
    have out : Steps P host ⟨s₂, f, [.frame rs.length f₂ [.label rs.length [] [.trap]]]⟩
        ⟨s₂, f, [.trap]⟩ :=
      (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
    exact enter.trans (inner.trans out)
  · subst hth
    have hc : c' = throwing t := by
      rcases o with _ | _ | _ | _ | a' | _ | _ <;> simp only [FlowMatch] at hm
      subst hm
      exact he
    subst hc
    have out : Steps P host ⟨s₂, f, [.frame rs.length f₂ [.label rs.length [] (throwing t)]]⟩
        ⟨s₂, f, throwing t⟩ :=
      (Relation.ReflTransGen.single (Step.ctxtFrame Step.throwRefLabel)).tail Step.throwRefFrame
    exact enter.trans (inner.trans out)

/-! ## The closure -/

theorem storeXFree_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hX : StoreXFree s) :
    StoreXFree s' :=
  fun a fi fn h₁ h₂ => hX a fi fn (h ▸ h₁) h₂

/-- The invariant of closed runs with exceptions: no extended call forms in the store's native
bodies, and the tag invariants. -/
def GoodStoreE (tags : List TagInst) (s : Store H) : Prop := StoreXFree s ∧ TagsOk tags s

/-- **The closure with exceptions on good stores**, as a call oracle. -/
def closedE (tags : List TagInst) : Abstract.CallRel H :=
  fun s a us out => GoodStoreE tags s ∧ closedCallXE s a us out

/-- Restricting a run to an oracle defined on good stores. -/
theorem GoodStoreE.restrict {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : ∀ s a us out, C s a us out → GoodStoreE tags s → GoodStoreE tags out.1)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOXE C s f stk es r) (hg : GoodStoreE tags s) :
    GoodStoreE tags r.1 ∧
      EvalOXE (fun s a us out => GoodStoreE tags s ∧ C s a us out) s f stk es r :=
  EvalOXE.restrictI (I := GoodStoreE tags)
    (fun hf hi => ⟨storeXFree_of_funcs (Silmaril.Wasm.Abstract.XRecursion.evalFlat_funcs hf) hi.1,
      hi.2.evalFlat hf⟩)
    (fun ht he hn hi => ⟨storeXFree_of_funcs rfl hi.1, tagsOk_throw hi.2 ht he hn⟩) hC h hg

/-- **The closure's answers on good stores are sound**, by least-fixpoint induction. -/
theorem closedCallXE_sound (tags : List TagInst) :
    ∀ (s : Store H) a us out, closedCallXE s a us out → GoodStoreE tags s →
      SoundAnsE tags P host s a us out := by
  let Q : Abstract.CallRel H := fun s a us out =>
    closedCallXE s a us out ∧ (GoodStoreE tags s → SoundAnsE tags P host s a us out)
  have hQ : (closedCallXE : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us ⟨s₂, fl⟩ ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d⟩
    refine ⟨?_, fun hg => ?_⟩
    · rw [closedCallXE_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d.mono fun _ _ _ _ h => h.1⟩
    · let C' : Abstract.CallRel H := fun s a us out => GoodStoreE tags s ∧ Q s a us out
      have hC' : OracleSoundE (ehExt tags) P host C' true :=
        fun s s₂ f a fi ps rs us fl hS hfi hty hn hcall =>
          let h := (hcall.2.2 hcall.1).2 f fi ps rs (.callRefType fi.type) hS hfi hty hn trivial
          ⟨h.1, h.2.1, h.2.2.1⟩
      have hT' : OracleThrowsE (ehExt tags) P host C' :=
        fun s s₂ f a fi ps rs us t c hS hfi hty hn hcr hcall =>
          ((hcall.2.2 hcall.1).2 f fi ps rs c hS hfi hty hn hcr).2.2.2 t rfl
      have hG' : OracleTagsE tags C' := fun _ _ _ _ _ hcall _ => (hcall.2.2 hcall.1).1
      have hkeep : ∀ s a us out, Q s a us out → GoodStoreE tags s → GoodStoreE tags out.1 :=
        fun _ _ _ _ hq hg => ⟨storeXFree_of_funcs (closedCallXE_funcs hq.1) hg.1, (hq.2 hg).1⟩
      exact soundAnsE_of_body hC' hT' hG' hfi hcode (hg.1 a fi fn hfi hcode) hg.2
        (GoodStoreE.restrict hkeep d hg).2
  exact fun s a us out h hg => (hQ _ _ _ _ h).2 hg

theorem oracleSoundE_closedE (tags : List TagInst) :
    OracleSoundE (ehExt tags) P host (closedE (H := H) tags) true :=
  fun _ _ f _ fi ps rs _ _ hS hfi hty hn ⟨hg, hcl⟩ =>
    let h := (closedCallXE_sound (P := P) (host := host) tags _ _ _ _ hcl hg).2 f fi ps rs
      (.callRefType fi.type) hS hfi hty hn trivial
    ⟨h.1, h.2.1, h.2.2.1⟩

theorem oracleThrowsE_closedE (tags : List TagInst) :
    OracleThrowsE (ehExt tags) P host (closedE (H := H) tags) :=
  fun _ _ f _ fi ps rs _ t c hS hfi hty hn hcr ⟨hg, hcl⟩ =>
    ((closedCallXE_sound (P := P) (host := host) tags _ _ _ _ hcl hg).2 f fi ps rs c hS hfi hty
      hn hcr).2.2.2 t rfl

theorem oracleTagsE_closedE (tags : List TagInst) : OracleTagsE tags (closedE (H := H) tags) :=
  fun _ _ _ _ _ ⟨hg, hcl⟩ _ =>
    (closedCallXE_sound (P := Numerics.Profile.spec) (host := default) tags _ _ _ _ hcl hg).1

/-- **Closed runs with exceptions are Core 3.0 runs**: on a good store, every `EvalOXE` run
against the closure `closedCallXE`, of checked code without the extended call forms, is a Core
run with exceptions on; no oracle is assumed. -/
theorem evalOXE_closed_good {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOXE closedCallXE s f stk es r) (hg : GoodStoreE tags s)
    (hx : xFreeL es = true) :
    TagsOk tags r.1 ∧ ArityGoodE (ehExt tags) s f stk es r true ∧
      CoreGoodE (ehExt tags) P host s f stk es r := by
  have hkeep : ∀ s a us out, closedCallXE s a us out → GoodStoreE tags s →
      GoodStoreE tags out.1 :=
    fun _ _ _ _ hcl hg => ⟨storeXFree_of_funcs (closedCallXE_funcs hcl) hg.1,
      (closedCallXE_sound (P := P) (host := host) tags _ _ _ _ hcl hg).1⟩
  exact evalOXE_goodEH (oracleSoundE_closedE tags) (oracleThrowsE_closedE tags)
    (oracleTagsE_closedE tags) (GoodStoreE.restrict hkeep h hg).2 hx hg.2

end Silmaril.Wasm.Interp
