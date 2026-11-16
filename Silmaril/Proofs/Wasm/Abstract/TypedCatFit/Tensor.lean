module

public import Silmaril.Proofs.Wasm.Abstract.TypedCatFit.Fit
public import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Tensor
public import Silmaril.Proofs.Wasm.Abstract.TypedCat.Strength
public import Silmaril.Wasm.Abstract.TypedCat.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCatFit.Thms`: **the coincidence of an oracle with its
fitting restriction on checked code, and the answered tensor without `fitP`.** From
`evalOXP_fit`: on checked code from a store agreeing with the context, the runs of `EvalOXP C` are
those of `EvalOXP (fitP C)` (the converse is monotonicity), so every consequence of
`ArityResp Γ (fitP C)` for `fitP C` holds for `C` itself: the result invariant, the answered
tensor (the stack `stk ++ rest` is checked at height `|stk| + |rest|`, `chkE_shift`), and its
typed and relational forms. For the closure, `ArityResp Γ (fitP closedCallXP)` is
`TypedCat.arityResp_fitClosed`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCatFit

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type} {Γ : Ctx H} {C : Abstract.CallRel H}

/-- **Coincidence** on checked code. -/
theorem evalOXP_fit_iff (hC : ArityResp Γ (fitP C)) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {labels : List Nat} {ret : Nat} {oc : Option Nat} (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) (r : Store H × Frame × POut) :
    EvalOXP C s f stk es r ↔ EvalOXP (fitP C) s f stk es r :=
  ⟨fun d => (evalOXP_fit hC d hg hc).2.2.2.2, fun d => d.mono fun _ _ _ _ h => h.1⟩

/-- The result invariant for `C`, from arity respect on fitting calls only. -/
theorem evalOXP_goodO_fit (hC : ArityResp Γ (fitP C)) {s s' : Store H} {f f' : Frame}
    {stk : List Val} {es : List BExpr} {o : POut} {labels : List Nat} {ret : Nat}
    {oc : Option Nat} (d : EvalOXP C s f stk es (s', f', o)) (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO labels ret oc o :=
  let ⟨g, m, l, go, _⟩ := evalOXP_fit hC d hg hc
  ⟨g, m, l, go⟩

/-- The answered tensor for `C`, from arity respect on fitting calls only. -/
theorem evalOXP_tensor_fit (hC : ArityResp Γ (fitP C)) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {labels : List Nat} {ret : Nat} {oc : Option Nat}
    (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X := by
  have hc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels
      (some (stk ++ rest).length) es = some (oc.map (· + rest.length)) := by
    rw [List.length_append]
    exact chkE_shift rest.length stk.length es hc
  calc (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X)
      ↔ ∃ o', EvalOXP (fitP C) s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X :=
        exists_congr fun _ => and_congr_left' (evalOXP_fit_iff hC hg hc' _)
    _ ↔ ∃ o, EvalOXP (fitP C) s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X :=
        Silmaril.Wasm.Abstract.ExposePTyped.evalOXP_tensor hC hg hc rest s' f' X
    _ ↔ ∃ o, EvalOXP C s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X :=
        exists_congr fun _ => and_congr_left' (evalOXP_fit_iff hC hg hc _).symm

/-- Typed code at a typed state is checked. -/
theorem tmor_chk {I J : TIface} {ft : Bool} {es : List BExpr} (hm : TMor Γ I J ft es)
    {s : Store H} {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) :
    Γ.Good s ∧ chkE (ehExt Γ.tags) s.funcs f.module f.locals.length I.env.ret I.env.labels
      (some stk.length) es = some (ftOut ft J.ts.length) := by
  obtain ⟨-, xs, -, -, -, hc⟩ := hm
  obtain ⟨hg, hf, hn, hs⟩ := Silmaril.Proofs.Wasm.Abstract.ExposePTyped.realizes_chk hr
  refine ⟨hg, ?_⟩
  rw [hg.1, hf, hn, hs]; exact hc

/-- **Coincidence** on typed code at a typed state. -/
theorem tmor_fit_iff (hC : ArityResp Γ (fitP C)) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (r : Store H × Frame × POut) :
    EvalOXP C s f stk es r ↔ EvalOXP (fitP C) s f stk es r :=
  let ⟨hg, hc⟩ := tmor_chk hm hr
  evalOXP_fit_iff hC hg hc r

theorem tmor_tensor_fit (hC : ArityResp Γ (fitP C)) {I J : TIface} {ft : Bool}
    {es : List BExpr} (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  let ⟨hg, hc⟩ := tmor_chk hm hr
  evalOXP_tensor_fit hC hg hc rest s' f' X

theorem tmor_tensorR_fit (hC : ArityResp Γ (fitP C)) {I J : TIface} {ft : Bool}
    {es : List BExpr} (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest) s' f' X := by
  refine (tmor_tensor_fit hC hm hr rest s' f' X).trans ?_
  constructor
  · rintro ⟨o, h, rfl⟩
    exact ⟨_, (Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_denR_iff rest).2 ⟨o, h, rfl⟩, rfl⟩
  · rintro ⟨o', ho', rfl⟩
    obtain ⟨o, h, rfl⟩ := (Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_denR_iff rest).1 ho'
    exact ⟨o, h, rfl⟩

theorem tmor_tensorR_comp_fit (hC : ArityResp Γ (fitP C)) {I J K : TIface} {ft : Bool}
    {es₁ es₂ : List BExpr} (h₁ : THom Γ I J es₁) (h₂ : TMor Γ J K ft es₂) {s : Store H}
    {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H)
    (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C (es₁ ++ es₂)) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (seqR (whiskR rest (denR C es₁)) (whiskR rest (denR C es₂)))
        s f (stk ++ rest) s' f' X := by
  rw [tmor_tensorR_fit hC (Silmaril.Wasm.Abstract.ExposePTyped.tmor_comp h₁ h₂) hr rest s' f' X,
    denR_append, whiskR_seqR]

end Silmaril.Proofs.Wasm.Abstract.TypedCatFit
