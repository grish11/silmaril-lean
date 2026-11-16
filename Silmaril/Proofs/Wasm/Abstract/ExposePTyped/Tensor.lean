module

public import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Bwd
public import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Realize

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePTyped.Thms`: the answered stack tensor, both ways, for
checked code (`Mor`) and for typed code at the run states its interface describes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP

variable {H : Type} {Γ : Ctx H} {C : Abstract.CallRel H}

theorem evalOXP_goodO (hC : ArityResp Γ C) {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {o : POut} {labels : List Nat} {ret : Nat} {oc : Option Nat}
    (d : EvalOXP C s f stk es (s', f', o)) (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO labels ret oc o := by
  obtain ⟨g, m, l, go, -⟩ := evalOXP_fwd hC d hg hc
  exact ⟨g, m, l, go⟩

theorem evalOXP_tensor (hC : ArityResp Γ C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {labels : List Nat} {ret : Nat} {oc : Option Nat} (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X := by
  constructor
  · rintro ⟨o', d, rfl⟩
    obtain ⟨o, d', e⟩ := evalOXP_bwd hC d rfl hg hc
    exact ⟨o, d', e.symm⟩
  · rintro ⟨o, d, rfl⟩
    obtain ⟨-, -, -, -, t⟩ := evalOXP_fwd hC d hg hc
    obtain ⟨o', d', e⟩ := t rest
    exact ⟨o', d', e⟩

theorem mor_tensor (hC : ArityResp Γ C) {I : Iface} {oc : Option Nat} {es : List BExpr}
    (hm : Mor Γ I oc es) {s : Store H} {f : Frame} {stk : List Val} (hg : Γ.Good s)
    (hf : f.module = I.env.mi) (hn : f.locals.length = I.env.nl) (hs : stk.length = I.h)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X := by
  apply evalOXP_tensor hC hg (oc := oc)
  rw [hg.1, hf, hn, hs]; exact hm

theorem mor_goodO (hC : ArityResp Γ C) {I : Iface} {oc : Option Nat} {es : List BExpr}
    (hm : Mor Γ I oc es) {s s' : Store H} {f f' : Frame} {stk : List Val} {o : POut}
    (d : EvalOXP C s f stk es (s', f', o)) (hg : Γ.Good s)
    (hf : f.module = I.env.mi) (hn : f.locals.length = I.env.nl) (hs : stk.length = I.h) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO I.env.labels I.env.ret oc o := by
  apply evalOXP_goodO hC d hg
  rw [hg.1, hf, hn, hs]; exact hm

/-- What a typed run state gives the check. -/
theorem realizes_chk {I : TIface} {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) :
    Γ.Good s ∧ f.module = I.forget.env.mi ∧ f.locals.length = I.forget.env.nl ∧
      stk.length = I.forget.h := by
  obtain ⟨hg, -, hfm, ⟨C₀, hF, hIC⟩, -, -, hstk⟩ := hr
  obtain ⟨-, -, hn0, -⟩ := frame_ctx hF
  refine ⟨hg, hfm, ?_, by simpa [TIface.forget] using hstk.length_eq⟩
  show f.locals.length = I.C.locals.length
  rw [hIC]; exact hn0.symm

theorem tmor_tensor (hC : ArityResp Γ C) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X := by
  obtain ⟨-, xs, -, -, -, hc⟩ := hm
  obtain ⟨hg, hf, hn, hs⟩ := realizes_chk hr
  exact mor_tensor hC hc hg hf hn hs rest s' f' X

end Silmaril.Proofs.Wasm.Abstract.ExposePTyped
