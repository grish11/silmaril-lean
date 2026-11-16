module

public import Silmaril.Wasm.Abstract.XDiverge.Defs
public import Silmaril.Wasm.Interp.Diverge.Thms
public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms
import Silmaril.Proofs.Wasm.Abstract.XRecursion.Basic

/-!
Proofs for `Silmaril.Wasm.Abstract.XDiverge.Thms`: unfolding and coinduction,
and agreement with `Interp.EvalDiv` / `Interp.LocalDiv` on direct stores and
code. A `DivStep` unfolding is a `DivStepX` one (`stepX_of_step`) and, on
direct code, conversely (`step_of_stepX`): the terminating parts agree
(`XRecursion.evalOX_closed_iff`, `Recursion.evalO_closed_iff`) and the store's
functions are kept along them, so the store stays direct.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDiverge

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem DivStep EvalDiv LocalDiv)
open Silmaril.Wasm.Abstract (EvalO closedCall)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDiverge
open Silmaril.Proofs.Wasm.Abstract.XRecursion (storeXFree_of_funcs)

variable {H : Type}

theorem evalDivX_unfold {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDivX s f stk es ↔ DivStepX EvalDivX EvalDivX s f stk es := by
  have h : divOpX (EvalDivX (H := H)) = EvalDivX := (divOpX (H := H)).map_gfp
  exact (Eq.to_iff (congrFun (congrFun (congrFun (congrFun h s) f) stk) es)).symm

theorem localDivX_unfold {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    LocalDivX s f stk es ↔ DivStepX LocalDivX ⊥ s f stk es := by
  have h : localDivOpX (LocalDivX (H := H)) = LocalDivX := (localDivOpX (H := H)).map_gfp
  exact (Eq.to_iff (congrFun (congrFun (congrFun (congrFun h s) f) stk) es)).symm

theorem evalDivX_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepX X X s f stk es) : X ≤ EvalDivX :=
  (divOpX (H := H)).le_gfp fun s f stk es hx => h s f stk es hx

theorem localDivX_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepX X ⊥ s f stk es) : X ≤ LocalDivX :=
  (localDivOpX (H := H)).le_gfp fun s f stk es hx => h s f stk es hx

theorem localDivX_le_evalDivX : (LocalDivX : Problem H) ≤ EvalDivX :=
  evalDivX_coind fun _ _ _ _ h =>
    DivStepX.mono le_rfl (fun _ _ _ _ h => h.elim) (localDivX_unfold.1 h)

/-! ## The direct part -/

/-- The terminating parts, on direct code: `Eval` is `EvalOX closedCallX`. -/
theorem evalOX_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) : EvalOX closedCallX s f stk es r :=
  EvalOX.of_evalO ((Silmaril.Wasm.Abstract.evalO_closed_iff.2 h).mono closedCall_le_closedCallX)

theorem eval_of_evalOX {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) {r : Store H × Frame × Flow}
    (h : EvalOX closedCallX s f stk es r) : Eval s f stk es r :=
  Silmaril.Wasm.Abstract.evalO_closed_iff.1 ((evalOX_closed_iff hs hx).1 h)

theorem funcs_of_evalOX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX closedCallX s f stk es r) : r.1.funcs = s.funcs :=
  evalOX_funcs (fun _ _ _ _ h => closedCallX_funcs h) h

theorem xFree_body {s : Store H} (hs : StoreXFree s) {f : Frame} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} {fn : Func} (hfi : s.func? f x = some (a, fi)) (hcode : fi.code = .wasm fn) :
    xFreeL (liftInstrs fn.body) = true :=
  hs a fi fn (Silmaril.Wasm.Abstract.funcs_of_func? hfi) hcode

/-- Direct problems: a direct store and direct code. -/
def Direct (X : Problem H) : Problem H := fun s f stk es => StoreXFree s ∧ xFreeL es = true ∧ X s f stk es

/-- A native unfolding of a direct problem is an extended one. -/
theorem stepX_of_step {X Y : Problem H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (hs : StoreXFree s) (hx : xFreeL es = true) (h : DivStep X Y s f stk es) :
    DivStepX (Direct X) (Direct Y) s f stk es := by
  cases h with
  | args h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .args ⟨hs, hx.1.2, h⟩
  | callee hargs hfi hcode hty h =>
    have d := evalOX_of_eval hargs
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX d) hs
    exact .callee d hfi hcode hty ⟨hs₁, xFree_body hs₁ hfi hcode, h⟩
  | callRet hargs hfi hcode hty hbody hvs h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have d := evalOX_of_eval hargs
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX d) hs
    have db := evalOX_of_eval hbody
    exact .callRet d hfi hcode hty db hvs ⟨storeXFree_of_funcs (funcs_of_evalOX db) hs₁, hx.2, h⟩
  | opK hi hargs hflat h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have d := evalOX_of_eval hargs
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX d) hs
    exact .opK hi d hflat ⟨storeXFree_of_funcs (evalFlat_funcs hflat) hs₁, hx.2, h⟩
  | block har h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .block har ⟨hs, hx.1, h⟩
  | blockK har hbody hvs h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have d := evalOX_of_eval hbody
    exact .blockK har d hvs ⟨storeXFree_of_funcs (funcs_of_evalOX d) hs, hx.2, h⟩
  | loop har h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loop har ⟨hs, hx.1, h⟩
  | loopK har hbody h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have d := evalOX_of_eval hbody
    exact .loopK har d ⟨storeXFree_of_funcs (funcs_of_evalOX d) hs, hx.2, h⟩
  | loopBack har hbody h =>
    have d := evalOX_of_eval hbody
    exact .loopBack har d ⟨storeXFree_of_funcs (funcs_of_evalOX d) hs, hx, h⟩
  | cond h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .cond ⟨hs, hx.1.1.1, h⟩
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr hc hb har h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have d := evalOX_of_eval hc
    exact .arm d hb har ⟨storeXFree_of_funcs (funcs_of_evalOX d) hs,
      by cases b <;> simp [hx.1.1.2, hx.1.2], h⟩
  | ifK hc hb har harm hvs h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have d := evalOX_of_eval hc
    have da := evalOX_of_eval harm
    exact .ifK d hb har da hvs ⟨storeXFree_of_funcs ((funcs_of_evalOX da).trans
      (funcs_of_evalOX d)) hs, hx.2, h⟩

/-- An extended unfolding of a direct problem is a native one. -/
theorem step_of_stepX {X Y : Problem H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (hs : StoreXFree s) (hx : xFreeL es = true) (h : DivStepX X Y s f stk es) :
    DivStep (Direct X) (Direct Y) s f stk es := by
  cases h with
  | args h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .args ⟨hs, hx.1.2, h⟩
  | callee hargs hfi hcode hty h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX hargs) hs
    exact .callee (eval_of_evalOX hs hx.1.2 hargs) hfi hcode hty
      ⟨hs₁, xFree_body hs₁ hfi hcode, h⟩
  | callRet hargs hfi hcode hty hbody hvs h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX hargs) hs
    exact .callRet (eval_of_evalOX hs hx.1.2 hargs) hfi hcode hty
      (eval_of_evalOX hs₁ (xFree_body hs₁ hfi hcode) hbody) hvs
      ⟨storeXFree_of_funcs (funcs_of_evalOX hbody) hs₁, hx.2, h⟩
  | opK hi hargs hflat h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX hargs) hs
    exact .opK hi (eval_of_evalOX hs hx.1.2 hargs) hflat
      ⟨storeXFree_of_funcs (evalFlat_funcs hflat) hs₁, hx.2, h⟩
  | block har h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .block har ⟨hs, hx.1, h⟩
  | blockK har hbody hvs h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockK har (eval_of_evalOX hs hx.1 hbody) hvs
      ⟨storeXFree_of_funcs (funcs_of_evalOX hbody) hs, hx.2, h⟩
  | loop har h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loop har ⟨hs, hx.1, h⟩
  | loopK har hbody h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopK har (eval_of_evalOX hs hx.1 hbody)
      ⟨storeXFree_of_funcs (funcs_of_evalOX hbody) hs, hx.2, h⟩
  | loopBack har hbody h =>
    have hx' := hx
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx'
    exact .loopBack har (eval_of_evalOX hs hx'.1 hbody)
      ⟨storeXFree_of_funcs (funcs_of_evalOX hbody) hs, hx, h⟩
  | cond h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .cond ⟨hs, hx.1.1.1, h⟩
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr hc hb har h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .arm (eval_of_evalOX hs hx.1.1.1 hc) hb har ⟨storeXFree_of_funcs (funcs_of_evalOX hc) hs,
      by cases b <;> simp [hx.1.1.2, hx.1.2], h⟩
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl hc hb har harm hvs h =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (funcs_of_evalOX hc) hs
    have hxa : xFreeL (if b then t else el) = true := by cases b <;> simp [hx.1.1.2, hx.1.2]
    exact .ifK (eval_of_evalOX hs hx.1.1.1 hc) hb har (eval_of_evalOX hs₁ hxa harm) hvs
      ⟨storeXFree_of_funcs (funcs_of_evalOX harm) hs₁, hx.2, h⟩
  | callIndCallee => simp [xFreeL, xFree, isXCall] at hx
  | callIndRet => simp [xFreeL, xFree, isXCall] at hx
  | callRefCallee => simp [xFreeL, xFree, isXCall] at hx
  | callRefRet => simp [xFreeL, xFree, isXCall] at hx
  | tailCallee _ hres =>
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [isXCall_of_tailRes hres] at hx

theorem evalDivX_of_evalDiv {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) (h : EvalDiv s f stk es) : EvalDivX s f stk es :=
  evalDivX_coind (X := Direct EvalDiv) (fun _ _ _ _ ⟨hs, hx, h⟩ =>
    stepX_of_step hs hx (Silmaril.Wasm.Interp.evalDiv_iff_step.1 h)) _ _ _ _ ⟨hs, hx, h⟩

theorem evalDiv_of_evalDivX {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) (h : EvalDivX s f stk es) : EvalDiv s f stk es :=
  Silmaril.Wasm.Interp.evalDiv_of_coind (X := Direct EvalDivX) (fun _ _ _ _ ⟨hs, hx, h⟩ =>
    step_of_stepX hs hx (evalDivX_unfold.1 h)) _ _ _ _ ⟨hs, hx, h⟩

theorem direct_bot : Direct (⊥ : Problem H) = ⊥ := by
  funext s f stk es
  exact propext ⟨fun h => h.2.2, fun h => h.elim⟩

theorem localDivX_of_localDiv {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) (h : LocalDiv s f stk es) : LocalDivX s f stk es :=
  localDivX_coind (X := Direct LocalDiv) (fun _ _ _ _ ⟨hs, hx, h⟩ => by
    have := stepX_of_step hs hx (Silmaril.Wasm.Interp.localDiv_iff_step.1 h)
    rwa [direct_bot] at this) _ _ _ _ ⟨hs, hx, h⟩

theorem localDiv_of_localDivX {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) (h : LocalDivX s f stk es) : LocalDiv s f stk es :=
  Silmaril.Wasm.Interp.localDiv_of_coind (X := Direct LocalDivX) (fun _ _ _ _ ⟨hs, hx, h⟩ => by
    have := step_of_stepX hs hx (localDivX_unfold.1 h)
    rwa [direct_bot] at this) _ _ _ _ ⟨hs, hx, h⟩

end Silmaril.Proofs.Wasm.Abstract.XDiverge
