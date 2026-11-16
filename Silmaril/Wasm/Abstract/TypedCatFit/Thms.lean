module

public import Silmaril.Wasm.Abstract.TypedCat.Thms
import Silmaril.Proofs.Wasm.Abstract.TypedCatFit.Tensor
import Silmaril.Proofs.Wasm.Abstract.TypedCatFit.Central

/-!
# The closure as an oracle for the typed tensor, without `fitP`

`TypedCat` (#543) proves the answered stack tensor for typed code under the closure restricted to
calls passing the callee's parameter count (`tmor_tensor_fitClosed`, oracle
`fitP closedCallXP`), because the closure's Core 3.0 soundness (`PendSim.closedCallXP_sound`), and
so its arity respect (`arityResp_fitClosed`), is stated for that count only. This topic removes the
restriction.

**Coincidence.** Checked code calls with exactly the callee's parameter count: at every call site
(`call`, `call_indirect`, `call_ref`, in their returning, trapping and throwing forms) the check
has at least the callee's parameter count on the stack, so the arguments `stk₁.take ps.length`
have that length. Carrying the check's result invariant along the run needs only that *fitting*
answers respect arities. So, for any oracle `C` with `ArityResp Γ (fitP C)`, on checked code from a
store agreeing with `Γ` the runs of `EvalOXP C` are exactly those of `EvalOXP (fitP C)`
(`evalOXP_fit_iff`; on typed code at a typed state, `tmor_fit_iff`). Tail calls are not answered
by `EvalOXP` (they are pending until the frame is left), so they need nothing here.

**Consequences for `C` itself:** the result invariant (`evalOXP_goodO_fit`), the answered tensor
(`evalOXP_tensor_fit`), and its typed and relational forms (`tmor_tensor_fit`,
`tmor_tensorR_fit`, `tmor_tensorR_comp_fit`), all under `ArityResp Γ (fitP C)` only.

**The closure.** `ArityResp Γ (fitP closedCallXP)` holds (`TypedCat.arityResp_fitClosed`), so
the closure `closedCallXP` itself, with no restriction, coincides with its fitting restriction on
checked code (`evalOXP_closed_iff_fit`, `tmor_closed_iff_fit`) and is an oracle for the typed
tensor (`tmor_tensor_closed`, `tmor_tensorR_closed`, `tmor_tensorR_comp_closed`), at every typed
state, with no premise beyond typing. `ArityResp Γ closedCallXP` (an answer for **every** argument
list) is not claimed: the coincidence is what checked code needs.

**Central morphisms against typed morphisms, both sides.** `TypedCat.interchange_of_pure` puts a
pure morphism (`PureAt`) on top of an arbitrary relation; `thom_interchange_pure_above_closed`
instantiates it with typed code under the closure below. With the pure morphism **below**
(`rightR`) the interchange is not an equation of relations on all stacks (`PureAt` fixes the pure
morphism only at its height, and the morphism on top must land at the height the right
whiskering expects), so it is stated at a state: `interchange_pure_below` for any `g₁` falling
through at a fixed height `n'` on a stack of height `n + m`, and `thom_interchange_pure_below`
(any oracle with `ArityResp Γ (fitP C)`) and `thom_interchange_pure_below_closed` (the closure)
for typed code `I ⟶ J` on top, at a typed state with `m` passive values below.
-/

public section

namespace Silmaril.Wasm.Abstract.TypedCatFit

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type} {Γ : Ctx H} {C : Abstract.CallRel H}

/-! ## Coincidence with the fitting restriction -/

/-- **Checked code makes only fitting calls**: its runs under `C` are its runs under `fitP C`,
when fitting answers respect arities. -/
theorem evalOXP_fit_iff (hC : ArityResp Γ (fitP C)) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {labels : List Nat} {ret : Nat} {oc : Option Nat} (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) (r : Store H × Frame × POut) :
    EvalOXP C s f stk es r ↔ EvalOXP (fitP C) s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.evalOXP_fit_iff hC hg hc r

/-- **Typed code makes only fitting calls**, at every typed state. -/
theorem tmor_fit_iff (hC : ArityResp Γ (fitP C)) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (r : Store H × Frame × POut) :
    EvalOXP C s f stk es r ↔ EvalOXP (fitP C) s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.tmor_fit_iff hC hm hr r

/-! ## Arity respect on fitting calls suffices -/

/-- The result invariant of a checked run under `C`. -/
theorem evalOXP_goodO_fit (hC : ArityResp Γ (fitP C)) {s s' : Store H} {f f' : Frame}
    {stk : List Val} {es : List BExpr} {o : POut} {labels : List Nat} {ret : Nat}
    {oc : Option Nat} (d : EvalOXP C s f stk es (s', f', o)) (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO labels ret oc o :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.evalOXP_goodO_fit hC d hg hc

/-- **The answered stack tensor under `C`**, for checked code. -/
theorem evalOXP_tensor_fit (hC : ArityResp Γ (fitP C)) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {labels : List Nat} {ret : Nat} {oc : Option Nat}
    (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.evalOXP_tensor_fit hC hg hc rest s' f' X

/-- **The answered tensor for typed code under `C`.** -/
theorem tmor_tensor_fit (hC : ArityResp Γ (fitP C)) {I J : TIface} {ft : Bool}
    {es : List BExpr} (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.tmor_tensor_fit hC hm hr rest s' f' X

/-- **The answered tensor under `C`, relationally.** -/
theorem tmor_tensorR_fit (hC : ArityResp Γ (fitP C)) {I J : TIface} {ft : Bool}
    {es : List BExpr} (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest) s' f' X :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.tmor_tensorR_fit hC hm hr rest s' f' X

/-- **Whiskering preserves composition** of typed code under `C`. -/
theorem tmor_tensorR_comp_fit (hC : ArityResp Γ (fitP C)) {I J K : TIface} {ft : Bool}
    {es₁ es₂ : List BExpr} (h₁ : THom Γ I J es₁) (h₂ : TMor Γ J K ft es₂) {s : Store H}
    {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H)
    (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C (es₁ ++ es₂)) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (seqR (whiskR rest (denR C es₁)) (whiskR rest (denR C es₂)))
        s f (stk ++ rest) s' f' X :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.tmor_tensorR_comp_fit hC h₁ h₂ hr rest s' f' X

/-! ## The closure, unrestricted -/

/-- **The closure coincides with its fitting restriction** on checked code. -/
theorem evalOXP_closed_iff_fit {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {labels : List Nat} {ret : Nat} {oc : Option Nat} (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) (r : Store H × Frame × POut) :
    EvalOXP closedCallXP s f stk es r ↔ EvalOXP (fitP closedCallXP) s f stk es r :=
  evalOXP_fit_iff (arityResp_fitClosed Γ) hg hc r

/-- **The closure coincides with its fitting restriction** on typed code at typed states. -/
theorem tmor_closed_iff_fit {I J : TIface} {ft : Bool} {es : List BExpr} (hm : TMor Γ I J ft es)
    {s : Store H} {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk)
    (r : Store H × Frame × POut) :
    EvalOXP closedCallXP s f stk es r ↔ EvalOXP (fitP closedCallXP) s f stk es r :=
  tmor_fit_iff (arityResp_fitClosed Γ) hm hr r

/-- The result invariant of a checked closed run. -/
theorem evalOXP_goodO_closed {s s' : Store H} {f f' : Frame} {stk : List Val} {es : List BExpr}
    {o : POut} {labels : List Nat} {ret : Nat} {oc : Option Nat}
    (d : EvalOXP closedCallXP s f stk es (s', f', o)) (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO labels ret oc o :=
  evalOXP_goodO_fit (arityResp_fitClosed Γ) d hg hc

/-- **The answered stack tensor under the closure**, for checked code. -/
theorem evalOXP_tensor_closed {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {labels : List Nat} {ret : Nat} {oc : Option Nat} (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP closedCallXP s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X) ↔
      ∃ o, EvalOXP closedCallXP s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X :=
  evalOXP_tensor_fit (arityResp_fitClosed Γ) hg hc rest s' f' X

/-- **The answered tensor for typed code under the closure**, no `fitP`, no further premise. -/
theorem tmor_tensor_closed {I J : TIface} {ft : Bool} {es : List BExpr} (hm : TMor Γ I J ft es)
    {s : Store H} {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) (rest : List Val)
    (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP closedCallXP s f (stk ++ rest) es (s', f', o') ∧
        trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP closedCallXP s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  tmor_tensor_fit (arityResp_fitClosed Γ) hm hr rest s' f' X

/-- **The answered tensor under the closure, relationally.** -/
theorem tmor_tensorR_closed {I J : TIface} {ft : Bool} {es : List BExpr} (hm : TMor Γ I J ft es)
    {s : Store H} {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) (rest : List Val)
    (s' : Store H) (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR closedCallXP es) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (whiskR rest (denR closedCallXP es)) s f (stk ++ rest) s' f'
        X :=
  tmor_tensorR_fit (arityResp_fitClosed Γ) hm hr rest s' f' X

/-- **Whiskering preserves composition** of typed code under the closure. -/
theorem tmor_tensorR_comp_closed {I J K : TIface} {ft : Bool} {es₁ es₂ : List BExpr}
    (h₁ : THom Γ I J es₁) (h₂ : TMor Γ J K ft es₂) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR closedCallXP (es₁ ++ es₂)) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret
        (seqR (whiskR rest (denR closedCallXP es₁)) (whiskR rest (denR closedCallXP es₂)))
        s f (stk ++ rest) s' f' X :=
  tmor_tensorR_comp_fit (arityResp_fitClosed Γ) h₁ h₂ hr rest s' f' X

/-! ## Central morphisms against typed morphisms -/

section Central

variable {m m' n n' : Nat} {ψ φ : List Val → List Val} {g₁ g₂ : ORel H}

/-- **A pure morphism below commutes with a morphism on top** falling through at a fixed height,
at a stack of height `n + m`. -/
theorem interchange_pure_below (hp : PureAt m m' ψ g₂) {s : Store H} {f : Frame}
    {stk : List Val} (hl : stk.length = n + m)
    (hh : ∀ s' f' vs, g₁ s f (stk.take n) s' f' (.flow (.normal vs)) → vs.length = n')
    (s' : Store H) (f' : Frame) (o : POut) :
    seqR (leftR n g₁) (rightR n' g₂) s f stk s' f' o ↔
      seqR (rightR n g₂) (leftR n g₁) s f stk s' f' o :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.interchange_pure_below hp hl hh s' f' o

/-- **A pure morphism below commutes with typed code on top**, at a typed state. -/
theorem thom_interchange_pure_below (hC : ArityResp Γ (fitP C)) {I J : TIface}
    {es : List BExpr} (hm : THom Γ I J es) {s : Store H} {f : Frame} {top : List Val}
    (hr : Realizes Γ I s f top) (hp : PureAt m m' ψ g₂) (bot : List Val) (hb : bot.length = m)
    (s' : Store H) (f' : Frame) (o : POut) :
    seqR (leftR I.ts.length (denR C es)) (rightR J.ts.length g₂) s f (top ++ bot) s' f' o ↔
      seqR (rightR I.ts.length g₂) (leftR I.ts.length (denR C es)) s f (top ++ bot) s' f' o :=
  Silmaril.Proofs.Wasm.Abstract.TypedCatFit.thom_interchange_pure_below hC hm hr hp bot hb s' f' o

/-- **A pure morphism below commutes with typed code under the closure on top.** -/
theorem thom_interchange_pure_below_closed {I J : TIface} {es : List BExpr}
    (hm : THom Γ I J es) {s : Store H} {f : Frame} {top : List Val}
    (hr : Realizes Γ I s f top) (hp : PureAt m m' ψ g₂) (bot : List Val) (hb : bot.length = m)
    (s' : Store H) (f' : Frame) (o : POut) :
    seqR (leftR I.ts.length (denR closedCallXP es)) (rightR J.ts.length g₂) s f (top ++ bot) s'
        f' o ↔
      seqR (rightR I.ts.length g₂) (leftR I.ts.length (denR closedCallXP es)) s f (top ++ bot) s'
        f' o :=
  thom_interchange_pure_below (arityResp_fitClosed Γ) hm hr hp bot hb s' f' o

/-- **A pure morphism on top commutes with any code under the closure below.** -/
theorem thom_interchange_pure_above_closed (hp : PureAt n n' φ g₁) (es : List BExpr) :
    Interchange n n' g₁ (denR (closedCallXP (H := H)) es) :=
  interchange_of_pure hp _

end Central

end Silmaril.Wasm.Abstract.TypedCatFit
