module

public import Silmaril.Proofs.Wasm.Cfg.CallGuard
public import Silmaril.Proofs.Wasm.Cfg.MachineTail

@[expose] public section

/-!
# Host-free region runs keep the store's functions (proofs)

Without a host, Core steps never change the store's function list (`steps_funcs_closed`). So
along a host-free region run, every store has the function list `F` of the start, provided the
oracle's answers keep it (`runC_funcs`); and every call the run makes is made from a store with
the list `F`. An oracle `C` can then be replaced by any `C'` that agrees with it on stores with
the list `F`. This is stated for the host-free semantics only (host calls may change the store).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

local notation "NH" => (fun _ _ _ _ => False : HostSemantics H)

/-- **A host-free region run keeps the store's function list `F` and only calls from stores with
it**: with an oracle `C` whose answers from stores with `F` are answers of `C'` keeping `F`, a run
with `C` from a store with `F` is a run with `C'`, ending in a store with `F`. -/
theorem runC_funcs {C C' : Abstract.CallRel H} {F : List (FuncInst H)}
    (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
    {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Out}
    (h : RunC P NH C s f vs code s' f' o) (hI : s.funcs = F) :
    RunC P NH C' s f vs code s' f' o ∧ s'.funcs = F := by
  induction h with
  | nil => exact ⟨.nil, hI⟩
  | val hv _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.val hv r, e⟩
  | simple hi h₁ _ ih =>
    obtain ⟨r, e⟩ := ih ((steps_funcs_closed h₁).trans hI); exact ⟨.simple hi h₁ r, e⟩
  | simpleTrap hi h₁ => exact ⟨.simpleTrap hi h₁, (steps_funcs_closed h₁).trans hI⟩
  | trap => exact ⟨.trap, hI⟩
  | br => exact ⟨.br, hI⟩
  | ret => exact ⟨.ret, hI⟩
  | brIf _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.brIf r, e⟩
  | throw ht he hn => exact ⟨.throw ht he hn, by simpa [Store.addExn] using hI⟩
  | throwRefNull => exact ⟨.throwRefNull, hI⟩
  | throwRefExn => exact ⟨.throwRefExn, hI⟩
  | tryTable hbt hm _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.tryTable hbt hm r, e⟩
  | labelThrow _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.labelThrow r, e⟩
  | handlerNormal _ _ ih₁ ih₂ =>
    obtain ⟨r₁, e₁⟩ := ih₁ hI; obtain ⟨r₂, e₂⟩ := ih₂ e₁; exact ⟨.handlerNormal r₁ r₂, e₂⟩
  | handlerBr _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerBr r, e⟩
  | handlerRet _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerRet r, e⟩
  | handlerTrap _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerTrap r, e⟩
  | handlerCatch _ hc ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerCatch r hc, e⟩
  | handlerRethrow _ hc ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerRethrow r hc, e⟩
  | brData hb _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.brData hb r, e⟩
  | block hbt hm _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.block hbt hm r, e⟩
  | loop hbt hm _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.loop hbt hm r, e⟩
  | if_ _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.if_ r, e⟩
  | labelNormal _ _ ih₁ ih₂ =>
    obtain ⟨r₁, e₁⟩ := ih₁ hI; obtain ⟨r₂, e₂⟩ := ih₂ e₁; exact ⟨.labelNormal r₁ r₂, e₂⟩
  | labelBr0 _ hn _ ih₁ ih₂ =>
    obtain ⟨r₁, e₁⟩ := ih₁ hI; obtain ⟨r₂, e₂⟩ := ih₂ e₁; exact ⟨.labelBr0 r₁ hn r₂, e₂⟩
  | labelBrSucc _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.labelBrSucc r, e⟩
  | labelRet _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.labelRet r, e⟩
  | labelTrap _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.labelTrap r, e⟩
  | returnCall hfi => exact ⟨.returnCall hfi, hI⟩
  | returnCallRef hc => exact ⟨.returnCallRef hc, hI⟩
  | returnCallRefNull hc => exact ⟨.returnCallRefNull hc, hI⟩
  | returnCallIndirect _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.returnCallIndirect r, e⟩
  | labelTail _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.labelTail r, e⟩
  | labelTailNull _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.labelTailNull r, e⟩
  | handlerTail _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerTail r, e⟩
  | handlerTailNull _ ih => obtain ⟨r, e⟩ := ih hI; exact ⟨.handlerTailNull r, e⟩
  | call hfi hty hn hcall hvs _ ih =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; obtain ⟨r, e⟩ := ih e₁
    exact ⟨.call hfi hty hn hc hvs r, e⟩
  | callTrap hfi hty hn hcall =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; exact ⟨.callTrap hfi hty hn hc, e₁⟩
  | callThrow hfi hty hn hcall =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; exact ⟨.callThrow hfi hty hn hc, e₁⟩
  | callInd hres hfi hty hn hcall hvs _ ih =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; obtain ⟨r, e⟩ := ih e₁
    exact ⟨.callInd hres hfi hty hn hc hvs r, e⟩
  | callIndTrap hres hfi hty hn hcall =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; exact ⟨.callIndTrap hres hfi hty hn hc, e₁⟩
  | callIndThrow hres hfi hty hn hcall =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; exact ⟨.callIndThrow hres hfi hty hn hc, e₁⟩
  | callIndRes hres => exact ⟨.callIndRes hres, hI⟩
  | callRef hfi hty hn hcall hvs _ ih =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; obtain ⟨r, e⟩ := ih e₁
    exact ⟨.callRef hfi hty hn hc hvs r, e⟩
  | callRefTrap hfi hty hn hcall =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; exact ⟨.callRefTrap hfi hty hn hc, e₁⟩
  | callRefThrow hfi hty hn hcall =>
    obtain ⟨hc, e₁⟩ := hC _ _ _ _ hI hcall; exact ⟨.callRefThrow hfi hty hn hc, e₁⟩
  | callRefNull => exact ⟨.callRefNull, hI⟩

/-- The store of a state a tail call's answer reaches. -/
theorem tailEnd_store {rs : Nat} {s : Store H} {f : Frame} {fl : Binaryen.Flow}
    {st : Machine.MState H} (h : Machine.tailEnd rs s f fl = some st) : st.store = s :=
  (Proofs.Machine.codeOf_tailEnd (body := []) h).1

open Silmaril.Wasm.Cfg.Machine in
/-- **A host-free machine step keeps the store's function list `F`**, and is a step with any
oracle `C'` that agrees with `C` on stores with `F` (as in `runC_funcs`). -/
theorem mstepC_funcs {C C' : Abstract.CallRel H} {F : List (FuncInst H)}
    (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
    {body : Expr} {st st' : MState H} (h : MStepC P NH C body st st') (hI : st.store.funcs = F) :
    MStepC P NH C' body st st' ∧ st'.store.funcs = F := by
  cases h with
  | fall hb ht hr =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.fall hb ht r, by simpa [goto] using e⟩
  | br hb ht hr hL ha hl =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.br hb ht r hL ha hl, by first | simpa [goto] using e | (split <;> simpa [goto] using e)⟩
  | brIfTaken hb ht hr hk hL ha hl =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI
    exact ⟨.brIfTaken hb ht r hk hL ha hl, by first | simpa [goto] using e | (split <;> simpa [goto] using e)⟩
  | brIfNot hb ht hr =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.brIfNot hb ht r, by simpa [goto] using e⟩
  | brDataTaken hb ht hr hbs hL ha hl =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI
    exact ⟨.brDataTaken hb ht r hbs hL ha hl, by first | simpa [goto] using e | (split <;> simpa [goto] using e)⟩
  | brDataNot hb ht hr hbs =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.brDataNot hb ht r hbs, by simpa [goto] using e⟩
  | enter hb ht harm hkind hr hcond hbt hm =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI
    exact ⟨.enter hb ht harm hkind r hcond hbt hm, by simpa [goto] using e⟩
  | ret hb ht hr => obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.ret hb ht r, e⟩
  | brOut hb ht hr hL => obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.brOut hb ht r hL, e⟩
  | brIfOut hb ht hr hk hL =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.brIfOut hb ht r hk hL, e⟩
  | brDataOut hb ht hr hbs hL =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.brDataOut hb ht r hbs hL, e⟩
  | trap hb ht hr =>
    obtain ⟨stk₁, hr⟩ := hr
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.trap hb ht ⟨stk₁, r⟩, e⟩
  | termTrap hb ht hr hth =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; obtain ⟨r', e'⟩ := runC_funcs hC hth e
    exact ⟨.termTrap hb ht r r', e'⟩
  | bodyTrap hb hr => obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.bodyTrap hb r, e⟩
  | raise hb ht hi hr hth hT =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; obtain ⟨r', e'⟩ := runC_funcs hC hth e
    exact ⟨.raise hb ht hi r r' hT, e'⟩
  | catch_ hb ht hi hr hth hpass hL hT hc hL' ha hl =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; obtain ⟨r', e'⟩ := runC_funcs hC hth e
    exact ⟨.catch_ hb ht hi r r' hpass hL hT hc hL' ha hl, by first | simpa [goto] using e' | (split <;> simpa [goto] using e')⟩
  | bodyRaise hb hr hT => obtain ⟨r, e⟩ := runC_funcs hC hr hI; exact ⟨.bodyRaise hb r hT, e⟩
  | bodyCatch hb hr hpass hL hT hc hL' ha hl =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI
    exact ⟨.bodyCatch hb r hpass hL hT hc hL' ha hl, by first | simpa [goto] using e | (split <;> simpa [goto] using e)⟩
  | catchOut hb ht hi hr hth hpass hL hT hc hout =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; obtain ⟨r', e'⟩ := runC_funcs hC hth e
    exact ⟨.catchOut hb ht hi r r' hpass hL hT hc hout, e'⟩
  | bodyCatchOut hb hr hpass hL hT hc hout =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI
    exact ⟨.bodyCatchOut hb r hpass hL hT hc hout, e⟩
  | tailNull hb ht hi hr hth =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; obtain ⟨r', e'⟩ := runC_funcs hC hth e
    exact ⟨.tailNull hb ht hi r r', e'⟩
  | tail hb ht hi hr hth hfi hty hargs hn hcall hend =>
    obtain ⟨r, e⟩ := runC_funcs hC hr hI; obtain ⟨r', e'⟩ := runC_funcs hC hth e
    obtain ⟨hc, e''⟩ := hC _ _ _ _ e' hcall
    exact ⟨.tail hb ht hi r r' hfi hty hargs hn hc hend, by rw [tailEnd_store hend]; exact e''⟩

section Traces

open Silmaril.Wasm.Cfg.Machine

variable {C C' : Abstract.CallRel H} {F : List (FuncInst H)}
  (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
include hC

theorem mrun_funcs {body : Expr} {st st' : MState H}
    (h : Relation.ReflTransGen (MStepC P NH C body) st st') (hI : st.store.funcs = F) :
    Relation.ReflTransGen (MStepC P NH C' body) st st' ∧ st'.store.funcs = F := by
  induction h with
  | refl => exact ⟨.refl, hI⟩
  | tail _ hs ih =>
    obtain ⟨r, e⟩ := ih
    obtain ⟨hs', e'⟩ := mstepC_funcs hC hs e
    exact ⟨r.tail hs', e'⟩

theorem infinite_funcs {body : Expr} {st : MState H}
    (h : InfiniteTrace (MStepC P NH C body) st) (hI : st.store.funcs = F) :
    InfiniteTrace (MStepC P NH C' body) st := by
  refine InfiniteTrace.coinduct (fun x => InfiniteTrace (MStepC P NH C body) x ∧ x.store.funcs = F)
    ?_ ⟨h, hI⟩
  rintro x ⟨hx, ex⟩
  obtain ⟨y, hs, hy⟩ := hx.unfold
  obtain ⟨hs', ey⟩ := mstepC_funcs hC hs ex
  exact ⟨y, hs', hy, ey⟩

theorem bodyCallDiv_funcs {D : Store H → Nat → List Val → Prop} {body : Expr} {st : MState H}
    (h : BodyCallDiv P NH C D body st) (hI : st.store.funcs = F) :
    BodyCallDiv P NH C' D body st := by
  rcases h with ⟨b, sg, pre, post, x, s₁, f₁, ws, us, a, fi, ps, rs, hn, hb, hbody, hr, hfi, hty,
      hlen, hd⟩ |
    ⟨b, sg, pre, post, x, y, s₁, f₁, ws, us, ad, i, fa, fi, ps, rs, hn, hb, hbody, hr, hres, hfi,
      hty, hlen, hd⟩ |
    ⟨b, sg, pre, post, y, s₁, f₁, ws, us, fa, fi, ps, rs, hn, hb, hbody, hr, hfi, hty, hlen, hd⟩
  · exact .inl ⟨b, sg, pre, post, x, s₁, f₁, ws, us, a, fi, ps, rs, hn, hb, hbody,
      (runC_funcs hC hr hI).1, hfi, hty, hlen, hd⟩
  · exact .inr (.inl ⟨b, sg, pre, post, x, y, s₁, f₁, ws, us, ad, i, fa, fi, ps, rs, hn, hb, hbody,
      (runC_funcs hC hr hI).1, hres, hfi, hty, hlen, hd⟩)
  · exact .inr (.inr ⟨b, sg, pre, post, y, s₁, f₁, ws, us, fa, fi, ps, rs, hn, hb, hbody,
      (runC_funcs hC hr hI).1, hfi, hty, hlen, hd⟩)

theorem tailCallDiv_funcs {D : Store H → Nat → List Val → Prop} {body : Expr} {st : MState H}
    (h : TailCallDiv P NH C D body st) (hI : st.store.funcs = F) :
    TailCallDiv P NH C' D body st := by
  obtain ⟨b, sg, i, stk₁, s₁, s₂, f₁, f₂, W, a, c, fi, ps, rs, W₀, args, hn, hb, ht, hi, hr, hth,
    hfi, hty, hW, hlen, hd⟩ := h
  obtain ⟨r, e⟩ := runC_funcs hC hr hI
  exact ⟨b, sg, i, stk₁, s₁, s₂, f₁, f₂, W, a, c, fi, ps, rs, W₀, args, hn, hb, ht, hi, r,
    (runC_funcs hC hth e).1, hfi, hty, hW, hlen, hd⟩

/-- **Machine divergence with calls transfers between oracles that agree on stores with `F`**
(host-free). -/
theorem mdivC_funcs {D : Store H → Nat → List Val → Prop} {body : Expr} {st : MState H}
    (h : MDivC P NH C D body st) (hI : st.store.funcs = F) : MDivC P NH C' D body st := by
  rcases h with h | ⟨st', hrun, hd⟩
  · exact .inl (infinite_funcs hC h hI)
  · obtain ⟨r, e⟩ := mrun_funcs hC hrun hI
    exact .inr ⟨st', r, bodyCallDiv_funcs hC hd e⟩

/-- **Frame divergence transfers between oracles that agree on stores with `F`** (host-free). -/
theorem mdivT_funcs {D : Store H → Nat → List Val → Prop} {body : Expr} {st : MState H}
    (h : MDivT P NH C D body st) (hI : st.store.funcs = F) : MDivT P NH C' D body st := by
  rcases h with h | ⟨st', hrun, hd⟩
  · exact .inl (mdivC_funcs hC h hI)
  · obtain ⟨r, e⟩ := mrun_funcs hC hrun hI
    exact .inr ⟨st', r, tailCallDiv_funcs hC hd e⟩

end Traces

end Silmaril.Wasm.Cfg.Proofs.Region
