module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackWhole
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Cut

/-!
# Resolved logged runs and closed behaviours as Core runs to a final form (proofs)

For the divergent backward simulation (`HostClosingInfXPBack`), every profile:

* `res_evRun`: a logged canonical run of checked code whose log is resolved against the closure,
  by returning callees or up to a trapping callee (`ResX` without its flow side condition), is a
  Core run with exactly the resolved log to a final form;
* `close_evRun_call`: a closed behaviour of a call with a consistent log is a Core run of the call,
  in any frame and any `call_ref` form, with exactly that log to a final form (values, an
  exception or a trap).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {tags : List TagInst}

/-- **A resolved logged run is a Core run with exactly its resolved log to a final form.** -/
theorem res_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs : List (Call (wasmHostSig H))}
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hd : EvalLXPh s f stk es l r) (hres : Shape.SubstPre Cl (l.map OCall.lift) cs ∨ TrapRes l cs)
    (hcons : Cons host cs) (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out) :
    ∃ (s' : Store H) (f' : Frame) (c' : List Admin) (oc : Outcome),
      EvRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs
        ⟨s', f', c'⟩ ∧ oc.Ends c' := by
  rcases hres with hq | ⟨l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, hq₁, htr, rfl⟩
  · obtain ⟨-, -, -, cl⟩ := full_run (P := P) hH hE hd
      (substPre_mono (close_le_goodCX hH hE) hq) hcons hts
    obtain ⟨s', f', c', oc, hrun, he, -⟩ := cl hS hc
    exact ⟨s', f', c', oc, hrun, he⟩
  · rw [cons_append] at hcons
    have hz := trapAt_of_trapC (P := P) (ans := (b, s₂))
      (close_le_trapC (tags := tags) (P := P) hH hE g s₁ args htr) hcons.2
    have cl : CoreLT tags P host s f stk es (q₁ ++ c₁) (fun _ => True) :=
      evalLXPh_trap (P := P) hH hE hd l₁ _ l₂ rfl q₁ c₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hz (cons_append.2 hcons) hts
    obtain ⟨s', f', c', oc, hrun, he, -⟩ := cl hS hc
    exact ⟨s', f', c', oc, hrun, he⟩

/-- **A closed behaviour of a call is a Core run of the call to a final form**, with exactly its
log, in any frame and any `call_ref` form. -/
theorem close_evRun_call (hH : NativeHostSlice host) (hE : HostSliceE tags host) {a : Nat}
    {s : Store H} {us : List Val} {c₁ : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, e) ∈ Shape.close wasmHOpenXP a s us) (hc : Cons host c₁)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (f : Frame) (cr : Admin) (hcr : cr.IsCallRef) :
    ∃ (s' : Store H) (code : List Admin) (oc : Outcome), oc.Ends code ∧
      EvRun P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ c₁ ⟨s', f, code⟩ := by
  rcases e with ⟨b, s₂⟩ | _ | _
  · have h := close_ret_evRun (P := P) hH hE hm hc hts hS hfi hty hn f cr hcr
    rcases b with ws | t
    · exact ⟨s₂, _, .normal ws, rfl, h⟩
    · exact ⟨s₂, _, .throw t, rfl, h⟩
  · obtain ⟨s', -, h⟩ := close_trap_evRun (P := P) hH hE hm hc hts hS hfi hty hn f cr hcr
    exact ⟨s', _, .trap, rfl, h⟩
  · exact (close_ne_div hm).elim

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
