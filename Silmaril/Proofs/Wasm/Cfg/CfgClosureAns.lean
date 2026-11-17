module

public import Silmaril.Proofs.Wasm.Cfg.MachineLClose
public import Silmaril.Proofs.Wasm.Cfg.MachineLClosed

@[expose] public section

/-!
# Closed answers are session answers (H3, proofs)

The converse of `MachineLClose.closeOk_of_session`. `closed_goodS`: by least-fixpoint induction on
`closedCallXP`, every closed answer is a behaviour of the store-retaining session closure
`Shape.close wasmHOpenXPS` with the empty log: values (read at the callee's result arity), an
uncaught exception, or a trap, each in the answer's store. The callee's body run is a logged run
whose entries are good answers (`MachineLClosed.closed_logged`), so it resolves to the empty log
(`subst_of_res`); a pending tail call is answered by the tail callee's good answer, whose result
arity is the tail call's (`MachineLClose.evalLXPS_tail_wf`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgClosureAns

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall wasmHShapeS wasmHOpenXPS wasmEvFunXPS endOfFlowS
  tailAnsS exitFlow ansFlow CallRel)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP FrameP bodyCallXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP bodyCallXPOp)

variable {H : Type}

/-- The store-retaining session closure. -/
abbrev ClS : (wasmHShapeS H).ClosedMod := Shape.close wasmHOpenXPS

/-- **An answer the session closure gives with the empty log**: values read at the callee's
result arity, an uncaught exception, a trap, each in the answer's store. -/
def GoodS : CallRel H := fun s a us out =>
  (∀ vs, out.2.retVals = some vs → ∀ (fi : FuncInst H) (ps rs : List Validation.CValType),
    s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    (([] : List (Call (Abstract.wasmHostSig H))),
      End.ret (.inl (.inl (vs.take rs.length).reverse)) out.1) ∈ ClS a s us) ∧
  (∀ t, out.2 = .throw t →
    (([] : List (Call (Abstract.wasmHostSig H))), End.ret (.inl (.inr t)) out.1) ∈ ClS a s us) ∧
  (out.2 = .trap →
    (([] : List (Call (Abstract.wasmHostSig H))), End.ret (.inr ()) out.1) ∈ ClS a s us)

theorem closeOk_mono {C C' : CallRel H} (hC : C ≤ C') : ∀ {e : SCall H}, CloseOk C e →
    CloseOk C' e
  | ⟨.inr ⟨_, (_, _)⟩, (.inl (.inl _), _)⟩, ⟨fi, ps, rs, fl, vs, hfi, hty, hc, hv, hw⟩ =>
    ⟨fi, ps, rs, fl, vs, hfi, hty, hC _ _ _ _ hc, hv, hw⟩
  | ⟨.inr ⟨_, (_, _)⟩, (.inl (.inr _), _)⟩, h => hC _ _ _ _ h
  | ⟨.inr ⟨_, (_, _)⟩, (.inr _, _)⟩, h => hC _ _ _ _ h
  | ⟨.inl _, _⟩, h => h.elim

/-- **A good-answered entry is resolved by the session closure with the empty log.** -/
theorem closeOk_res : ∀ {e : SCall H}, CloseOk GoodS e →
    ∃ (g : Nat) (a : List Val) (s : Store H) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}) (s' : Store H),
      e = SCall.mk g a s b s' ∧ (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s') ∈
        ClS g s a 
  | ⟨.inr ⟨g, (a, s)⟩, (.inl (.inl _), s')⟩, ⟨fi, ps, rs, _, vs, hfi, hty, hc, hv, hw⟩ => by
    subst hw
    exact ⟨g, a, s, _, s', rfl, hc.1 vs hv fi ps rs hfi hty⟩
  | ⟨.inr ⟨g, (a, s)⟩, (.inl (.inr t), s')⟩, h =>
    ⟨g, a, s, _, s', rfl, (show GoodS s g a (s', .throw t) from h).2.1 t rfl⟩
  | ⟨.inr ⟨g, (a, s)⟩, (.inr (), s')⟩, h =>
    ⟨g, a, s, _, s', rfl, (show GoodS s g a (s', .trap) from h).2.2 rfl⟩
  | ⟨.inl _, _⟩, h => h.elim

/-- **A log of resolved internal calls resolves to the empty log**, keeping the end. -/
theorem subst_of_res : ∀ (l : List (SCall H)),
    (∀ z ∈ l, ∃ (g : Nat) (a : List Val) (s : Store H) (b : (List Val ⊕ Nat) ⊕ PUnit.{1})
      (s' : Store H), z = SCall.mk g a s b s' ∧
        (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s') ∈ ClS g s a) →
    ∀ e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1}), Shape.Subst ClS l e ([], e)
  | [], _, e => Shape.Subst.nil (c := ClS) e
  | z :: l, h, e => by
    obtain ⟨g, a, s, b, s', rfl, hz⟩ := h z (List.mem_cons_self ..)
    have := Shape.Subst.int (c := ClS) hz
      (subst_of_res l (fun z hz => h z (List.mem_cons_of_mem _ hz)) e)
    simpa [SCall.mk] using this

theorem close_of_open {a : Nat} {s : Store H} {us : List Val}
    {x : CallBeh ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self) (Store H)
      ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hx : x ∈ wasmHOpenXPS a s us) (hs : Shape.Subst ClS x.1 x.2 y) : y ∈ ClS a s us := by
  show y ∈ Shape.close wasmHOpenXPS a s us
  rw [← Shape.resolve_close]
  exact ⟨x, hx, hs⟩

theorem exitFlow_retVals {fl : Flow} {vs : List Val} (n : Nat) (h : fl.retVals = some vs) :
    exitFlow n fl = some (.normal (vs.take n).reverse) := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | t <;> simp_all [Flow.retVals, exitFlow]

/-- **One round of answering calls by good answers gives good answers.** -/
theorem body_goodS {s : Store H} {a : Nat} {us : List Val} {out : Store H × Flow}
    (h : bodyCallXP GoodS s a us out) : GoodS s a us out := by
  obtain ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, hbody, hfr⟩ := h
  obtain ⟨l, hL, hok⟩ := MachineLClosed.closed_logged hbody
  have hres := subst_of_res l (fun z hz => closeOk_res (hok z hz))
  cases hfr with
  | @flow _ bfl =>
    refine ⟨fun vs hvs fi' ps' rs' hfi' hty' => ?_, fun t ht => ?_, fun ht => ?_⟩
    · rw [hfi] at hfi'; cases hfi'
      rw [hty] at hty'; cases hty'
      exact close_of_open (.inl ⟨fi, fn, ps, rs, s₁, f₂, bfl, _, l, hfi, hcode, hty, hL,
        exitFlow_retVals rs.length hvs, rfl⟩) (hres _)
    · simp only at ht; subst ht
      exact close_of_open (.inl ⟨fi, fn, ps, rs, s₁, f₂, .throw t, .throw t, l, hfi, hcode, hty,
        hL, rfl, rfl⟩) (hres _)
    · simp only at ht; subst ht
      exact close_of_open (.inl ⟨fi, fn, ps, rs, s₁, f₂, .trap, .trap, l, hfi, hcode, hty,
        hL, rfl, rfl⟩) (hres _)
  | @tail _ s₂ a' n args fl hcall hfl =>
    obtain ⟨fi', ps', rs', hfi', hty', rfl⟩ := MachineLClose.evalLXPS_tail_wf hL a' args n rfl
    have key : ∀ b, (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s₂) ∈ ClS a' s₁ args →
        (([] : List (Call (Abstract.wasmHostSig H))), tailAnsS rs.length rs'.length b s₂) ∈
          ClS a s us := by
      intro b hz
      refine close_of_open (.inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', rs'.length, args, b, l,
        hfi, hcode, hty, hL, rfl⟩)) ?_
      refine subst_of_res _ (fun z hz' => ?_) _
      rcases List.mem_append.1 hz' with hz' | hz'
      · exact closeOk_res (hok z hz')
      · rw [List.mem_singleton.1 hz']
        exact ⟨a', args, s₁, b, s₂, rfl, hz⟩
    refine ⟨fun vs hvs fi₀ ps₀ rs₀ hfi₀ hty₀ => ?_, fun t ht => ?_, fun ht => ?_⟩
    · rw [hfi] at hfi₀; cases hfi₀
      rw [hty] at hty₀; cases hty₀
      rcases fl with w | ⟨_ | k, w⟩ | w | _ | t <;>
        simp only [Abstract.CallX.tailFlow, Flow.retVals, Option.some.injEq,
          reduceCtorEq] at hvs
      all_goals
        subst hvs
        have hz := hcall.1 w (by simp [Flow.retVals]) fi' ps' rs' hfi' hty'
        have := key _ hz
        simpa [tailAnsS, ansFlow, Abstract.CallX.tailFlow, exitFlow, endOfFlowS,
          List.take_take] using this
    · rcases fl with w | ⟨_ | k, w⟩ | w | _ | t' <;>
        simp only [Abstract.CallX.tailFlow, reduceCtorEq] at ht
      simp only [Flow.throw.injEq] at ht
      subst ht
      have := key _ (hcall.2.1 _ rfl)
      simpa [tailAnsS, ansFlow, Abstract.CallX.tailFlow, exitFlow, endOfFlowS] using this
    · rcases fl with w | ⟨_ | k, w⟩ | w | _ | t' <;>
        simp only [Abstract.CallX.tailFlow, reduceCtorEq] at ht
      · simp [Flow.retVals, Flow.Abrupt] at hfl
      · have := key _ (hcall.2.2 rfl)
        simpa [tailAnsS] using this

/-- **Every answer of the closed call relation is good.** -/
theorem closed_goodS : (closedCallXP : CallRel H) ≤ GoodS :=
  OrderHom.lfp_le bodyCallXPOp (fun _ _ _ _ h => body_goodS h)

/-- **A `closedCallXP`-answered entry is a session behaviour with the empty log.** -/
theorem session_of_closeOk {s s₂ : Store H} {g : Nat} {args : List Val}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}} (h : CloseOk closedCallXP (SCall.mk g args s b s₂)) :
    (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s₂) ∈ wasmEvFunXPS s (g, args) := by
  have h' := closeOk_mono closed_goodS h
  rcases b with (ws | t) | u
  · obtain ⟨fi, ps, rs, fl, vs, hfi, hty, hc, hv, rfl⟩ := h'
    exact hc.1 vs hv fi ps rs hfi hty
  · exact (show GoodS s g args (s₂, .throw t) from h').2.1 t rfl
  · exact (show GoodS s g args (s₂, .trap) from h').2.2 rfl

end Silmaril.Wasm.Cfg.Proofs.CfgClosureAns
