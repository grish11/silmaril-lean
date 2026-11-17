module

public import Silmaril.Wasm.Cfg.CfgSession.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Abstract.HostClosingS.Thms

@[expose] public section

/-!
# The recursive CFG closure (proofs)

`cfgHOpen_eq`: the CFG open module is the session's, by the forward theorems (`forward_sink`,
`forward_tail`) and the converse (`backward`; the converse's excluded `brk (k + 1)` has no framed
end, `exitFlow` gives `none`).

`cfgHOpenX_eq`: the canonical CFG open module is `Abstract.wasmHOpenXP`, by the same machine
theorems and the exact session/canonical correspondence (`Abstract.evalLXPS_canonical_cut`,
`Abstract.evalLXPh_session_cut`): a machine log read by `CanonRead` is the log of a canonical run
(`canonRead_evalLXPh`), and every canonical run has a session run whose log reads as its log
(`evalLXPh_canonRead`). The reading is unambiguous: `OCall.toS` is injective and never gives a
trap answer (`toS_injective`, `trap_ne_map`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgSession

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHShapeS SCall endOfFlowS tailAnsS exitFlow wasmHOpenXPS)

variable {H : Type}

/-- A sink's native result is a flow in the sink's store and frame. -/
theorem endRel_sf {st : MState H} {r : Store H × Frame × Abstract.CallXP.POut} (h : EndRel st r) :
    ∃ fl, r = (st.store, st.frame, .flow fl) := by
  unfold EndRel at h
  split at h
  · obtain ⟨fl, rfl, -⟩ := h; exact ⟨fl, rfl⟩
  · subst h; exact ⟨_, rfl⟩
  · obtain ⟨a, -, rfl⟩ := h; exact ⟨_, rfl⟩
  · exact h.elim

theorem exitFlow_of_retVals {n : Nat} {fl : Flow} {ws : List Val} (h : fl.retVals = some ws) :
    exitFlow n fl = some (.normal (ws.take n).reverse) := by
  cases fl with
  | normal => cases h; rfl
  | ret => cases h; rfl
  | brk k vs => cases k with
    | zero => cases h; rfl
    | succ k => simp [Flow.retVals] at h
  | _ => simp [Flow.retVals] at h

/-- **The end a sink stands for does not depend on the native flow read**: every flow the sink
stands for has the same `exitFlow`. -/
theorem exitFlow_endRel {st : MState H} {a a' : Store H} {b b' : Frame} {fl fl' : Flow}
    (h : EndRel st (a, b, .flow fl)) (h' : EndRel st (a', b', .flow fl')) (n : Nat) :
    exitFlow n fl = exitFlow n fl' := by
  unfold EndRel at h h'
  cases hn : st.node with
  | exit =>
    simp only [hn] at h h'
    obtain ⟨g, hg, hv⟩ := h
    obtain ⟨g', hg', hv'⟩ := h'
    simp only [Prod.mk.injEq, Abstract.CallXP.POut.flow.injEq] at hg hg'
    obtain ⟨-, -, rfl⟩ := hg; obtain ⟨-, -, rfl⟩ := hg'
    rw [exitFlow_of_retVals hv, exitFlow_of_retVals hv']
  | trap =>
    simp only [hn, Prod.mk.injEq, Abstract.CallXP.POut.flow.injEq] at h h'
    rw [h.2.2, h'.2.2]
  | raise =>
    simp only [hn] at h h'
    obtain ⟨x, hx, hr⟩ := h
    obtain ⟨x', hx', hr'⟩ := h'
    rw [hx] at hx'
    simp only [List.cons.injEq, Val.ref.injEq, Ref.exn.injEq, and_true] at hx'
    simp only [Prod.mk.injEq, Abstract.CallXP.POut.flow.injEq] at hr hr'
    rw [hr.2.2, hr'.2.2, hx']
  | _ => simp [hn] at h

theorem exitFlow_brk {n k : Nat} {ws : List Val} : exitFlow n (.brk (k + 1) ws) = none := rfl

/-- **The CFG open module is the session's open module.** -/
theorem cfgHOpen_eq : (cfgHOpenXPS : (wasmHShapeS H).OpenMod) = wasmHOpenXPS := by
  funext a s vs
  ext x
  constructor
  · rintro (⟨fi, fn, ps, rs, st, bfl, fl, l, hfi, hc, hty, hrun, hs, hE, hex, rfl⟩ |
      ⟨fi, fn, ps, rs, st, s₁, s₂, f₂, a', n, args, b, l, l', hfi, hc, hty, hrun, ht, rfl⟩ | hh)
    · obtain ⟨r, hr, hE₀⟩ := forward_sink hrun hs
      obtain ⟨bfl₀, rfl⟩ := endRel_sf hE₀
      refine .inl ⟨fi, fn, ps, rs, st.store, st.frame, bfl₀, fl, l, hfi, hc, hty, hr, ?_, rfl⟩
      rw [exitFlow_endRel hE₀ hE]; exact hex
    · exact .inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l ++ l', hfi, hc, hty,
        forward_tail hrun ht, rfl⟩)
    · exact .inr (.inr hh)
  · rintro (⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hr, hex, rfl⟩ |
      ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hfi, hc, hty, hr, rfl⟩ | hh)
    · have hnb : ∀ k ws, (s', f₂, Abstract.CallXP.POut.flow bfl).2.2 ≠ .flow (.brk (k + 1) ws) := by
        rintro k ws h
        simp only [Abstract.CallXP.POut.flow.injEq] at h
        subst h; simp [exitFlow_brk] at hex
      obtain ⟨st, l₁, l₂, hrun, rfl, hend⟩ := backward hr hnb
      rcases hend with ⟨hs, rfl, hE⟩ | ht
      · obtain ⟨g, hg⟩ := endRel_sf hE
        simp only [Prod.mk.injEq, Abstract.CallXP.POut.flow.injEq] at hg
        obtain ⟨rfl, rfl, rfl⟩ := hg
        exact .inl ⟨fi, fn, ps, rs, st, bfl, fl, l₁, hfi, hc, hty, by simpa using hrun, hs, hE,
          hex, by simp⟩
      · cases ht
    · obtain ⟨st, l₁, l₂, hrun, rfl, hend⟩ := backward hr (by intro k ws h; cases h)
      rcases hend with ⟨-, -, hE⟩ | ht
      · obtain ⟨g, hg⟩ := endRel_sf hE; cases hg
      · exact .inr (.inl ⟨fi, fn, ps, rs, st, s₁, s₂, f₂, a', n, args, b, l₁, l₂, hfi, hc, hty,
          hrun, ht, rfl⟩)
    · exact .inr (.inr hh)

/-- **The CFG session closure is the session closure.** -/
theorem cfgEvFun_eq : (cfgEvFunXPS : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H)
    (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.wasmEvFunXPS := by
  funext s p
  simp only [cfgEvFunXPS, Abstract.wasmEvFunXPS, cfgHOpen_eq]

open Silmaril.Wasm.Abstract (PendLXPS) in
/-- **The CFG session's pending host calls are the session's.** -/
theorem cfgPend_iff {s : Store H} {a : Nat} {vs : List Val}
    {q : List (Call (Abstract.wasmHostSig H))} {m : (Abstract.wasmHostSig H).Op} :
    CfgPendLXPS s a vs q m ↔ PendLXPS s a vs q m := by
  constructor
  · intro h
    induction h with
    | self hf hc => exact .self hf hc
    | desc hf hc hrun hr hq _ ih =>
      exact .desc hf hc ((pending_iff).2 ⟨_, _, _, hrun, hr, rfl⟩) (by rwa [cfgHOpen_eq] at hq) ih
    | tail hf hc hrun ht hq _ ih =>
      exact .tail hf hc (forward_tail hrun ht) (by rwa [cfgHOpen_eq] at hq) ih
  · intro h
    induction h with
    | self hf hc => exact .self hf hc
    | desc hf hc hr hq _ ih =>
      obtain ⟨st, l₁, l₂, hrun, hR, rfl⟩ := (pending_iff).1 hr
      exact .desc hf hc hrun hR (by rwa [cfgHOpen_eq]) ih
    | tail hf hc hbody hq _ ih =>
      obtain ⟨st, l₁, l₂, hrun, rfl, hend⟩ := backward hbody (by intro k ws h; cases h)
      rcases hend with ⟨-, -, hE⟩ | ht
      · obtain ⟨g, hg⟩ := endRel_sf hE; cases hg
      · exact .tail hf hc hrun ht (by rwa [cfgHOpen_eq]) ih

/-- **The pending host calls of the CFG session are the session's.** -/
theorem cfgEvPend_eq : (cfgEvPendXPS : Silmaril.Games.Abstract.Pending (Abstract.wasmHostSig H)
    (Store H) (Nat × List Val)) = Abstract.wasmEvPendXPS := by
  funext s p
  ext x
  exact cfgPend_iff

/-! ## The canonical, trap-erasing module -/

section Canon

open Silmaril.Wasm.Abstract (OCall EvalLXPS EvalLXPh wasmHShape wasmHOpenXP)

theorem toS_injective : Function.Injective (OCall.toS : OCall H → SCall H) := by
  rintro ⟨⟨⟨⟩⟩ | y, b, s'⟩ ⟨⟨⟨⟩⟩ | y', b', s''⟩ h
  cases h; rfl

theorem map_toS_inj {l l' : List (OCall H)} (h : l.map OCall.toS = l'.map OCall.toS) : l = l' :=
  List.map_injective_iff.2 toS_injective h

/-- A callee-trap answer is no session reading of a canonical call. -/
theorem trap_not_mem {g : Nat} {args : List Val} {s₁ s₂ : Store H} (l : List (OCall H)) :
    SCall.mk g args s₁ (.inr ()) s₂ ∉ l.map OCall.toS := by
  intro h
  obtain ⟨⟨⟨⟨⟩⟩ | y, b, s'⟩, -, h⟩ := List.mem_map.1 h
  cases h

theorem trap_ne_map {g : Nat} {args : List Val} {s₁ s₂ : Store H} (u l : List (OCall H)) :
    u.map OCall.toS ++ [SCall.mk g args s₁ (.inr ()) s₂] ≠ l.map OCall.toS := by
  intro h
  exact trap_not_mem (g := g) (args := args) (s₁ := s₁) (s₂ := s₂) l (h ▸ by simp)

theorem trap_app_inj {g g' : Nat} {args args' : List Val} {s₁ s₂ s₁' s₂' : Store H}
    {u u' : List (OCall H)}
    (h : u.map OCall.toS ++ [SCall.mk g args s₁ (.inr ()) s₂] =
      u'.map OCall.toS ++ [SCall.mk g' args' s₁' (.inr ()) s₂']) :
    u = u' ∧ g = g' ∧ args = args' ∧ s₁ = s₁' ∧ s₂ = s₂' := by
  obtain ⟨hu, ht⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at ht
  cases ht
  exact ⟨map_toS_inj hu, rfl, rfl, rfl, rfl⟩

/-- **A session run of a log read as `l` is a canonical run of `l`**, a callee-trap answer read as
a cut call. -/
theorem canonRead_evalLXPh {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {lS : List (SCall H)} {l : List (OCall H)} {r : Store H × Frame × Abstract.CallXP.POut}
    (h : EvalLXPS s f stk es lS r) (hc : CanonRead lS l) : EvalLXPh s f stk es l r := by
  rcases hc with rfl | ⟨u, g, args, s₁, s₂, ws, fi, ps, rs, rfl, rfl, hf, hty, hws⟩
  · rcases Abstract.evalLXPS_canonical_cut h with ⟨l', hl', h'⟩ | ⟨-, u, g, args, s₁, s₂, -, hl', -⟩
    · rwa [map_toS_inj hl']
    · exact absurd hl'.symm (trap_ne_map _ _)
  · rcases Abstract.evalLXPS_canonical_cut h with ⟨l', hl', -⟩ |
      ⟨-, u', g', args', s₁', s₂', -, hl', fi', ps', rs', hf', hty', hall⟩
    · exact absurd hl' (trap_ne_map _ _)
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := trap_app_inj hl'
      obtain rfl : fi = fi' := Option.some.inj (hf.symm.trans hf')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
      exact hall ws hws

/-- **A canonical run is a session run of a log read as its log.** -/
theorem evalLXPh_canonRead {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Abstract.CallXP.POut}
    (h : EvalLXPh s f stk es l r) : ∃ lS, CanonRead lS l ∧ EvalLXPS s f stk es lS r := by
  rcases Abstract.evalLXPh_session_cut h with h' |
    ⟨-, u, g, args, s₁, s₂, ws, fi, ps, rs, rfl, hf, hty, hws, h'⟩
  · exact ⟨_, .inl rfl, h'⟩
  · exact ⟨_, .inr ⟨u, g, args, s₁, s₂, ws, fi, ps, rs, rfl, rfl, hf, hty, hws⟩, h'⟩

/-- **The canonical CFG open module is the canonical open module.** -/
theorem cfgHOpenX_eq : (cfgHOpenXP : (wasmHShape H).OpenMod) = wasmHOpenXP := by
  funext a s vs
  ext x
  constructor
  · rintro (⟨fi, fn, ps, rs, st, bfl, fl, lS, l, hfi, hc, hty, hrun, hs, hE, hread, hex, rfl⟩ |
      ⟨fi, fn, ps, rs, st, s₁, s₂, f₂, a', n, args, b, l₁, l₂, l, hfi, hc, hty, hrun, ht, heq,
        rfl⟩ | hh)
    · obtain ⟨r, hr, hE₀⟩ := forward_sink hrun hs
      obtain ⟨bfl₀, rfl⟩ := endRel_sf hE₀
      refine .inl ⟨fi, fn, ps, rs, st.store, st.frame, bfl₀, fl, l, hfi, hc, hty,
        canonRead_evalLXPh hr hread, ?_, rfl⟩
      rw [exitFlow_endRel hE₀ hE]; exact hex
    · have hS := forward_tail hrun ht
      rw [heq] at hS
      obtain ⟨l', hl', h'⟩ := Abstract.evalLXPS_canonical hS (by simp)
      obtain rfl := map_toS_inj hl'
      exact .inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hfi, hc, hty, h', rfl⟩)
    · exact .inr (.inr hh)
  · rintro (⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hr, hex, rfl⟩ |
      ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hfi, hc, hty, hr, rfl⟩ | hh)
    · obtain ⟨lS, hread, hS⟩ := evalLXPh_canonRead hr
      have hnb : ∀ k ws, (s', f₂, Abstract.CallXP.POut.flow bfl).2.2 ≠ .flow (.brk (k + 1) ws) := by
        rintro k ws h
        simp only [Abstract.CallXP.POut.flow.injEq] at h
        subst h; simp [exitFlow_brk] at hex
      obtain ⟨st, l₁, l₂, hrun, rfl, hend⟩ := backward hS hnb
      rcases hend with ⟨hs, rfl, hE⟩ | ht
      · obtain ⟨g, hg⟩ := endRel_sf hE
        simp only [Prod.mk.injEq, Abstract.CallXP.POut.flow.injEq] at hg
        obtain ⟨rfl, rfl, rfl⟩ := hg
        exact .inl ⟨fi, fn, ps, rs, st, bfl, fl, l₁, l, hfi, hc, hty, by simpa using hrun, hs, hE,
          by simpa using hread, hex, rfl⟩
      · cases ht
    · have hS := Abstract.evalLXPh_session hr (by simp)
      obtain ⟨st, l₁, l₂, hrun, heq, hend⟩ := backward hS (by intro k ws h; cases h)
      rcases hend with ⟨-, -, hE⟩ | ht
      · obtain ⟨g, hg⟩ := endRel_sf hE; cases hg
      · exact .inr (.inl ⟨fi, fn, ps, rs, st, s₁, s₂, f₂, a', n, args, b, l₁, l₂, l, hfi, hc, hty,
          hrun, ht, heq.symm, rfl⟩)
    · exact .inr (.inr hh)

/-- **The canonical CFG closure is the canonical closure.** -/
theorem cfgEvFunX_eq : (cfgEvFunXP : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H)
    (Store H) (Nat × List Val) (List Val ⊕ Nat)) = Abstract.wasmEvFunXP := by
  funext s p
  simp only [cfgEvFunXP, Abstract.wasmEvFunXP, cfgHOpenX_eq]

end Canon

end Silmaril.Wasm.Cfg.Proofs.CfgSession
