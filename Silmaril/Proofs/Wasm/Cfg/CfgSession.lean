module

public import Silmaril.Wasm.Cfg.CfgSession.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Cfg.MachineLDiv.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXPBack.Thms

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

`cfgSessionTriple_eq`: the CFG session triple is `Abstract.sessionTripleXP`.

* Productive streams (`infLcfg_eq`): the machine's productive streams from the CFG entry are the
  session readings of the body's (`MachineL.prodL_iff`), and the reading is injective.
* Divergence after a log (`closeDLog_cfg_eq`), at the level of `Shape.closeDLog`, not per call:
  `LDLwXP ⊆ LDLcfg` by `MachineL.logDiv_machine`. Conversely `MachineL.machine_logDiv` extends the
  machine's log by canonical entries `C` answered by the closed oracle (`CloseOk closedCallXP`;
  their session readings are value or exception answers, never traps). Each resolves to the empty
  host log in `Shape.close wasmHOpenXP` (`closeOk_substPre`, by
  `Abstract.close_of_closedCallXP_vals`/`_throw`), so the host log `qs ++ q` is unchanged.
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

/-! ## The CFG session triple -/

section Triple

open Silmaril.Wasm.Abstract (OCall HCall wasmHShape wasmHOpenXP LDLwXP InfLwXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)

/-- The closure of the canonical open module. -/
abbrev Cl : (wasmHShape H).ClosedMod := Shape.close wasmHOpenXP

theorem substPre_append {c : (wasmHShape H).ClosedMod} {u v : List (HCall H)}
    {q q' : List (Call (Abstract.wasmHostSig H))} (hu : Shape.SubstPre c u q)
    (hv : Shape.SubstPre c v q') : Shape.SubstPre c (u ++ v) (q ++ q') := by
  induction hu with
  | nil => simpa using hv
  | ext _ ih => exact .ext ih
  | int hm _ ih => rw [List.append_assoc]; exact .int hm ih

/-- **A closed-oracle entry resolves to the empty host log.** A canonical call whose session
reading is answered by `closedCallXP` (by values or an exception) is a closure behaviour with no
host call. -/
theorem closeOk_substPre {o : OCall H} (h : CloseOk closedCallXP o.toS) :
    Shape.SubstPre (Cl (H := H)) [o.lift] [] := by
  rcases o with ⟨⟨⟨⟩⟩ | ⟨a, args, s₁⟩, b, s₂⟩
  have hz : (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s₂) ∈ Cl a s₁ args := by
    rcases b with ws | t
    · obtain ⟨fi, ps, rs, fl, vs, hfi, hty, hC, hv, rfl⟩ := h
      exact Abstract.close_of_closedCallXP_vals hC hv hfi hty
    · exact Abstract.close_of_closedCallXP_throw h
  have := Shape.SubstPre.int (rest := []) hz (Shape.SubstPre.nil (c := Cl))
  rw [List.append_nil] at this
  exact this

theorem closeOk_all {C : List (OCall H)} (h : ∀ e ∈ C.map OCall.toS, CloseOk closedCallXP e) :
    Shape.SubstPre (Cl (H := H)) (C.map OCall.lift) [] := by
  induction C with
  | nil => exact .nil
  | cons o C ih =>
    have := substPre_append (closeOk_substPre (h _ (List.mem_cons_self ..)))
      (ih fun e he => h e (List.mem_cons_of_mem _ he))
    simpa using this

theorem ldlw_ldlcfg {z : (wasmHShape H).self.Op} {u : List (HCall H)} (h : LDLwXP z u) :
    LDLcfg z u := by
  obtain ⟨fi, fn, L, hfi, hcode, hd, rfl⟩ := h
  exact ⟨fi, fn, L, hfi, hcode, logDiv_machine hd, rfl⟩

/-- **Logged divergence on the machine is native logged divergence after closed entries**, which
resolve to the empty host log. -/
theorem ldlcfg_ldlw {z : (wasmHShape H).self.Op} {u : List (HCall H)} (h : LDLcfg z u) :
    ∃ C : List (OCall H), LDLwXP z (u ++ C.map OCall.lift) ∧
      Shape.SubstPre (Cl (H := H)) (C.map OCall.lift) [] := by
  obtain ⟨fi, fn, L, hfi, hcode, hd, rfl⟩ := h
  obtain ⟨c, L', hc, hL', hd'⟩ := machine_logDiv hd
  obtain ⟨L₁, C, rfl, h1, rfl⟩ := List.map_eq_append_iff.1 hL'
  obtain rfl := map_toS_inj h1
  exact ⟨C, ⟨fi, fn, _, hfi, hcode, hd', by simp⟩, closeOk_all hc⟩

/-- **Logged divergence on the machine closes as native logged divergence.** -/
theorem closeDLog_cfg_eq :
    Shape.closeDLog (wasmHOpenXP (H := H)) LDLcfg = Shape.closeDLog wasmHOpenXP LDLwXP := by
  funext f s a
  ext y
  simp only [Shape.closeDLog, Set.mem_union, Set.mem_ofPred_eq]
  refine or_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨z, qs, u, q, hp, hl, hq, he⟩
    obtain ⟨C, hw, hC⟩ := ldlcfg_ldlw hl
    exact ⟨z, qs, _, q, hp, hw, by simpa using substPre_append hq hC, he⟩
  · rintro ⟨z, qs, u, q, hp, hl, hq, he⟩
    exact ⟨z, qs, u, q, hp, ldlw_ldlcfg hl, hq, he⟩

theorem cfgEvFunD_eq : (cfgEvFunDXP : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H)
    (Store H) (Nat × List Val) (List Val ⊕ Nat)) = Abstract.wasmEvFunDXP := by
  funext s p
  simp only [cfgEvFunDXP, Abstract.wasmEvFunDXP, cfgHOpenX_eq, closeDLog_cfg_eq]

/-- **The machine's productive streams of a body are the native ones.** -/
theorem infLcfg_eq : (InfLcfg : Shape.OpenInf (wasmHShape H)) = InfLwXP := by
  funext a s vs
  ext ν
  simp only [InfLcfg, InfLwXP, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨fi, fn, ω, hfi, hcode, hp, rfl⟩
    obtain ⟨ω', hi, he⟩ := prodL_iff.1 hp
    obtain rfl : ω = ω' := funext fun n => toS_injective (congrFun he n)
    exact ⟨fi, fn, ω, hfi, hcode, hi, rfl⟩
  · rintro ⟨fi, fn, ω, hfi, hcode, hi, rfl⟩
    exact ⟨fi, fn, ω, hfi, hcode, prodL_iff.2 ⟨ω, hi, rfl⟩, rfl⟩

theorem cfgEvInfN_eq : (cfgEvInfNXP : Silmaril.Games.Abstract.PInf (Abstract.wasmHostSig H)
    (Store H) (Nat × List Val)) = Abstract.wasmEvInfNXP := by
  funext s p
  simp only [cfgEvInfNXP, Abstract.wasmEvInfNXP, cfgHOpenX_eq, infLcfg_eq]

theorem cfgEvFunDS_eq : (cfgEvFunDXPS : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H)
    (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.wasmEvFunDXPS := by
  funext s p
  simp only [cfgEvFunDXPS, Abstract.wasmEvFunDXPS, cfgEvFun_eq, cfgEvFunD_eq]

theorem cfgSessionTriple_eq :
    (cfgSessionTriple : Silmaril.Games.Abstract.ObsTriple (Abstract.wasmHostSig H) (Store H)
      (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.sessionTripleXP := by
  simp only [cfgSessionTriple, Abstract.sessionTripleXP, cfgEvFunDS_eq, cfgEvPend_eq,
    cfgEvInfN_eq]

end Triple

end Silmaril.Wasm.Cfg.Proofs.CfgSession
