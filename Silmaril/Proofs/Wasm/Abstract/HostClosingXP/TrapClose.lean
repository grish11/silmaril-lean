module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapFwd
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Closure

/-!
# The trapping behaviours of the canonical closure are logged Core runs (proofs)

A trapping resolution (`subst_trap`) either resolves every call by a returning callee and ends in
the open behaviour's trap, or stops at a call whose callee traps (`Shape.Subst.intTrap`), anything
after it dropped. By least-fixpoint induction (`close_le_trapC`), every trapping closed behaviour
with a consistent log is a Core run of the call to a trap with exactly that log, in some store:

* a Wasm body ending in a trap: `evalLXPh_fwd` in its frame, the trap (or Core's pending null tail
  call) leaving the label and frame;
* a Wasm body cut at a trapping callee, in its body or at its pending tail call:
  `evalLXPh_trap` in its frame, or the body's run to the pending tail call, the frame left and
  the tail callee's trap;
* a host callee answering a trap: its one event.

A cut call (`callCut`, `indCut`, `refCut`) contributes exactly through the second case: it is
resolved only by `intTrap`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailFlow)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Trapping resolutions -/

universe u

/-- **A trapping resolution**: every call resolved by a returning callee and the open end a
trap, or a prefix resolved and then a call whose callee traps. -/
theorem subst_trap {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) (hy : y.2 = .trap) :
    (e = .trap ∧ Shape.SubstPre c x y.1) ∨
      ∃ (u w : List (Call (sh.E ⊕ₛ sh.self))) (g : sh.F) (a : sh.A g) (s : sh.S)
        (ans : sh.B g × sh.S) (q c₁ : List (Call sh.E)),
        x = u ++ ⟨.inr ⟨g, (a, s)⟩, ans⟩ :: w ∧ Shape.SubstPre c u q ∧
          (c₁, .trap) ∈ c g s a ∧ y.1 = q ++ c₁ := by
  induction h with
  | nil e => exact .inl ⟨hy, .nil⟩
  | @ext m n rest e y _ ih =>
    rcases ih hy with ⟨he, hp⟩ | ⟨u, w, g, a, s, ans, q, c₁, rfl, hp, hc, hq⟩
    · exact .inl ⟨he, .ext hp⟩
    · exact .inr ⟨⟨.inl m, n⟩ :: u, w, g, a, s, ans, ⟨m, n⟩ :: q, c₁, rfl, .ext hp, hc,
        by simp [hq]⟩
  | @int g' a' s' b s₂ rest e c₀ y hm _ ih =>
    rcases ih hy with ⟨he, hp⟩ | ⟨u, w, g, a, s, ans, q, c₁, rfl, hp, hc, hq⟩
    · exact .inl ⟨he, .int hm hp⟩
    · exact .inr ⟨⟨.inr ⟨g', (a', s')⟩, (b, s₂)⟩ :: u, w, g, a, s, ans, c₀ ++ q, c₁, rfl,
        .int hm hp, hc, by simp [hq]⟩
  | @intTrap g a s ans rest e c₁ hc =>
    exact .inr ⟨[], rest, g, a, s, ans, [], c₁, rfl, .nil, hc, rfl⟩
  | intDiv _ => cases hy

theorem substPre_mono {sh : Silmaril.Games.Abstract.Shape.{u}} {c c' : sh.ClosedMod} (h : c ≤ c')
    {x : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (hs : Shape.SubstPre c x q) :
    Shape.SubstPre c' x q := by
  induction hs with
  | nil => exact .nil
  | ext _ ih => exact .ext ih
  | int hm _ ih => exact .int (h _ _ _ hm) ih

theorem substPre_ext_single {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod}
    {m : sh.E.Op} {n : sh.E.Ar m} {q : List (Call sh.E)}
    (hs : Shape.SubstPre c [⟨.inl m, n⟩] q) : q = [⟨m, n⟩] := by
  cases hs with
  | ext h => cases h; rfl

theorem lift_eq_mk{z : OCall H} {g : Nat} {a : List Val} {s : Store H}
    {ans : (List Val ⊕ Nat) × Store H}
    (h : OCall.lift z = ⟨.inr ⟨g, (a, s)⟩, ans⟩) : z = OCall.mk g a s ans.1 ans.2 := by
  rcases z with ⟨⟨⟩ | ⟨g', a', s'⟩, ⟨b, s₂⟩⟩
  cases h
  rfl

/-- A log whose lift splits at an internal call splits there. -/
theorem map_lift_split {l : List (OCall H)} {u w : List (HCall H)} {g : Nat} {a : List Val}
    {s : Store H} {ans : (List Val ⊕ Nat) × Store H}
    (h : l.map OCall.lift = u ++ ⟨.inr ⟨g, (a, s)⟩, ans⟩ :: w) :
    ∃ l₁ l₂, l = l₁ ++ OCall.mk g a s ans.1 ans.2 :: l₂ ∧ l₁.map OCall.lift = u := by
  obtain ⟨l₁, l₂', rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp h
  obtain ⟨z, l₂, rfl, hz, -⟩ := List.map_eq_cons_iff.mp h₂
  exact ⟨l₁, l₂, by rw [lift_eq_mk hz], h₁⟩

theorem mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' s₂ s₂' : Store H}
    {b b' : List Val ⊕ Nat} (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem tailAns_ne_trap {m n : Nat} {b : List Val ⊕ Nat} {s : Store H} :
    tailAns m n b s ≠ .trap := by
  rcases b with ws | t <;> simp [tailAns, ansFlow, tailFlow, exitFlow, endOfFlow]

/-- A closed behaviour names a typed function. -/
theorem close_fn {a : Nat} {s : Store H} {us : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : y ∈ Shape.close wasmHOpenXP a s us) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
  rw [← Shape.resolve_close] at h
  obtain ⟨x, hx, -⟩ := h
  rcases hx with ⟨fi, -, ps, rs, -, -, -, -, -, hfi, -, hty, -⟩ |
    ⟨fi, -, ps, rs, -, -, -, -, -, -, -, -, hfi, -, hty, -⟩ |
    ⟨fi, -, ps, rs, -, -, -, hfi, -, hty, -⟩ <;> exact ⟨fi, ps, rs, hfi, hty⟩

/-! ## A callee's trap, case by case, in the exact store of the trap -/

section Callee

variable {tags : List TagInst} {S : Store H → Prop} {s : Store H} {a : Nat} {us : List Val}
  {fi : FuncInst H} {ps rs : List Validation.CValType}

theorem CalleeTrap.mono {qc : List (Call (wasmHostSig H))} {S' : Store H → Prop}
    (h : CalleeTrap P host s a us qc S) (hS : ∀ s', S s' → S' s') : CalleeTrap P host s a us qc S' :=
  fun f c hcr => let ⟨s', h₁, h₂⟩ := h f c hcr; ⟨s', hS _ h₁, h₂⟩

/-- **A Wasm body trapping itself**: its logged run to a trap flow in the store `s'`, its calls
resolved by the closure to a consistent log `q`, is a Core run of the call to a trap in exactly
`s'` (or Core's pending null tail call, also in `s'`). -/
theorem body_trap_callee (hH : NativeHostSlice host) (hE : HostSliceE tags host) {fn : Func}
    {s' : Store H} {f₂ : Frame} {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s', f₂, .flow .trap))
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hq : Cons host q) :
    CalleeTrap P host s a us q (· = s') := by
  intro f c hcr
  obtain ⟨ob, hob, hb'⟩ := body_chk hSt hfi hcode hty hn
  obtain ⟨d, cl⟩ := evalLXPh_fwd (P := P) hH hE hE' q
    (substPre_mono (close_le_goodCX hH hE) hp) hq
  have hwb := cl hts hSt hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨s'', f'', c', o, hrun, he', hm⟩ := hwb
  have inner := evRun_wrap (Wfr rs.length f) (hW_fr _ f) hrun
  rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hfm⟩ | ⟨-, vs, c₀, rfl, hc₀, rfl, rfl⟩
  · rcases o with _ | _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hfm
    have hc' : c' = [.trap] := he'
    subst hc'
    refine ⟨_, rfl, ?_⟩
    have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
      (evRun_trans inner (evRun_of_free (steps_trap_frame (P := P))))
    simpa [vals] using this
  · obtain ⟨-, rest, rfl⟩ := he'
    refine ⟨_, rfl, ?_⟩
    have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
      (evRun_trans inner (evRun_of_free (frame_tailNull (P := P) (host := NH) hc₀)))
    simpa [vals] using this

/-- **A Wasm body cut at a trapping callee**: its logged run whose calls before the call `z` are
resolved by the closure to `q`, the callee of `z` trapping with the host events `c₁` in a store
satisfying `S`, is a Core run of the call to a trap in that store: the trap leaves every context
and the frame unchanged. -/
theorem body_cut_callee (hH : NativeHostSlice host) (hE : HostSliceE tags host) {fn : Func}
    {l l₁ l₂ : List (OCall H)} {z : OCall H} {r : Store H × Frame × POut}
    {q c₁ : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l r)
    (hl : l = l₁ ++ z :: l₂) (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l₁.map OCall.lift) q)
    (hz : TrapAt tags P host z c₁ S) (hq : Cons host (q ++ c₁)) :
    CalleeTrap P host s a us (q ++ c₁) S := by
  intro f c hcr
  obtain ⟨ob, hob, hb'⟩ := body_chk hSt hfi hcode hty hn
  have hwb := evalLXPh_trap (P := P) hH hE hE' l₁ z l₂ hl q c₁
    (substPre_mono (close_le_goodCX hH hE) hp) hz hq hts hSt hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨s'', f'', c', o, hrun, he', ho⟩ := hwb
  rw [trap_of_ends he' ho.1] at hrun
  have inner := evRun_wrap (Wfr rs.length f) (hW_fr _ f) hrun
  refine ⟨s'', ho.2, ?_⟩
  have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
    (evRun_trans inner (evRun_of_free (steps_trap_frame (P := P))))
  simpa [vals] using this

/-- **A Wasm body whose pending tail call's callee traps**: the body's run to the pending tail
call `(a', args)`, its calls resolved by the closure to `q`, the frame left, and the tail callee's
trap with the host events `c₁` in a store satisfying `S`, is a Core run of the call to a trap in
that store. -/
theorem body_tail_callee (hH : NativeHostSlice host) (hE : HostSliceE tags host) {fn : Func}
    {l : List (OCall H)} {s₁ s₂ : Store H} {f₂ : Frame} {a' n : Nat} {args : List Val}
    {b : List Val ⊕ Nat} {q c₁ : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s₁, f₂, .tail a' args n))
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q)
    (hz : TrapAt tags P host (OCall.mk a' args s₁ b s₂) c₁ S) (hq : Cons host (q ++ c₁)) :
    CalleeTrap P host s a us (q ++ c₁) S := by
  intro f c hcr
  obtain ⟨ob, hob, hb'⟩ := body_chk hSt hfi hcode hty hn
  rw [cons_append] at hq
  obtain ⟨d, cl⟩ := evalLXPh_fwd (P := P) hH hE hE' q
    (substPre_mono (close_le_goodCX hH hE) hp) hq.1
  obtain ⟨t₁, hA, -⟩ := evalOXP_host_good (P := P) hH hE d hts
  obtain ⟨-, hinv, hw⟩ := hA hSt hb'
  obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, -⟩ := hw a' args n rfl
  obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
  have hS₁ : StoreChkE (ehExt tags) s₁.funcs := hinv.1.2.1 hSt
  have hwb := cl hts hSt hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨s'', f'', c', o, hrun, he', hm⟩ := hwb
  obtain ⟨vs₁, c₀, rfl, hc₀, rfl, rfl⟩ := matchP_tail_iff.mp hm
  obtain ⟨-, rest, rfl⟩ := he'
  have inner := evRun_wrap (Wfr rs.length f) (hW_fr _ f) hrun
  have ex := frame_tail_exit (P := P) (host := NH) (s := s'') (f := f) (k := rs.length)
    (F := f'') (vs₁ := vs₁) (rest := rest) hc₀ hfi₂ hex₂ (hargs.trans hpl₂.symm)
  obtain ⟨s₃, hs₃, hcl⟩ := hz _ _ _ _ _ rfl fi₂ ps₂ rs₂ hfi₂ hty₂ t₁ hS₁ hargs f _
    (isCallRef_retToCallIn hc₀ f''.module)
  refine ⟨s₃, hs₃, ?_⟩
  have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
    (evRun_trans inner (evRun_trans (evRun_of_free ex) hcl))
  simpa [vals] using this

/-- **A host function answering a trap**, leaving the store `s'`: its one event, then a trap in
exactly `s'`. -/
theorem host_trap_callee {hh : H} {s' : Store H} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : us.length = ps.length) (hm : host hh s us (.returned s' .trap)) :
    CalleeTrap P host s a us [⟨(hh, s, us), (s', .trap)⟩] (· = s') := by
  intro f c hcr
  obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
  exact ⟨s', rfl, .event (hEvStep_host_callRef (P := P) (f := f) hcr hfi he' (hn.trans hpl.symm)
    hcode hm) (.refl _)⟩

/-- **An invocation whose function traps**: the invocation's Core run to the trap. -/
theorem invoke_calleeTrap {vs : List Val} {cs : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (h : CalleeTrap P host s a vs cs S) :
    ∃ s₂, S s₂ ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  rw [invoke_eq hfi]
  exact h {} _ trivial

end Callee

/-! ## The trapping closed behaviours -/

/-- **Trapping closed behaviours that are logged Core runs**: closed behaviours that, trapping
with a consistent log, are on stores with the tag invariants and the store check, for typed
arguments, Core runs of the call to a trap with exactly that log, in some store. -/
def TrapC (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    (wasmHShape H).ClosedMod := fun a s us =>
  {y | y ∈ Shape.close wasmHOpenXP a s us ∧ (y.2 = .trap → Cons host y.1 →
    ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi →
      Validation.DefType.funcType? fi.type = some (ps, rs) → TagsOk tags s →
      StoreChkE (ehExt tags) s.funcs → us.length = ps.length →
      CalleeTrap P host s a us y.1 (fun _ => True))}

/-- The callee of a split call traps, from `TrapC`, in some store. -/
theorem trapAt_of_trapC {tags : List TagInst} {a : Nat} {args : List Val} {s₁ : Store H}
    {ans : (List Val ⊕ Nat) × Store H} {c₁ : List (Call (wasmHostSig H))}
    (hm : (c₁, .trap) ∈ TrapC tags P host a s₁ args) (hc : Cons host c₁) :
    TrapAt tags P host (OCall.mk a args s₁ ans.1 ans.2) c₁ (fun _ => True) := by
  intro a' args' s₁' b s₂ h fi ps rs hfi hty hts hS hn
  obtain ⟨rfl, rfl, rfl⟩ := mk_inj h
  exact hm.2 rfl hc fi ps rs hfi hty hts hS hn

/-- **Every closed behaviour is in `TrapC`**: least-fixpoint induction, case by case. -/
theorem close_le_trapC {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : Shape.close (wasmHOpenXP (H := H)) ≤ TrapC tags P host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s us y ⟨x, hx, hS⟩
  have hle : TrapC tags P host ≤ Shape.close (wasmHOpenXP (H := H)) := fun _ _ _ _ h => h.1
  have hmem : y ∈ Shape.close wasmHOpenXP a s us := by
    rw [← Shape.resolve_close]
    exact ⟨x, hx, hS.mono hle⟩
  refine ⟨hmem, fun hy hq fi₀ ps₀ rs₀ hfi₀ hty₀ hts hSt hn => ?_⟩
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hcode, hty, hE', hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b₀, l, hfi, hcode, hty, hE', rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hcode, hty, hxf, rfl⟩
  all_goals
    obtain rfl : fi₀ = fi := Option.some.inj (hfi₀.symm.trans hfi)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty₀.symm.trans hty))
  · -- a Wasm body ending in a flow
    rcases subst_trap hS hy with ⟨he, hp⟩ | ⟨u, w, g, a₁, s₀, ans, q, c₁, hsplit, hp, hc₁, hq₁⟩
    · -- the body traps
      have hfl : fl = .trap := by rcases fl <;> simp_all [endOfFlow]
      subst hfl
      have hbfl : bfl = .trap := by
        rcases bfl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [exitFlow]
      subst hbfl
      exact (body_trap_callee hH hE hfi hcode hty hn hts hSt hE' (substPre_mono hle hp) hq).mono
        fun _ _ => trivial
    · -- the body cut at a trapping callee
      obtain ⟨l₁, l₂, rfl, rfl⟩ := map_lift_split hsplit
      rw [hq₁] at hq ⊢
      exact body_cut_callee hH hE hfi hcode hty hn hts hSt hE' rfl (substPre_mono hle hp)
        (trapAt_of_trapC (ans := ans) hc₁ ((cons_append).1 hq).2) hq
  · -- a Wasm body ending in a pending tail call
    rcases subst_trap hS hy with ⟨he, -⟩ | ⟨u, w, g, a₁, s₀, ans, q, c₁, hsplit, hp, hc₁, hq₁⟩
    · exact absurd he tailAns_ne_trap
    · obtain ⟨l₁, l₂, hl, rfl⟩ := map_lift_split hsplit
      rw [hq₁] at hq ⊢
      have hz := trapAt_of_trapC (ans := ans) hc₁ ((cons_append).1 hq).2
      rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, hzl⟩
      · -- in the body
        exact body_cut_callee hH hE hfi hcode hty hn hts hSt hE' rfl (substPre_mono hle hp) hz hq
      · -- at the pending tail call, made at the frame
        obtain ⟨rfl, rfl, rfl⟩ := mk_inj hzl.symm
        exact body_tail_callee hH hE hfi hcode hty hn hts hSt hE' (substPre_mono hle hp) hz hq
  · -- a host function answering a trap: its one event
    rcases subst_trap hS hy with ⟨he, hp⟩ | ⟨u, w, g, a₁, s₀, ans, q, c₁, hsplit, -, -, -⟩
    · rw [substPre_ext_single hp] at hq ⊢
      have hm : host hh s us (.returned s' r) := hq _ List.mem_cons_self
      rcases r with w | t | _
      · simp only [resFlow, exitFlow, Option.some.injEq] at hxf
        subst hxf
        cases he
      · exact absurd hm (hH.noThrow _ _ _ _ _)
      · exact (host_trap_callee hfi hcode hty hn hm).mono fun _ _ => trivial
    · rcases u with _ | ⟨u₀, u⟩
      · cases hsplit
      · obtain ⟨-, h⟩ := List.cons.inj hsplit
        simp at h

/-- **A trapping closed behaviour with a consistent log is a Core run of the call to a trap**
with exactly that log, in any frame and any `call_ref` form, every profile, in some store. -/
theorem close_trap_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {a : Nat} {s : Store H} {us : List Val}
    {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, .trap) ∈ Shape.close wasmHOpenXP a s us) (hc : Cons host c₁)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    CalleeTrap P host s a us c₁ (fun _ => True) :=
  (close_le_trapC hH hE a s us hm).2 rfl hc fi ps rs hfi hty hts hS hn

/-- **A trapping behaviour of an invocation with a consistent log is a Core run of the
invocation to a trap with exactly that log**, in some store, every profile. -/
theorem wasmEvFunXP_trap_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val}
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .trap) ∈ wasmEvFunXP s (a, vs))
    (hc : Cons host cs) : ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  obtain ⟨fi, ps, rs, hfi, hty⟩ := close_fn h
  obtain ⟨s₂, -, h⟩ := invoke_calleeTrap hfi
    (close_trap_evRun hH hE h hc hts hS hfi hty (invokeOk_length hok hfi hty))
  exact ⟨s₂, h⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
