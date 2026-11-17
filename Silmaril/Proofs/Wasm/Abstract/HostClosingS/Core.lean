module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Close
public import Silmaril.Wasm.Abstract.HostCall.Thms

/-!
# Session behaviours are Core runs, a trap in exactly its store (proofs)

* `closeS_le_trapS`: by least-fixpoint induction on the session closure, a store-keeping trap
  `(c₁, .ret (.inr ()) s₂)` of a call, with a consistent log, on a store with the tag invariants
  and the store check, for typed arguments, is a Core run of the call to a trap in **exactly**
  `s₂`, every profile. The cases are those of the open module: a body trapping itself (in the
  store its run ends in), a body whose call is answered by a trap (the callee's trap, in its
  store, the run ending in that store), a pending tail call answered by a trap, and a host
  function answering a trap. Each is the store-exact case of `HostClosingXP`
  (`evalLXPh_trap_exact`, `evalLXPh_cut_exact`, `evalLXPh_tail_exact`, `host_trap_exact`), the
  calls before the trapping one resolved against the canonical closure through the projection
  (`substPre_toOld`).
* `wasmEvFunXPS_trap_evRun`: so for an invocation;
* `evRun_wasmEvFunXPS_trap`: backwards, in the deterministic profile: the canonical closure has
  the trap (`evRun_wasmEvFunXP_trap`), it lifts to a store-keeping session trap in some store,
  which is a Core run to a trap in its store, and the two runs, with the same log, trap in the same
  store (`evRun_trap_det`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingS

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Games.Abstract.StratSession (eraseEnd)

/-! ## Resolved prefixes -/

section Generic

universe u

variable {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod}

theorem substPre_split {B : List (Call (sh.E ⊕ₛ sh.self))} :
    ∀ {A : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)}, Shape.SubstPre c (A ++ B) q →
      ∃ qa qb, q = qa ++ qb ∧ Shape.SubstPre c A qa ∧ Shape.SubstPre c B qb
  | [], q, h => ⟨[], q, rfl, .nil, h⟩
  | ⟨.inl _, _⟩ :: _, _, h => by
    cases h with
    | ext h =>
      obtain ⟨qa, qb, rfl, ha, hb⟩ := substPre_split h
      exact ⟨_ :: qa, qb, rfl, .ext ha, hb⟩
  | ⟨.inr ⟨_, (_, _)⟩, (_, _)⟩ :: _, _, h => by
    cases h with
    | int hm h =>
      obtain ⟨qa, qb, rfl, ha, hb⟩ := substPre_split h
      exact ⟨_ ++ qa, qb, by simp, .int hm ha, hb⟩

theorem substPre_single {g : sh.F} {a : sh.A g} {s : sh.S} {b : sh.B g} {s' : sh.S}
    {q : List (Call sh.E)} (h : Shape.SubstPre c [⟨.inr ⟨g, (a, s)⟩, (b, s')⟩] q) :
    (q, .ret b s') ∈ c g s a := by
  cases h with
  | int hm h =>
    cases h
    simpa using hm

end Generic

variable {H : Type}

/-- A session resolved prefix of values and exception answers is a canonical resolved prefix. -/
theorem substPre_toOld {c : (wasmHShapeS H).ClosedMod} (hc : c ≤ Shape.close wasmHOpenXPS) :
    ∀ (l : List (OCall H)) {q : List (Call (wasmHostSig H))},
      Shape.SubstPre c (l.map oToS) q → Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q
  | [], _, h => by
    cases h
    exact .nil
  | ⟨.inr ⟨_, (_, _)⟩, (_, _)⟩ :: l, _, h => by
    cases h with
    | int hm h => exact .int (close_erase (hc _ _ _ hm)) (substPre_toOld hc l h)

theorem consistent_right {host : HostSemantics H} {q₁ q₂ : List (Call (wasmHostSig H))}
    (h : (coreHostRel host).Consistent (q₁ ++ q₂)) : (coreHostRel host).Consistent q₂ :=
  fun x hx => h x (List.mem_append_right _ hx)

/-- **The session closure never diverges.** -/
theorem closeS_ne_div {a : Nat} {s : Store H} {vs : List Val} {c₁ : List (Call (wasmHostSig H))} :
    (c₁, .div) ∉ Shape.close wasmHOpenXPS a s vs := fun h =>
  wasmEvFunXP_ne_div (s := s) (a := a) (vs := vs) (close_erase h)

theorem endOfFlowS_eq_trap {fl : Flow} {s s₂ : Store H}
    (h : endOfFlowS fl s = .ret (.inr ()) s₂) : fl = .trap ∧ s = s₂ := by
  rcases fl <;> simp_all [endOfFlowS]

theorem tailAnsS_inl_ne {m n : Nat} {b : List Val ⊕ Nat} {s s₂ : Store H} :
    tailAnsS m n (.inl b) s ≠ .ret (.inr ()) s₂ := by
  rcases b with ws | t <;>
    simp [tailAnsS, ansFlow, CallX.tailFlow, exitFlow, endOfFlowS]

/-- **A returning session behaviour is exactly a returning canonical behaviour.** -/
theorem mem_ret_iff {a : Nat} {s s₂ : Store H} {vs : List Val} {cs : List (Call (wasmHostSig H))}
    {b : List Val ⊕ Nat} :
    (cs, .ret (.inl b) s₂) ∈ Shape.close wasmHOpenXPS a s vs ↔
      (cs, .ret b s₂) ∈ Shape.close wasmHOpenXP a s vs := by
  refine ⟨fun h => close_erase h, fun h => ?_⟩
  obtain ⟨⟨c', e'⟩, hy', hc', he'⟩ := close_lift h
  obtain rfl : c' = cs := hc'
  obtain rfl := eraseEnd_eq_ret he'
  exact hy'

/-! ## Store-keeping traps are Core runs to a trap in their store -/

section Fwd

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **Session behaviours whose store-keeping traps are Core runs to a trap in their store.** -/
def TrapS (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    (wasmHShapeS H).ClosedMod := fun a s us =>
  {y | y ∈ Shape.close wasmHOpenXPS a s us ∧ ∀ s₂, y.2 = .ret (.inr ()) s₂ →
    (coreHostRel host).Consistent y.1 →
    ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi →
      Validation.DefType.funcType? fi.type = some (ps, rs) → TagsOk tags s →
      StoreChkE (ehExt tags) s.funcs → us.length = ps.length →
      ∀ (f : Frame) (c : Admin), c.IsCallRef →
        EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ y.1 ⟨s₂, f, [.trap]⟩}

/-- **Every session behaviour is in `TrapS`**: least-fixpoint induction. -/
theorem closeS_le_trapS {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : Shape.close (wasmHOpenXPS (H := H)) ≤ TrapS tags P host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s us y ⟨x, hx, hS⟩
  have hle : TrapS tags P host ≤ Shape.close (wasmHOpenXPS (H := H)) := fun _ _ _ _ h => h.1
  have hmem : y ∈ Shape.close wasmHOpenXPS a s us := by
    rw [← Shape.resolve_close]
    exact ⟨x, hx, hS.mono hle⟩
  refine ⟨hmem, fun s₂ hy hq fi₀ ps₀ rs₀ hfi₀ hty₀ hts hSt hn f c hcr => ?_⟩
  rcases subst_cases hS with ⟨hp, he⟩ |
    ⟨u, w, g, a₁, s₀, ans, q, c₁, -, -, ⟨hm, -⟩ | ⟨hm, -⟩⟩
  rotate_left
  · exact absurd (hle _ _ _ hm) close_ne_trap
  · exact absurd (hle _ _ _ hm) closeS_ne_div
  rw [hy] at he
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hcode, hty, hrun, hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂', f₂, a', n, args, b, l, hfi, hcode, hty, hrun, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hcode, hty, hxf, rfl⟩
  all_goals
    obtain rfl : fi₀ = fi := Option.some.inj (hfi₀.symm.trans hfi)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty₀.symm.trans hty))
  · -- a Wasm body ending in a flow: a trap in its store
    obtain ⟨rfl, rfl⟩ := endOfFlowS_eq_trap he.symm
    have hbfl : bfl = .trap := by
      rcases bfl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [exitFlow]
    subst hbfl
    rcases evalLXPS_toH hrun with ⟨l', rfl, h'⟩ |
      ⟨-, u, g, args, s₁, s₃, hs, rfl, fi', ps', rs', -, -, hall⟩
    · -- trapping itself
      exact evalLXPh_trap_exact hH hE hfi hcode hty hn hts hSt h' (substPre_toOld hle l' hp) hq f c
        hcr
    · -- its last call answered by a trap, in the store the call's callee traps in
      obtain rfl : s' = s₃ := hs
      have h' := hall (List.replicate (rs'.length + 1) (Val.ref .null)) (by simp)
      obtain ⟨qa, qb, hqy, ha, hb⟩ := substPre_split hp
      have hm := substPre_single hb
      rw [hqy] at hq ⊢
      exact evalLXPh_cut_exact (l₂ := []) hH hE hfi hcode hty hn hts hSt h' rfl
        (substPre_toOld hle u ha)
        (fun fi' ps' rs' h₁ h₂ h₃ h₄ h₅ => hm.2 _ rfl (consistent_right hq) fi' ps' rs' h₁ h₂ h₃ h₄
          h₅)
        hq f c hcr
  · -- a Wasm body ending in a pending tail call, answered by a trap
    rcases b with b | ⟨⟩
    · exact absurd he.symm tailAnsS_inl_ne
    obtain rfl : s₂' = s₂ := by simpa [tailAnsS] using he.symm
    obtain ⟨l', rfl, h'⟩ := (evalLXPS_toH hrun).ok (by simp)
    obtain ⟨qa, qb, hqy, ha, hb⟩ := substPre_split hp
    have hm := substPre_single hb
    rw [hqy] at hq ⊢
    exact evalLXPh_tail_exact hH hE hfi hcode hty hn hts hSt h' (substPre_toOld hle l' ha)
      (fun fi' ps' rs' h₁ h₂ h₃ h₄ h₅ => hm.2 _ rfl (consistent_right hq) fi' ps' rs' h₁ h₂ h₃ h₄
        h₅)
      hq f c hcr
  · -- a host function answering a trap: its one event
    obtain ⟨rfl, rfl⟩ := endOfFlowS_eq_trap he.symm
    have hr : r = .trap := by
      rcases r with w | t | _ <;> simp_all [resFlow, exitFlow]
    subst hr
    generalize y.1 = Y at hp hq ⊢
    cases hp with
    | ext hp =>
      cases hp
      have hm : host hh s us (.returned s' .trap) := hq _ List.mem_cons_self
      exact host_trap_exact hfi hcode hty hn hm f c hcr

/-- **A store-keeping trap of an invocation, with a consistent log, is a Core run of the
invocation to a trap in exactly its store**, every profile. -/
theorem wasmEvFunXPS_trap_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val}
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inr ()) s₂) ∈ wasmEvFunXPS s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    simp [Validation.DefType.funcType?, Validation.Expand.iff.1 he]
  exact invoke_trap_exact hfi ((closeS_le_trapS (P := P) hH hE a s vs h).2 s₂ rfl hc fi _ _ hfi
    hty hts hS hvs.length_eq)

end Fwd

/-! ## Core runs to a trap are store-keeping traps in their store -/

section Back

open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **A Core run of a typed invocation to a trap in `s₂` is the session trap in `s₂`**, with
exactly the run's log (deterministic profile). -/
theorem evRun_wasmEvFunXPS_trap (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩) :
    (cs, .ret (.inr ()) s₂) ∈ wasmEvFunXPS s (a, vs) := by
  obtain ⟨⟨c', e'⟩, hy', hc', he'⟩ :=
    close_lift (evRun_wasmEvFunXP_trap hT hH hE hs hS hts hok hrun)
  obtain rfl : c' = cs := hc'
  rcases eraseEnd_eq_trap he' with rfl | ⟨s₂', rfl⟩
  · exact absurd hy' close_ne_trap
  · obtain ⟨rfl, -⟩ := evRun_trap_det
      (wasmEvFunXPS_trap_evRun (P := profile o) hH hE hts hS hok hy' (evRun_consistent hrun)) hrun
    exact hy'

end Back

end Silmaril.Proofs.Wasm.Abstract.HostClosingS
