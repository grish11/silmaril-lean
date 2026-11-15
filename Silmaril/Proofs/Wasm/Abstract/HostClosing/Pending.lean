module

public import Silmaril.Proofs.Wasm.Abstract.HostClosing.Backward

/-!
# Pending host calls of the logged closed semantics (proofs)

`pendO_of_pendL`/`pendL_of_pendO`: a pending host call of `wasmEvPend` after a consistent log
is a host call reached by `PendO (hostCall host)` from the invocation (or the invocation of a
host function itself), and conversely. The logged reach `ReachL`, its completed calls resolved
consistently, is `ReachO (hostCall host)` (`reachO_of_reachL`, `reachL_of_reachO`), by the
replay lemmas of `Forward`/`Backward` on its prefixes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

theorem allRetL_mono {c c' : (wasmHShape H).ClosedMod} (hc : c ≤ c') {l : List (OCall H)}
    {q : List (ICall H)} (h : AllRetL c l q) : AllRetL c' l q := by
  induction h with
  | nil => exact .nil
  | cons hz _ ih =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hm⟩ := hz
    exact .cons ⟨a, args, s₁, b, s₂, rfl, hc _ _ _ hm⟩ ih

theorem allRetL_of_substPre_aux {c : (wasmHShape H).ClosedMod} {L : List (HCall H)}
    {q : List (ICall H)} (h : Shape.SubstPre c L q) :
    ∀ l : List (OCall H), L = l.map OCall.lift → AllRetL c l q := by
  induction h with
  | nil =>
    intro l hl
    cases l with
    | nil => exact .nil
    | cons z l => cases hl
  | ext _ ih =>
    intro l hl
    cases l with
    | nil => cases hl
    | cons z l =>
      obtain ⟨a, args, s₁, b, s₂, rfl⟩ := OCall.eq_mk z
      simp only [List.map_cons, lift_mk, List.cons.injEq] at hl
      obtain ⟨hz, -⟩ := hl
      cases hz
  | int hc _ ih =>
    intro l hl
    cases l with
    | nil => cases hl
    | cons z l =>
      obtain ⟨a, args, s₁, b, s₂, rfl⟩ := OCall.eq_mk z
      simp only [List.map_cons, lift_mk, List.cons.injEq] at hl
      obtain ⟨hz, hl⟩ := hl
      cases hz
      exact .cons ⟨_, _, _, _, _, rfl, hc⟩ (ih l hl)

theorem substPre_lift_iff {c : (wasmHShape H).ClosedMod} {l : List (OCall H)}
    {q : List (ICall H)} : Shape.SubstPre c (l.map OCall.lift) q ↔ AllRetL c l q := by
  refine ⟨fun h => allRetL_of_substPre_aux h l rfl, fun h => ?_⟩
  induction h with
  | nil => exact .nil
  | cons hz _ ih =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hm⟩ := hz
    exact Shape.SubstPre.int hm ih

/-- **A logged reach whose calls return consistently is a reach of `hostCall host`.** -/
theorem reachO_of_reachL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {y : (wasmOShape H).self.Op} (h : ReachL s f stk es l y) :
    ∀ q, AllRetL (toClosedH host) l q → Cons host q → ReachO (hostCall host) s f stk es y := by
  induction h with
  | here hargs hfi hty => exact fun q h hq => .here ((evalO_of_evalLH hargs).1 q h hq) hfi hty
  | args _ ih => exact fun q h hq => .args (ih q h hq)
  | callK hargs hfi hty _ ih =>
    intro q h hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
    cases h₂ with
    | cons hz h₃ =>
      rw [cons_append, cons_append] at hq
      obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inlH hz hq.2.1 (funcs_of_func? hfi) hty
      exact .callK ((evalO_of_evalLH hargs).1 _ h₁ hq.1) hfi hty hC hvs (hws ▸ ih _ h₃ hq.2.2)
  | opK hi hargs hflat _ ih =>
    intro q h hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
    rw [cons_append] at hq
    exact .opK hi ((evalO_of_evalLH hargs).1 _ h₁ hq.1) hflat (ih _ h₂ hq.2)
  | block har _ ih => exact fun q h hq => .block har (ih q h hq)
  | blockK har hbody hvs _ ih =>
    intro q h hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
    rw [cons_append] at hq
    exact .blockK har ((evalO_of_evalLH hbody).1 _ h₁ hq.1) hvs (ih _ h₂ hq.2)
  | loop har _ ih => exact fun q h hq => .loop har (ih q h hq)
  | loopK har hbody _ ih =>
    intro q h hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
    rw [cons_append] at hq
    exact .loopK har ((evalO_of_evalLH hbody).1 _ h₁ hq.1) (ih _ h₂ hq.2)
  | loopBack har hbody _ ih =>
    intro q h hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
    rw [cons_append] at hq
    exact .loopBack har ((evalO_of_evalLH hbody).1 _ h₁ hq.1) (ih _ h₂ hq.2)
  | cond _ ih => exact fun q h hq => .cond (ih q h hq)
  | arm hc hb har _ ih =>
    intro q h hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
    rw [cons_append] at hq
    exact .arm ((evalO_of_evalLH hc).1 _ h₁ hq.1) hb har (ih _ h₂ hq.2)
  | ifK hc hb har harm hvs _ ih =>
    intro q h hq
    obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := allRetL_append.1 h
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h₁₂
    rw [cons_append, cons_append] at hq
    exact .ifK ((evalO_of_evalLH hc).1 _ h₁ hq.1.1) hb har ((evalO_of_evalLH harm).1 _ h₂ hq.1.2)
      hvs (ih _ h₃ hq.2)

/-- A terminating, non-trapping `hostCall` prefix as a logged run with consistent resolved
calls. -/
theorem evalL_of_evalO_normal {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (d : EvalO (hostCall host) s f stk es r) (hr : r.2.2 ≠ .trap) :
    ∃ l q, EvalL s f stk es l r ∧ AllRetL (Shape.close wasmHOpen) l q ∧ Cons host q := by
  obtain ⟨l, r', q, dL, m, hq⟩ := evalL_of_evalOH (d.mono (hostCall_le_ofClosedH (host := host)))
  obtain ⟨h, rfl⟩ := m.normal hr
  exact ⟨l, q, dL, h, hq⟩

/-- **A reach of `hostCall host` is a logged reach whose calls return consistently.** -/
theorem reachL_of_reachO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachO (hostCall host) s f stk es y) :
    ∃ l q, ReachL s f stk es l y ∧ AllRetL (Shape.close wasmHOpen) l q ∧ Cons host q := by
  induction h with
  | here hargs hfi hty =>
    obtain ⟨l, q, d, h, hq⟩ := evalL_of_evalO_normal hargs nofun
    exact ⟨l, q, .here d hfi hty, h, hq⟩
  | args _ ih =>
    obtain ⟨l, q, d, h, hq⟩ := ih
    exact ⟨l, q, .args d, h, hq⟩
  | @callK s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl y hargs hfi hty hcall hvs _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hargs nofun
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := ih
    obtain ⟨qz, hqz, hz⟩ := ret_ofClosedH_inl (hostCall_le_ofClosedH _ _ _ _ hcall)
      (funcs_of_func? hfi) hty hvs
    refine ⟨_, q₁ ++ (qz ++ q₂), ReachL.callK (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁
      hfi hty (by rw [List.reverse_reverse]; exact d₂),
      allRetL_append.2 ⟨_, _, rfl, h₁, .cons hz h₂⟩, cons_append.2 ⟨hq₁, cons_append.2 ⟨hqz, hq₂⟩⟩⟩
  | opK hi hargs hflat _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hargs nofun
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := ih
    exact ⟨_, _, .opK hi d₁ hflat d₂, allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩,
      cons_append.2 ⟨hq₁, hq₂⟩⟩
  | block har _ ih =>
    obtain ⟨l, q, d, h, hq⟩ := ih
    exact ⟨l, q, .block har d, h, hq⟩
  | @blockK s s₁ f f₁ stk vs bt body es np nr fl y har hbody hvs _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hbody
      (by rintro (h : fl = .trap); subst h; simp [Flow.blockVals] at hvs)
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := ih
    exact ⟨_, _, .blockK har d₁ hvs d₂, allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩,
      cons_append.2 ⟨hq₁, hq₂⟩⟩
  | loop har _ ih =>
    obtain ⟨l, q, d, h, hq⟩ := ih
    exact ⟨l, q, .loop har d, h, hq⟩
  | loopK har hbody _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hbody nofun
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := ih
    exact ⟨_, _, .loopK har d₁ d₂, allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩,
      cons_append.2 ⟨hq₁, hq₂⟩⟩
  | loopBack har hbody _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hbody nofun
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := ih
    exact ⟨_, _, .loopBack har d₁ d₂, allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩,
      cons_append.2 ⟨hq₁, hq₂⟩⟩
  | cond _ ih =>
    obtain ⟨l, q, d, h, hq⟩ := ih
    exact ⟨l, q, .cond d, h, hq⟩
  | arm hc hb har _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hc nofun
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := ih
    exact ⟨_, _, .arm d₁ hb har d₂, allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩,
      cons_append.2 ⟨hq₁, hq₂⟩⟩
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl y hc hb har harm hvs _ ih =>
    obtain ⟨l₁, q₁, d₁, h₁, hq₁⟩ := evalL_of_evalO_normal hc nofun
    obtain ⟨l₂, q₂, d₂, h₂, hq₂⟩ := evalL_of_evalO_normal harm
      (by rintro (h : fl = .trap); subst h; simp [Flow.blockVals] at hvs)
    obtain ⟨l₃, q₃, d₃, h₃, hq₃⟩ := ih
    exact ⟨_, _, .ifK d₁ hb har d₂ hvs d₃,
      allRetL_append.2 ⟨_, _, rfl, allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩, h₃⟩,
      cons_append.2 ⟨cons_append.2 ⟨hq₁, hq₂⟩, hq₃⟩⟩

/-- **A consistent pending call is a pending host call of `hostCall host`.** -/
theorem pendO_of_pendL {s : Store H} {a : Nat} {vs : List Val} {cs : List (ICall H)}
    {m : (wasmHostSig H).Op} (h : PendL s a vs cs m) (hc : Cons host cs) :
    ∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
      (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧
        y.2.2.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ m = (hh, y.2.2, y.2.1) := by
  induction h with
  | self hf hcode => exact ⟨_, _, _, .inl rfl, hf, hcode, rfl⟩
  | @desc s a vs fi fn l q q' z m hf hcode hr hq _ ih =>
    rw [cons_append] at hc
    have hR := reachO_of_reachL hr q
      (allRetL_mono close_le_toClosedH (substPre_lift_iff.1 hq)) hc.1
    obtain ⟨y, fi', hh, hy, hfi', hc', rfl⟩ := ih hc.2
    refine ⟨y, fi', hh, .inr ?_, hfi', hc', rfl⟩
    rcases hy with rfl | hy
    · exact .body hf hcode hR
    · exact .desc hf hcode hR hy

/-- **A pending host call of `hostCall host` is a consistent pending call.** -/
theorem pendL_of_pendO {x y : (wasmOShape H).self.Op} (h : PendO (hostCall host) x y)
    {fi : FuncInst H} {hh : H} (hfi : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .host hh) :
    ∃ cs, PendL x.2.2 x.1 x.2.1 cs (hh, y.2.2, y.2.1) ∧ Cons host cs := by
  induction h with
  | body hf hc hr =>
    obtain ⟨l, q, d, hl, hq⟩ := reachL_of_reachO hr
    exact ⟨q ++ [], .desc hf hc d (substPre_lift_iff.2 hl) (.self hfi hcode),
      cons_append.2 ⟨hq, fun _ h => nomatch h⟩⟩
  | desc hf hc hr _ ih =>
    obtain ⟨l, q, d, hl, hq⟩ := reachL_of_reachO hr
    obtain ⟨cs, hp, hcs⟩ := ih hfi
    exact ⟨q ++ cs, .desc hf hc d (substPre_lift_iff.2 hl) hp, cons_append.2 ⟨hq, hcs⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosing
