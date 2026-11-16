module

public import Silmaril.Proofs.Wasm.Abstract.HostClosing.Forward

/-!
# `hostCall` outcomes as logged closed behaviours (proofs)

`hostCall_le_ofClosedH`: every outcome of `hostCall host` is, through its exit flow, a
behaviour of `Shape.close wasmHOpen` with a consistent host log. Least-fixpoint induction:
an `EvalO` run answered by such behaviours is mirrored by a logged run whose log
`Shape.Subst` resolves (`evalL_of_evalOH`); a host answer is the host function's one import
call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

/-- A call relation answered by a closed module through exit flows, with consistent logs. -/
def ofClosedH (host : HostSemantics H) (c : (wasmHShape H).ClosedMod) : CallRel H :=
  fun s a vs out =>
    ∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (fl : Flow),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
      exitFlow rs.length out.2 = some fl → ∃ q, Cons host q ∧ (q, endOfFlow fl out.1) ∈ c a s vs

/-- How a logged run reproduces an `EvalO` run, with the import calls `q` of its calls. -/
def MirrorsL (c : (wasmHShape H).ClosedMod) (r : Store H × Frame × Flow) (l : List (OCall H))
    (q : List (ICall H)) (r' : Store H × Frame × Flow) : Prop :=
  (AllRetL c l q ∧ r' = r) ∨ (r.2.2 = .trap ∧ TrapAtL c l q ∧ ∃ t, r'.2.2 = .throw t)

theorem MirrorsL.normal {c : (wasmHShape H).ClosedMod} {r r' : Store H × Frame × Flow}
    {l : List (OCall H)} {q : List (ICall H)} (h : MirrorsL c r l q r') (hr : r.2.2 ≠ .trap) :
    AllRetL c l q ∧ r' = r :=
  h.resolve_right fun h' => hr h'.1

theorem MirrorsL.append {c : (wasmHShape H).ClosedMod} {r r' : Store H × Frame × Flow}
    {u l : List (OCall H)} {q₁ q₂ : List (ICall H)} (hu : AllRetL c u q₁)
    (h : MirrorsL c r l q₂ r') : MirrorsL c r (u ++ l) (q₁ ++ q₂) r' := by
  rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, h₃⟩
  · exact .inl ⟨allRetL_append.2 ⟨_, _, rfl, hu, h⟩, rfl⟩
  · exact .inr ⟨h₁, trapAtL_append_right hu h₂, h₃⟩

theorem ret_ofClosedH_inl {c : (wasmHShape H).ClosedMod} {s₁ s₂ : Store H} {a : Nat}
    {args : List Val} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
    {vs : List Val} (hC : ofClosedH host c s₁ a args (s₂, fl)) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : fl.retVals = some vs) :
    ∃ q, Cons host q ∧ RetL c (OCall.mk a args s₁ (.inl (vs.take rs.length).reverse) s₂) q := by
  obtain ⟨q, hq, hm⟩ := hC fi ps rs (.normal (vs.take rs.length).reverse) hfi hty (by
    rcases fl with w | ⟨_ | k, w⟩ | w | _ | x <;> simp_all [Flow.retVals, exitFlow])
  exact ⟨q, hq, a, args, s₁, _, s₂, rfl, hm⟩

/-- An `EvalO` run answered by `ofClosedH host c` is mirrored by a logged run. -/
theorem evalL_of_evalOH {c : (wasmHShape H).ClosedMod} {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : EvalO (ofClosedH host c) s f stk es r) :
    ∃ l r' q, EvalL s f stk es l r' ∧ MirrorsL c r l q r' ∧ Cons host q := by
  induction h with
  | nil => exact ⟨[], _, [], .nil, .inl ⟨.nil, rfl⟩, fun _ h => nomatch h⟩
  | argsAbort _ hfl ih =>
    obtain ⟨l, r', q, d, h, hq⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, q, .argsAbort d hfl, .inl ⟨h, rfl⟩, hq⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, q, .argsAbort d Flow.notNormal_throw, .inr ⟨h₁, h₂, t, rfl⟩, hq⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, h₂, hq₂⟩ := ih₂
    obtain ⟨qz, hqz, hz⟩ := ret_ofClosedH_inl hcall (funcs_of_func? hfi) hty hvs
    have d := EvalL.callRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁ hfi hty
      (by rw [List.reverse_reverse]; exact d₂)
    refine ⟨_, _, (q₁ ++ qz) ++ q₂, d, ?_, cons_append.2 ⟨cons_append.2 ⟨hq₁, hqz⟩, hq₂⟩⟩
    rw [← List.singleton_append, ← List.append_assoc]
    exact MirrorsL.append (allRetL_append.2 ⟨_, _, rfl, h₁, allRetL_singleton hz⟩) h₂
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨qz, hqz, hm⟩ := hcall fi ps rs .trap (funcs_of_func? hfi) hty rfl
    have hz : TrapsL c (OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr 0) s₂) qz :=
      ⟨_, _, _, _, _, rfl, hm⟩
    exact ⟨_, _, q₁ ++ qz, EvalL.callThrow (t := 0) (s₂ := s₂) d₁ hfi hty,
      .inr ⟨rfl, trapAtL_append_right h₁ (.here hz), 0, rfl⟩, cons_append.2 ⟨hq₁, hqz⟩⟩
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨qz, hqz, hm⟩ := hcall fi ps rs (.throw t) (funcs_of_func? hfi) hty rfl
    have hz : RetL c (OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr t) s₂) qz :=
      ⟨_, _, _, _, _, rfl, hm⟩
    exact ⟨_, _, q₁ ++ qz, EvalL.callThrow (t := t) (s₂ := s₂) d₁ hfi hty,
      .inl ⟨allRetL_append.2 ⟨_, _, rfl, h₁, allRetL_singleton hz⟩, rfl⟩,
      cons_append.2 ⟨hq₁, hqz⟩⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, h₂, hq₂⟩ := ih₂
    exact ⟨_, _, _, .opOk hi d₁ hflat d₂, h₂.append h₁, cons_append.2 ⟨hq₁, hq₂⟩⟩
  | opStop hi _ hflat hfl ih =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨_, _, _, .opStop hi d₁ hflat hfl, .inl ⟨h₁, rfl⟩, hq₁⟩
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal (by rintro (h : fl = .trap); subst h; simp [Flow.blockVals] at hvs)
    obtain ⟨l₂, r₂, q₂, d₂, h₂, hq₂⟩ := ih₂
    exact ⟨_, _, _, .blockOk har d₁ hvs d₂, h₂.append h₁, cons_append.2 ⟨hq₁, hq₂⟩⟩
  | blockBrk har _ ih =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨_, _, _, .blockBrk har d₁, .inl ⟨h₁, rfl⟩, hq₁⟩
  | blockEsc har _ hfl ih =>
    obtain ⟨l, r', q, d, h, hq⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, q, .blockEsc har d hfl, .inl ⟨h, rfl⟩, hq⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, q, .blockEsc har d trivial, .inr ⟨h₁, h₂, t, rfl⟩, hq⟩
  | loopOk har _ _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, h₂, hq₂⟩ := ih₂
    exact ⟨_, _, _, .loopOk har d₁ d₂, h₂.append h₁, cons_append.2 ⟨hq₁, hq₂⟩⟩
  | loopBack har _ _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, h₂, hq₂⟩ := ih₂
    exact ⟨_, _, _, .loopBack har d₁ d₂, h₂.append h₁, cons_append.2 ⟨hq₁, hq₂⟩⟩
  | loopBrk har _ ih =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨_, _, _, .loopBrk har d₁, .inl ⟨h₁, rfl⟩, hq₁⟩
  | loopEsc har _ hfl ih =>
    obtain ⟨l, r', q, d, h, hq⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, q, .loopEsc har d hfl, .inl ⟨h, rfl⟩, hq⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, q, .loopEsc har d trivial, .inr ⟨h₁, h₂, t, rfl⟩, hq⟩
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c' t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, m₂, hq₂⟩ := ih₂
    obtain ⟨h₂, rfl⟩ := m₂.normal (by rintro (h : fl = .trap); subst h; simp [Flow.blockVals] at hvs)
    obtain ⟨l₃, r₃, q₃, d₃, h₃, hq₃⟩ := ih₃
    exact ⟨_, _, _, .ifOk d₁ hb har d₂ hvs d₃,
      h₃.append (allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩),
      cons_append.2 ⟨cons_append.2 ⟨hq₁, hq₂⟩, hq₃⟩⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, m₂, hq₂⟩ := ih₂
    obtain ⟨h₂, rfl⟩ := m₂.normal nofun
    exact ⟨_, _, _, .ifBrk d₁ hb har d₂, .inl ⟨allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩, rfl⟩,
      cons_append.2 ⟨hq₁, hq₂⟩⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    obtain ⟨l₁, r₁, q₁, d₁, m₁, hq₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, q₂, d₂, h₂, hq₂⟩ := ih₂
    rcases h₂ with ⟨h₂, rfl⟩ | ⟨h₂₁, h₂₂, t, h₂₃⟩
    · exact ⟨_, _, _, .ifEsc d₁ hb har d₂ hfl, .inl ⟨allRetL_append.2 ⟨_, _, rfl, h₁, h₂⟩, rfl⟩,
        cons_append.2 ⟨hq₁, hq₂⟩⟩
    · obtain ⟨s', f', fl'⟩ := r₂
      subst h₂₃
      exact ⟨_, _, _, .ifEsc d₁ hb har d₂ trivial,
        .inr ⟨h₂₁, trapAtL_append_right h₁ h₂₂, t, rfl⟩, cons_append.2 ⟨hq₁, hq₂⟩⟩
  | ifAbort _ hfl ih =>
    obtain ⟨l, r', q, d, h, hq⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, q, .ifAbort d hfl, .inl ⟨h, rfl⟩, hq⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, q, .ifAbort d Flow.notNormal_throw, .inr ⟨h₁, h₂, t, rfl⟩, hq⟩

/-- **Every `hostCall` outcome is a consistent closed behaviour.** -/
theorem hostCall_le_ofClosedH :
    (hostCall host : CallRel H) ≤ ofClosedH host (Shape.close wasmHOpen) := by
  refine OrderHom.lfp_le _ ?_
  rintro s a vs ⟨s', bfl⟩ (⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩ | ⟨fi, hh, r, hfi, hc, hm, hout⟩)
  · intro fi' ps' rs' fl hfi' hty' hx
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    obtain ⟨l, r', q, dL, h, hq⟩ := evalL_of_evalOH d
    refine ⟨q, hq, ?_⟩
    rw [Shape.close, ← OrderHom.map_lfp]
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨(l.map OCall.lift, endOfFlow fl s'),
        .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, dL, hx, rfl⟩, subst_of_allRetL h⟩
    · obtain ⟨s'', f'', fl'⟩ := r'
      obtain rfl : bfl = .trap := h₁
      obtain rfl : fl = .trap := by simpa [exitFlow] using hx.symm
      subst h₃
      exact ⟨(l.map OCall.lift, endOfFlow (.throw t) s''),
        .inl ⟨fi, fn, ps, rs, s'', f'', .throw t, .throw t, l, hfi, hc, hty, dL, rfl, rfl⟩,
        subst_of_trapAtL h₂⟩
  · intro fi' ps' rs' fl hfi' hty' hx
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    simp only at hout
    subst hout
    refine ⟨[⟨(hh, s, vs), (s', r)⟩], ?_, ?_⟩
    · intro z hz
      simp only [List.mem_singleton] at hz
      subst hz
      exact hm
    · rw [Shape.close, ← OrderHom.map_lfp]
      exact ⟨([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlow fl s'),
        .inr ⟨fi, hh, ps', rs', s', r, fl, hfi, hc, hty', hx, rfl⟩, .ext (.nil _)⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosing
