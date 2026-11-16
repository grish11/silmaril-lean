module

public import Silmaril.Wasm.Abstract.OpenStrat.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms
public import Silmaril.Proofs.Wasm.Abstract.OpenStrat.SatShape

/-!
# The open triple with exceptions is saturated (proofs)

Every call prefix forced by `openTripleXP` is a pending call of `wasmEvPendXP` (`PendLXP`), by the
shape-level lemmas of `SatShape` at `P x c e := PendLXP x.2.2 x.1 x.2.1 c e`:

* `openOkXP`: the calls of every open behaviour of `wasmHOpenXP` pass pending calls: a host
  function's import call is `PendLXP.self`; an internal call is a descent (`reachLXP_of_descends`),
  so `PendLXP.desc` or `PendLXP.tail`;
* `reach_of_logDivXP`, `reach_of_infLXP`: every logged call of a logged local divergence and of a
  productive run within a function is reached after the calls logged before it, so their logs pass
  pending calls (`logOkXP_of_reach`);
* `pendLXP_prefix`: a prefix of a pending call before a host call is pending (by induction; a
  descent's prefix is the prefix of a run cutting the reached call, `reachLXP_cut`);
* `satP_openTripleXP_le`: the four kinds of call prefixes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.OpenStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## Logs of open calls -/

theorem mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' s₂ s₂' : Store H}
    {b b' : List Val ⊕ Nat} (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' := by
  unfold OCall.mk at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem ocall_eq_mk (z : OCall H) : ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ := by
  match z with
  | ⟨.inr ⟨a, args, s₁⟩, (b, s₂)⟩ => exact ⟨a, args, s₁, b, s₂, rfl⟩
  | ⟨.inl m, _⟩ => exact (m : PEmpty).elim

/-- A split of a log at a recorded call. -/
theorem split_mk {l₁' l₂' l₁ l₂ : List (OCall H)} {o : OCall H} {g : Nat} {args : List Val}
    {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    (h : l₁' ++ o :: l₂' = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂) :
    (∃ w, l₁' = l₁ ++ OCall.mk g args s₁ b s₂ :: w) ∨ (l₁ = l₁' ∧ o = OCall.mk g args s₁ b s₂) ∨
      ∃ pre, l₁ = l₁' ++ o :: pre ∧ l₂' = pre ++ OCall.mk g args s₁ b s₂ :: l₂ := by
  rcases split_app h with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
  · exact .inl ⟨w, h₁⟩
  · rcases pre' with _ | ⟨p, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at h₂
      exact .inr (.inl ⟨by simp, h₂.1⟩)
    · simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, h₂⟩ := h₂
      exact .inr (.inr ⟨pre, rfl, h₂⟩)

theorem lift_ne_inl (o : OCall H) {e : (wasmHostSig H).Op} {n : (wasmHostSig H).Ar e} :
    o.lift ≠ ⟨.inl e, n⟩ := by
  obtain ⟨a, args, s₁, b, s₂, rfl⟩ := ocall_eq_mk o
  intro h
  exact Sum.inr_ne_inl (congrArg Sigma.fst h)

theorem not_inl_map_lift {l : List (OCall H)} {u₁ u₂ : List (HCall H)} {e : (wasmHostSig H).Op}
    {n : (wasmHostSig H).Ar e} (h : l.map OCall.lift = u₁ ++ ⟨.inl e, n⟩ :: u₂) : False := by
  have : (⟨.inl e, n⟩ : HCall H) ∈ l.map OCall.lift := by
    rw [h]; simp only [List.mem_append, List.mem_cons, true_or, or_true]
  obtain ⟨o, -, ho⟩ := List.mem_map.1 this
  exact lift_ne_inl o ho

/-! ## Pending calls pass through logs -/

/-- The pending calls of `wasmEvPendXP` at a call of the module. -/
abbrev PXP (x : (wasmHShape H).self.Op) (c : List (Call (wasmHostSig H)))
    (e : (wasmHostSig H).Op) : Prop :=
  PendLXP x.2.2 x.1 x.2.1 c e

/-- **A log of reached calls passes pending calls.** -/
theorem logOkXP_of_reach {x : (wasmHShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {l : List (OCall H)} (hf : x.2.2.funcs[x.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hr : ∀ l₁ g args s₁ b s₂ l₂, l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ →
      ReachLXP x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) l₁
        ⟨g, (args, s₁)⟩) :
    LogOk wasmHOpenXP PXP x (l.map OCall.lift) := by
  intro u₁ cl u₂ q hu hq
  obtain ⟨l₁, l₂', rfl, rfl, hl₂⟩ := List.map_eq_append_iff.1 hu
  obtain ⟨o, l₂, rfl, rfl, -⟩ := List.map_eq_cons_iff.1 hl₂
  obtain ⟨g, args, s₁, b, s₂, rfl⟩ := ocall_eq_mk o
  refine ⟨fun e n h => (lift_ne_inl _ h).elim, fun y ans h c e hP => ?_⟩
  have hy : y = ⟨g, (args, s₁)⟩ := (Sum.inr.inj (congrArg Sigma.fst h)).symm
  subst hy
  exact .desc hf hcode (hr l₁ g args s₁ b s₂ l₂ rfl) hq hP

/-- The log of a logged canonical run of a Wasm body passes pending calls. -/
theorem logOkXP_of_eval {x : (wasmHShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {l : List (OCall H)} {r : Store H × Frame × CallXP.POut} (hf : x.2.2.funcs[x.1]? = some fi)
    (hcode : fi.code = .wasm fn)
    (h : EvalLXPh x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) l r) :
    LogOk wasmHOpenXP PXP x (l.map OCall.lift) :=
  logOkXP_of_reach hf hcode fun _ _ _ _ _ _ _ hl => reachLXP_of_evalLXPh h hl

/-- **The calls of every open behaviour pass pending calls.** -/
theorem openOkXP : OpenOk (wasmHOpenXP (H := H)) PXP := by
  intro x z hz u₁ cl u₂ q hu hq
  refine ⟨fun e n hcl => ?_, fun y ans hcl c e hP => ?_⟩
  · subst hcl
    rcases hz with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, -, rfl⟩ |
      ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n', args, b₀, l, hfi, hc, hty, hE, rfl⟩ |
      ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, -, rfl⟩
    · exact (not_inl_map_lift hu).elim
    · exact (not_inl_map_lift hu).elim
    · rcases u₁ with _ | ⟨_, u₁⟩
      · simp only [List.nil_append, List.cons.injEq] at hu
        obtain ⟨hu, -⟩ := hu
        cases hu
        cases hq
        exact .self hfi hc
      · have := congrArg List.length hu
        simp only [List.length_cons, List.length_nil, List.length_append] at this
        omega
  · subst hcl
    rcases reachLXP_of_descends ⟨z, hz, u₁, ans, u₂, hu, hq⟩ with
      ⟨fi, fn, l, hf, hc, hq', hr | ⟨f₂, n, hE⟩⟩
    · exact .desc hf hc hr hq' hP
    · exact .tail hf hc hE hq' hP

/-! ## Logged local divergence and productive runs reach their calls -/

/-- **Every logged call of a logged local divergence is reached**, after the calls logged before
it. -/
theorem reach_of_logDivXP {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} (h : LogDivXP s f stk es l) :
    ∀ l₁ g args s₁ b s₂ l₂, l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ →
      ReachLXP s f stk es l₁ ⟨g, (args, s₁)⟩ := by
  induction h with
  | div => intro l₁ g args s₁ b s₂ l₂ he; simp at he
  | args _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .args (ih l₁ g args s₁ b s₂ l₂ he)
  | callK hargs hfi hty _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .args (reachLXP_of_evalLXPh hargs h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
      exact .call hargs hfi hty
    · exact .callK hargs hfi hty (ih pre g args s₁ b s₂ l₂ h₂)
  | indK hargs hres hfi hty hy _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .args (reachLXP_of_evalLXPh hargs h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
      exact .ind hargs hres hfi hty hy
    · exact .indK hargs hres hfi hty hy (ih pre g args s₁ b s₂ l₂ h₂)
  | refK hargs hfi hty hy _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .args (reachLXP_of_evalLXPh hargs h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
      exact .ref hargs hfi hty hy
    · exact .refK hargs hfi hty hy (ih pre g args s₁ b s₂ l₂ h₂)
  | opK hi hargs hflat _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .args (reachLXP_of_evalLXPh hargs h₁)
    · exact .opK hi hargs hflat (ih pre g args s₁ b s₂ l₂ h₂)
  | block har _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .block har (ih l₁ g args s₁ b s₂ l₂ he)
  | blockK har hbody hvs _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .block har (reachLXP_of_evalLXPh hbody h₁)
    · exact .blockK har hbody hvs (ih pre g args s₁ b s₂ l₂ h₂)
  | loop har _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .loop har (ih l₁ g args s₁ b s₂ l₂ he)
  | loopK har hbody _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .loop har (reachLXP_of_evalLXPh hbody h₁)
    · exact .loopK har hbody (ih pre g args s₁ b s₂ l₂ h₂)
  | loopBack har hbody _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .loop har (reachLXP_of_evalLXPh hbody h₁)
    · exact .loopBack har hbody (ih pre g args s₁ b s₂ l₂ h₂)
  | cond _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .cond (ih l₁ g args s₁ b s₂ l₂ he)
  | arm hc hb har _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .cond (reachLXP_of_evalLXPh hc h₁)
    · exact .arm hc hb har (ih pre g args s₁ b s₂ l₂ h₂)
  | ifK hc hb har harm hvs _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · rcases split_app h₁ with ⟨w', h₁'⟩ | ⟨pre', rfl, h₂'⟩
      · exact .cond (reachLXP_of_evalLXPh hc h₁')
      · exact .arm hc hb har (reachLXP_of_evalLXPh harm h₂')
    · exact .ifK hc hb har harm hvs (ih pre g args s₁ b s₂ l₂ h₂)
  | handler har _ ih =>
    exact fun l₁ g args s₁ b s₂ l₂ he => .handler har (ih l₁ g args s₁ b s₂ l₂ he)
  | tryK har hbody hvs _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .handler har (reachLXP_of_evalLXPh hbody h₁)
    · exact .tryK har hbody hvs (ih pre g args s₁ b s₂ l₂ h₂)

/-- Reaches along a stream with a log in front. -/
theorem reach_streamAppend {l : List (OCall H)} {ω : Nat → OCall H}
    {R : List (OCall H) → (wasmOShape H).self.Op → Prop}
    (hl : ∀ l₁ g args s₁ b s₂ l₂, l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ → R l₁ ⟨g, (args, s₁)⟩)
    (hω : ∀ k g args s₁ b s₂, ω k = OCall.mk g args s₁ b s₂ →
      R (l ++ streamTake ω k) ⟨g, (args, s₁)⟩) :
    ∀ k g args s₁ b s₂, (l ++ω ω) k = OCall.mk g args s₁ b s₂ →
      R (streamTake (l ++ω ω) k) ⟨g, (args, s₁)⟩ := by
  intro k g args s₁ b s₂ hk
  rcases streamAppend_cases l ω k with ⟨w, h₁⟩ | ⟨j, h₁, h₂⟩
  · rw [hk] at h₁
    exact hl _ g args s₁ b s₂ w h₁
  · rw [h₁]
    exact hω j g args s₁ b s₂ (h₂ ▸ hk)

/-- The calls of a log ending in one call. -/
theorem split_snoc_mk {l₁ L₁ L₂ : List (OCall H)} {o : OCall H} {g : Nat} {args : List Val}
    {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    (h : l₁ ++ [o] = L₁ ++ OCall.mk g args s₁ b s₂ :: L₂) :
    (∃ w, l₁ = L₁ ++ OCall.mk g args s₁ b s₂ :: w) ∨ (L₁ = l₁ ∧ o = OCall.mk g args s₁ b s₂) := by
  rcases split_mk h with h | h | ⟨pre, -, h₂⟩
  · exact .inl h
  · exact .inr h
  · simp at h₂

/-- **Every call of a productive run within a function is reached**, after the calls before
it. -/
theorem reach_of_infLXP {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {ω : Nat → OCall H} (h : InfLXP s f stk es ω) :
    ∀ k g args s₁ b s₂, ω k = OCall.mk g args s₁ b s₂ →
      ReachLXP s f stk es (streamTake ω k) ⟨g, (args, s₁)⟩ := by
  induction h with
  | args _ ih => exact fun k g args s₁ b s₂ hk => .args (ih k g args s₁ b s₂ hk)
  | callK hargs hfi hty _ ih =>
    refine reach_streamAppend (fun L₁ g args s₁ b s₂ L₂ he => ?_) (fun k g args s₁ b s₂ hk => ?_)
    · rcases split_snoc_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩
      · exact .args (reachLXP_of_evalLXPh hargs h₁)
      · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
        exact .call hargs hfi hty
    · simpa using ReachLXP.callK hargs hfi hty (ih k g args s₁ b s₂ hk)
  | indK hargs hres hfi hty hy _ ih =>
    refine reach_streamAppend (fun L₁ g args s₁ b s₂ L₂ he => ?_) (fun k g args s₁ b s₂ hk => ?_)
    · rcases split_snoc_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩
      · exact .args (reachLXP_of_evalLXPh hargs h₁)
      · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
        exact .ind hargs hres hfi hty hy
    · simpa using ReachLXP.indK hargs hres hfi hty hy (ih k g args s₁ b s₂ hk)
  | refK hargs hfi hty hy _ ih =>
    refine reach_streamAppend (fun L₁ g args s₁ b s₂ L₂ he => ?_) (fun k g args s₁ b s₂ hk => ?_)
    · rcases split_snoc_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩
      · exact .args (reachLXP_of_evalLXPh hargs h₁)
      · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
        exact .ref hargs hfi hty hy
    · simpa using ReachLXP.refK hargs hfi hty hy (ih k g args s₁ b s₂ hk)
  | opK hi hargs hflat _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .args (reachLXP_of_evalLXPh hargs he))
      fun k g args s₁ b s₂ hk => .opK hi hargs hflat (ih k g args s₁ b s₂ hk)
  | block har _ ih => exact fun k g args s₁ b s₂ hk => .block har (ih k g args s₁ b s₂ hk)
  | blockK har hbody hvs _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .block har (reachLXP_of_evalLXPh hbody he))
      fun k g args s₁ b s₂ hk => .blockK har hbody hvs (ih k g args s₁ b s₂ hk)
  | loop har _ ih => exact fun k g args s₁ b s₂ hk => .loop har (ih k g args s₁ b s₂ hk)
  | loopK har hbody _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .loop har (reachLXP_of_evalLXPh hbody he))
      fun k g args s₁ b s₂ hk => .loopK har hbody (ih k g args s₁ b s₂ hk)
  | loopBack har hbody _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .loop har (reachLXP_of_evalLXPh hbody he))
      fun k g args s₁ b s₂ hk => .loopBack har hbody (ih k g args s₁ b s₂ hk)
  | @loopInf s f stk bt body es np nr ω st l h0 har hit hω =>
    intro k g args s₁ b s₂ hk
    obtain ⟨n, hn⟩ := hω.2 (k + 1)
    obtain ⟨j, pre, w, hj, hpre⟩ := flatMap_split l n (prefix_split (hω.1 n) (k := k) (by omega))
    rw [hk] at hj
    have back : ∀ d i, i + d = j →
        ReachLXP (st i).1 (st i).2.1 (st i).2.2 (.loop bt body :: es)
          ((List.range d).flatMap (fun t => l (i + t)) ++ pre) ⟨g, (args, s₁)⟩ := by
      intro d
      induction d with
      | zero =>
        intro i hi
        obtain ⟨vs, hE, -⟩ := hit i
        simp only [Nat.add_zero] at hi
        subst hi
        exact .loop (har i) (reachLXP_of_evalLXPh hE hj)
      | succ d ih =>
        intro i hi
        obtain ⟨vs, hE, hst⟩ := hit i
        have := ih (i + 1) (by omega)
        rw [hst] at this
        have e : (List.range (d + 1)).flatMap (fun t => l (i + t)) =
            l i ++ (List.range d).flatMap (fun t => l (i + 1 + t)) := by
          rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
          simp only [Nat.add_zero]
          congr 2
          funext t
          congr 1
          omega
        rw [e, List.append_assoc]
        exact .loopBack (har i) hE this
    have := back j 0 (by omega)
    rw [h0] at this
    simpa [hpre] using this
  | cond _ ih => exact fun k g args s₁ b s₂ hk => .cond (ih k g args s₁ b s₂ hk)
  | arm hc hb har _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .cond (reachLXP_of_evalLXPh hc he))
      fun k g args s₁ b s₂ hk => .arm hc hb har (ih k g args s₁ b s₂ hk)
  | ifK hc hb har harm hvs _ ih =>
    refine reach_streamAppend (fun L₁ g args s₁ b s₂ L₂ he => ?_)
      (fun k g args s₁ b s₂ hk => ?_)
    · rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
      · exact .cond (reachLXP_of_evalLXPh hc h₁)
      · exact .arm hc hb har (reachLXP_of_evalLXPh harm h₂)
    · simpa using ReachLXP.ifK hc hb har harm hvs (ih k g args s₁ b s₂ hk)
  | handler har _ ih => exact fun k g args s₁ b s₂ hk => .handler har (ih k g args s₁ b s₂ hk)
  | tryK har hbody hvs _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .handler har (reachLXP_of_evalLXPh hbody he))
      fun k g args s₁ b s₂ hk => .tryK har hbody hvs (ih k g args s₁ b s₂ hk)

/-! ## Prefixes of pending calls -/

/-- **A prefix of a pending call before a host call is a pending call.** -/
theorem pendLXP_prefix {s : Store H} {a : Nat} {vs : List Val} {c : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : PendLXP s a vs c m) :
    ∀ {pre post : List (Call (wasmHostSig H))} {ev : Call (wasmHostSig H)},
      c = pre ++ ev :: post → PendLXP s a vs pre ev.1 := by
  induction h with
  | self => intro pre post ev h; simp at h
  | @desc s a vs fi fn l q q' z m hf hcode hr hq _ ih =>
    intro pre post ev h
    rcases split_app h with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
    · obtain ⟨ws, f', d⟩ := reachLXP_cut hr
      have hl := logOkXP_of_eval (x := ⟨a, (vs, s)⟩) hf hcode d
      rw [List.map_append] at hl
      exact logOk_pend openOkXP (logOk_prefix hl) hq h₁
    · exact .desc hf hcode hr hq (ih h₂)
  | @tail s s₁ a vs fi fn f₂ a' n args l q q' m hf hcode hbody hq _ ih =>
    intro pre post ev h
    rcases split_app h with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
    · exact logOk_pend openOkXP (logOkXP_of_eval (x := ⟨a, (vs, s)⟩) hf hcode hbody) hq h₁
    · exact .tail hf hcode hbody hq (ih h₂)

/-! ## The call prefixes of the open triple -/

/-- **Every call prefix of the open triple with exceptions is a pending call.** -/
theorem satP_openTripleXP_le (s : Store H) (p : Nat × List Val) :
    StratObs.satP openTripleXP s p ⊆ wasmEvPendXP s p := by
  rintro ⟨c, e⟩ (h | ⟨d, m', hd, n, c', rfl⟩ | ⟨d, en, hd, n, c', rfl⟩ | ⟨ω, hω, k, rfl, rfl⟩)
  · exact h
  · exact pendLXP_prefix (ev := ⟨e, n⟩) hd rfl
  · refine closeDLog_pend (x := ⟨p.1, (p.2, s)⟩) (ev := ⟨e, n⟩) openOkXP ?_ hd rfl
    rintro z _ ⟨fi, fn, l, hf, hc, hL, rfl⟩
    exact logOkXP_of_reach hf hc (reach_of_logDivXP hL)
  · refine closeInfL_pend (x := ⟨p.1, (p.2, s)⟩) openOkXP ?_ hω k
    rintro z _ ⟨fi, fn, ω, hf, hc, hI, rfl⟩ n
    rw [streamTake_map]
    refine logOkXP_of_reach hf hc fun l₁ g args s₁ b s₂ l₂ he => ?_
    obtain ⟨h₁, h₂⟩ := streamTake_split he
    rw [h₁]
    exact reach_of_infLXP hI _ g args s₁ b s₂ h₂.symm

end Silmaril.Proofs.Wasm.Abstract.OpenStrat
