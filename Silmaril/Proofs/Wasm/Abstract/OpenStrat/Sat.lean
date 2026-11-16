module

public import Silmaril.Proofs.Wasm.Abstract.OpenStrat.SatXP

/-!
# The exception-free open triple is saturated (proofs)

Every call prefix forced by `openTriple` is a pending call of `wasmEvPend` (`PendL`), as in
`SatXP`, at `P x c e := PendL x.2.2 x.1 x.2.1 c e`:

* `openOk`: the calls of every open behaviour of `wasmHOpen` pass pending calls (a host function's
  import call is `PendL.self`; an internal call is a descent, `reachL_of_descends`, so
  `PendL.desc`);
* `reach_of_logDiv`, `reach_of_infL`: every logged call of a logged local divergence and of a
  productive run within a function is reached after the calls logged before it;
* `pendL_prefix`: a prefix of a pending call before a host call is pending (a descent's prefix is
  the prefix of a run answering the reached call by an exception, `reachL_throw`);
* `satP_openTriple_le`: the four kinds of call prefixes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.OpenStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## Pending calls pass through logs -/

/-- The pending calls of `wasmEvPend` at a call of the module. -/
abbrev PN (x : (wasmHShape H).self.Op) (c : List (Call (wasmHostSig H)))
    (e : (wasmHostSig H).Op) : Prop :=
  PendL x.2.2 x.1 x.2.1 c e

/-- **A log of reached calls passes pending calls.** -/
theorem logOk_of_reach {x : (wasmHShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {l : List (OCall H)} (hf : x.2.2.funcs[x.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hr : ∀ l₁ g args s₁ b s₂ l₂, l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ →
      ReachL x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) l₁
        ⟨g, (args, s₁)⟩) :
    LogOk wasmHOpen PN x (l.map OCall.lift) := by
  intro u₁ cl u₂ q hu hq
  obtain ⟨l₁, l₂', rfl, rfl, hl₂⟩ := List.map_eq_append_iff.1 hu
  obtain ⟨o, l₂, rfl, rfl, -⟩ := List.map_eq_cons_iff.1 hl₂
  obtain ⟨g, args, s₁, b, s₂, rfl⟩ := ocall_eq_mk o
  refine ⟨fun e n h => (lift_ne_inl _ h).elim, fun y ans h c e hP => ?_⟩
  have hy : y = ⟨g, (args, s₁)⟩ := (Sum.inr.inj (congrArg Sigma.fst h)).symm
  subst hy
  exact .desc hf hcode (hr l₁ g args s₁ b s₂ l₂ rfl) hq hP

/-- The log of a logged native run of a Wasm body passes pending calls. -/
theorem logOk_of_eval {x : (wasmHShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {l : List (OCall H)} {r : Store H × Frame × Flow} (hf : x.2.2.funcs[x.1]? = some fi)
    (hcode : fi.code = .wasm fn)
    (h : EvalL x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) l r) :
    LogOk wasmHOpen PN x (l.map OCall.lift) :=
  logOk_of_reach hf hcode fun _ _ _ _ _ _ _ hl => reachL_of_evalL h hl

/-- **The calls of every open behaviour pass pending calls.** -/
theorem openOk : OpenOk (wasmHOpen (H := H)) PN := by
  intro x z hz u₁ cl u₂ q hu hq
  refine ⟨fun e n hcl => ?_, fun y ans hcl c e hP => ?_⟩
  · subst hcl
    rcases hz with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, -, rfl⟩ |
      ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, -, rfl⟩
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
    obtain ⟨fi, fn, ps, rs, l, hf, hc, -, hr, hq'⟩ :=
      reachL_of_descends ⟨z, hz, u₁, ans, u₂, hu, hq⟩
    exact .desc hf hc hr hq' hP

/-! ## Logged local divergence and productive runs reach their calls -/

/-- **Every logged call of a logged local divergence is reached**, after the calls logged before
it. -/
theorem reach_of_logDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} (h : LogDiv s f stk es l) :
    ∀ l₁ g args s₁ b s₂ l₂, l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ →
      ReachL s f stk es l₁ ⟨g, (args, s₁)⟩ := by
  induction h with
  | div => intro l₁ g args s₁ b s₂ l₂ he; simp at he
  | args _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .args (ih l₁ g args s₁ b s₂ l₂ he)
  | callK hargs hfi hty _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .args (reachL_of_evalL hargs h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
      exact .here hargs hfi hty
    · exact .callK hargs hfi hty (ih pre g args s₁ b s₂ l₂ h₂)
  | opK hi hargs hflat _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .args (reachL_of_evalL hargs h₁)
    · exact .opK hi hargs hflat (ih pre g args s₁ b s₂ l₂ h₂)
  | block har _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .block har (ih l₁ g args s₁ b s₂ l₂ he)
  | blockK har hbody hvs _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .block har (reachL_of_evalL hbody h₁)
    · exact .blockK har hbody hvs (ih pre g args s₁ b s₂ l₂ h₂)
  | loop har _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .loop har (ih l₁ g args s₁ b s₂ l₂ he)
  | loopK har hbody _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .loop har (reachL_of_evalL hbody h₁)
    · exact .loopK har hbody (ih pre g args s₁ b s₂ l₂ h₂)
  | loopBack har hbody _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .loop har (reachL_of_evalL hbody h₁)
    · exact .loopBack har hbody (ih pre g args s₁ b s₂ l₂ h₂)
  | cond _ ih => exact fun l₁ g args s₁ b s₂ l₂ he => .cond (ih l₁ g args s₁ b s₂ l₂ he)
  | arm hc hb har _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · exact .cond (reachL_of_evalL hc h₁)
    · exact .arm hc hb har (ih pre g args s₁ b s₂ l₂ h₂)
  | ifK hc hb har harm hvs _ ih =>
    intro l₁ g args s₁ b s₂ l₂ he
    rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
    · rcases split_app h₁ with ⟨w', h₁'⟩ | ⟨pre', rfl, h₂'⟩
      · exact .cond (reachL_of_evalL hc h₁')
      · exact .arm hc hb har (reachL_of_evalL harm h₂')
    · exact .ifK hc hb har harm hvs (ih pre g args s₁ b s₂ l₂ h₂)

/-- **Every call of a productive run within a function is reached**, after the calls before
it. -/
theorem reach_of_infL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {ω : Nat → OCall H} (h : InfL s f stk es ω) :
    ∀ k g args s₁ b s₂, ω k = OCall.mk g args s₁ b s₂ →
      ReachL s f stk es (streamTake ω k) ⟨g, (args, s₁)⟩ := by
  induction h with
  | args _ ih => exact fun k g args s₁ b s₂ hk => .args (ih k g args s₁ b s₂ hk)
  | callK hargs hfi hty _ ih =>
    refine reach_streamAppend (fun L₁ g args s₁ b s₂ L₂ he => ?_) (fun k g args s₁ b s₂ hk => ?_)
    · rcases split_snoc_mk he with ⟨w, h₁⟩ | ⟨rfl, h₁⟩
      · exact .args (reachL_of_evalL hargs h₁)
      · obtain ⟨rfl, rfl, rfl⟩ := mk_inj h₁
        exact .here hargs hfi hty
    · simpa using ReachL.callK hargs hfi hty (ih k g args s₁ b s₂ hk)
  | opK hi hargs hflat _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .args (reachL_of_evalL hargs he))
      fun k g args s₁ b s₂ hk => .opK hi hargs hflat (ih k g args s₁ b s₂ hk)
  | block har _ ih => exact fun k g args s₁ b s₂ hk => .block har (ih k g args s₁ b s₂ hk)
  | blockK har hbody hvs _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .block har (reachL_of_evalL hbody he))
      fun k g args s₁ b s₂ hk => .blockK har hbody hvs (ih k g args s₁ b s₂ hk)
  | loop har _ ih => exact fun k g args s₁ b s₂ hk => .loop har (ih k g args s₁ b s₂ hk)
  | loopK har hbody _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .loop har (reachL_of_evalL hbody he))
      fun k g args s₁ b s₂ hk => .loopK har hbody (ih k g args s₁ b s₂ hk)
  | loopBack har hbody _ ih =>
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .loop har (reachL_of_evalL hbody he))
      fun k g args s₁ b s₂ hk => .loopBack har hbody (ih k g args s₁ b s₂ hk)
  | @loopInf s f stk bt body es np nr ω st l h0 har hit hω =>
    intro k g args s₁ b s₂ hk
    obtain ⟨n, hn⟩ := hω.2 (k + 1)
    obtain ⟨j, pre, w, hj, hpre⟩ := flatMap_split l n (prefix_split (hω.1 n) (k := k) (by omega))
    rw [hk] at hj
    have back : ∀ d i, i + d = j →
        ReachL (st i).1 (st i).2.1 (st i).2.2 (.loop bt body :: es)
          ((List.range d).flatMap (fun t => l (i + t)) ++ pre) ⟨g, (args, s₁)⟩ := by
      intro d
      induction d with
      | zero =>
        intro i hi
        obtain ⟨vs, hE, -⟩ := hit i
        simp only [Nat.add_zero] at hi
        subst hi
        exact .loop (har i) (reachL_of_evalL hE hj)
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
    exact reach_streamAppend (fun _ _ _ _ _ _ _ he => .cond (reachL_of_evalL hc he))
      fun k g args s₁ b s₂ hk => .arm hc hb har (ih k g args s₁ b s₂ hk)
  | ifK hc hb har harm hvs _ ih =>
    refine reach_streamAppend (fun L₁ g args s₁ b s₂ L₂ he => ?_)
      (fun k g args s₁ b s₂ hk => ?_)
    · rcases split_app he with ⟨w, h₁⟩ | ⟨pre, rfl, h₂⟩
      · exact .cond (reachL_of_evalL hc h₁)
      · exact .arm hc hb har (reachL_of_evalL harm h₂)
    · simpa using ReachL.ifK hc hb har harm hvs (ih k g args s₁ b s₂ hk)

/-! ## Prefixes of pending calls -/

/-- **A prefix of a pending call before a host call is a pending call.** -/
theorem pendL_prefix {s : Store H} {a : Nat} {vs : List Val} {c : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : PendL s a vs c m) :
    ∀ {pre post : List (Call (wasmHostSig H))} {ev : Call (wasmHostSig H)},
      c = pre ++ ev :: post → PendL s a vs pre ev.1 := by
  induction h with
  | self => intro pre post ev h; simp at h
  | @desc s a vs fi fn l q q' z m hf hcode hr hq _ ih =>
    intro pre post ev h
    rcases split_app h with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
    · obtain ⟨s', f', t, ans, s'', d⟩ := reachL_throw hr
      have hl := logOk_of_eval (x := ⟨a, (vs, s)⟩) hf hcode d
      rw [List.map_append] at hl
      exact logOk_pend openOk (logOk_prefix hl) hq h₁
    · exact .desc hf hcode hr hq (ih h₂)

/-! ## The call prefixes of the open triple -/

/-- **Every call prefix of the exception-free open triple is a pending call.** -/
theorem satP_openTriple_le (s : Store H) (p : Nat × List Val) :
    StratObs.satP openTriple s p ⊆ wasmEvPend s p := by
  rintro ⟨c, e⟩ (h | ⟨d, m', hd, n, c', rfl⟩ | ⟨d, en, hd, n, c', rfl⟩ | ⟨ω, hω, k, rfl, rfl⟩)
  · exact h
  · exact pendL_prefix (ev := ⟨e, n⟩) hd rfl
  · refine closeDLog_pend (x := ⟨p.1, (p.2, s)⟩) (ev := ⟨e, n⟩) openOk ?_ hd rfl
    rintro z _ ⟨fi, fn, l, hf, hc, hL, rfl⟩
    exact logOk_of_reach hf hc (reach_of_logDiv hL)
  · refine closeInfL_pend (x := ⟨p.1, (p.2, s)⟩) openOk ?_ hω k
    rintro z _ ⟨fi, fn, ω, hf, hc, hI, rfl⟩ n
    rw [streamTake_map]
    refine logOk_of_reach hf hc fun l₁ g args s₁ b s₂ l₂ he => ?_
    obtain ⟨h₁, h₂⟩ := streamTake_split he
    rw [h₁]
    exact reach_of_infL hI _ g args s₁ b s₂ h₂.symm

end Silmaril.Proofs.Wasm.Abstract.OpenStrat
