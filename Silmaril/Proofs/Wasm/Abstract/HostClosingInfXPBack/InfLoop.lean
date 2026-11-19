module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.InfCtl

/-!
# Productive runs: loops (proofs)

* `loop_stepI`: one iteration of a loop running productively alone: its body runs productively
  (an `InfOutX J` of the loop), or it branches back with a resolved logged run and the loop runs
  productively again from the new state, by a nonempty host-free run when the iteration makes
  no host call. Every other end of the body is ruled out by `head_contraI`.
* `headInf_loop`, by choice of the iterations: if the loop never ends in its body, it branches
  back forever (`InfLXP.loopInf`); its iterations keep making host calls, since otherwise the run
  would be host-free divergence from some iteration on (`J.coreInf_not_diverges`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)
open Shape (streamAppend)

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H} {J : Silmaril.Wasm.Interp.BackInv H}

theorem xcode_cons_eq (st : List Val) (e : BExpr) (es : List BExpr) :
    xcode st [e] ++ expression (Binaryen.BExpr.lowerList es) = xcode st (e :: es) := by
  simp [xcode, expression]

/-- A host-free run between two head trees alone is one between the trees. -/
theorem link_cons_rtg {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {e : BExpr}
    (es : List BExpr) (h : Relation.ReflTransGen (Det.DStep o) (pcfg s f stk [e]) (pcfg s' f' stk' [e])) :
    Relation.ReflTransGen (Det.DStep o) (pcfg s f stk (e :: es)) (pcfg s' f' stk' (e :: es)) := by
  have := (lifts_suffix (o := o) (expression (Binaryen.BExpr.lowerList es))).rtg h
  simpa only [pcfg, xcode_cons_eq] using this

/-- **One iteration of a loop running productively alone.** -/
theorem loop_stepI (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {body : List BExpr} (es : List BExpr) (ihB : InfG J tags o host body)
    {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → Call (wasmHostSig H)}
    (ht1 : J.TypedP tags s f stk [.loop bt body])
    (hdv : CoreInf (profile o) host (pcfg s f stk [.loop bt body]) ω) :
    InfOutX J tags o host s f stk (.loop bt body :: es) ω ∨
      ∃ (np nr : Nat) (s₁ : Store H) (f₁ : Frame) (vs : List Val) (l₁ : List (OCall H))
        (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)),
        Binaryen.arity f bt = some (np, nr) ∧ Binaryen.arity f₁ bt = some (np, nr) ∧
        EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.brk 0 vs)) ∧
        Shape.SubstPre Cl (l₁.map OCall.lift) cs₁ ∧ ω = cs₁ ++ω ω₂ ∧
        J.TypedP tags s₁ f₁ (vs.take np ++ stk.drop np) [.loop bt body] ∧
        CoreInf (profile o) host (pcfg s₁ f₁ (vs.take np ++ stk.drop np) [.loop bt body]) ω₂ ∧
        (cs₁ = [] → Relation.TransGen (Det.DStep o) (pcfg s f stk [.loop bt body])
          (pcfg s₁ f₁ (vs.take np ++ stk.drop np) [.loop bt body])) := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTM, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨hp, hbe, -⟩ := arity_loop_pre har hc
  obtain ⟨ob₀, hb₀, -⟩ := endsAt_eq hbe
  have hb₀' : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob₀ := by rw [take_length_of_le hp]; exact hb₀
  have hcode : (pcfg s f stk [.loop bt body] : Config H) =
      ⟨s, f, vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: []⟩ := by
    show (⟨s, f, xcode stk [.loop bt body]⟩ : Config H) = _
    rw [xcode, code_loop]; rfl
  have hstep : Step (profile o) Det.noHost (pcfg s f stk [.loop bt body])
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label np [.loop bt (Binaryen.BExpr.lowerList body)] (xcode (stk.take np) body)] ++ []⟩ := by
    rw [hcode]; exact step_enter hp (step_loop har) []
  have ht0 := typedP_ctx' ht1
  have hdK := coreInf_through_dsteps (.single hstep) hdv
  have htB := J.loop_body_typedP har ht1
  rcases coreInf_split_label hdK with hdb | ⟨cs₁, ω₂, cb, N₁, rfl, hb, hsb, hdc, hd₁⟩
  · exact .inl (infOut_lift₀ (fun _ => InfLXP.loop har) (fun _ _ => ReachLXP.loop har)
      (link_cons ⟨_, lifts_label (stk.drop np).reverse np _ [], .single hstep⟩)
      (ihB s f _ ω htB hdb))
  obtain ⟨l, ⟨s₁, f₁, ob⟩, hd, hres, hok⟩ := J.evRunN_back hT hH hE htB hb hsb hdc
  have hw := resW_of_back hres
  cases ob with
  | tail => exact (head_contraI hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
    · exact (head_contraI hH hE ht1 (.loopOk har hd .nil) (resW_nil hw) hdv).elim
    · -- the body branches back to the loop
      have hq : Shape.SubstPre Cl (l.map OCall.lift) cs₁ := by
        rcases hres with h | ⟨h, -⟩
        · exact h
        · cases h
      have hcons₁ := consistent_of_coreInf hdv
      obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hcons₁
      obtain ⟨t₁, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
        hev hts
      obtain ⟨hpo, inv, -⟩ := hA hS hb₀'
      obtain ⟨n', hn', hnv⟩ := hpo
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn'
      subst hn'
      rcases hok with ⟨oc, he, hm'⟩ | ⟨h, -⟩
      swap
      · cases h
      rcases matchP_flow_iff.mp hm' with ⟨hs₁, hf₁, hfm⟩ | ⟨h, -⟩
      swap
      · cases h
      obtain ⟨cst, cfr, ccd⟩ := cb
      dsimp only at hs₁ hf₁ he hb hd₁
      subst hs₁ hf₁
      have hex := exit_br0 (P := profile o) (host := NH) (s₁ := cst) (f₁ := cfr)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hfm hnv ((stk.drop np).reverse) []
      have hcont : vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
          expression [.loop bt (Binaryen.BExpr.lowerList body)] ++ [] =
          xcode (vs.take np ++ stk.drop np) [.loop bt body] := by
        rw [xcode, code_loop]; simp [expression]
      rw [hcont] at hex
      have h3 : Steps (profile o) host (pcfg s f stk [.loop bt body])
          (pcfg cst cfr (vs.take np ++ stk.drop np) [.loop bt body]) :=
        ((Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
          (Steps.ctx _ _ (Steps.label np _ (evRunN_steps hb)))).trans (steps_host hex)
      have htL := J.steps_host hT ht0
        ((Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
          (Steps.ctx _ _ (Steps.label np _ (evRunN_steps hb))))
      have hd₂ := coreInf_through_dsteps hex hd₁
      have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have htk : J.TypedP tags cst cfr (vs.take np ++ stk.drop np) [.loop bt body] :=
        ⟨rest, labels, ret, out, storeChk_inv inv hS, by rw [hlen]; exact chk_inv inv hc,
          J.steps_host hT hct (Steps.append rest h3), by rw [inv.2.1]; exact hTM, t₁⟩
      refine .inr ⟨np, nr, cst, cfr, vs, l, cs₁, ω₂, har, ?_, hd, hq, rfl, htk, hd₂, fun h0 => ?_⟩
      · rw [arity_eq, inv.2.1]; exact ha
      · subst h0
        exact tg_trans_rtg (.single hstep)
          (((lifts_label (o := o) (stk.drop np).reverse np
            [.loop bt (Binaryen.BExpr.lowerList body)] []).rtg (evRunN_nil_dsteps hb)).trans hex)
    · exact (head_contraI hH hE ht1 (.loopBrk har hd) hw hdv).elim
    · exact (head_contraI hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim
    · exact (head_contraI hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim
    · exact (head_contraI hH hE ht1 (.loopEsc har hd trivial) hw hdv).elim

theorem substPre_nil_eq {q : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre Cl (([] : List (OCall H)).map OCall.lift) q) : q = [] := by
  cases h
  rfl

/-- **A loop running productively alone**, by choice of the iterations. -/
theorem headInf_loop (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {body es : List BExpr} (ihB : InfG J tags o host body)
    {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → Call (wasmHostSig H)}
    (ht : J.TypedP tags s f stk (.loop bt body :: es))
    (hdv : CoreInf (profile o) host (pcfg s f stk [.loop bt body]) ω) :
    InfOutX J tags o host s f stk (.loop bt body :: es) ω := by
  classical
  by_contra hno
  let Good : Store H × Frame × List Val × (Nat → Call (wasmHostSig H)) → Prop := fun p =>
    J.TypedP tags p.1 p.2.1 p.2.2.1 [.loop bt body] ∧
    CoreInf (profile o) host (pcfg p.1 p.2.1 p.2.2.1 [.loop bt body]) p.2.2.2 ∧
    (InfOutX J tags o host p.1 p.2.1 p.2.2.1 (.loop bt body :: es) p.2.2.2 →
      InfOutX J tags o host s f stk (.loop bt body :: es) ω)
  have step : ∀ p : {p // Good p}, ∃ (p' : {p // Good p}) (np nr : Nat) (vs : List Val)
      (l₁ : List (OCall H)) (cs₁ : List (Call (wasmHostSig H))),
      Binaryen.arity p.1.2.1 bt = some (np, nr) ∧ Binaryen.arity p'.1.2.1 bt = some (np, nr) ∧
      EvalLXPh p.1.1 p.1.2.1 (p.1.2.2.1.take np) body l₁ (p'.1.1, p'.1.2.1, .flow (.brk 0 vs)) ∧
      p'.1.2.2.1 = vs.take np ++ p.1.2.2.1.drop np ∧
      Shape.SubstPre Cl (l₁.map OCall.lift) cs₁ ∧ p.1.2.2.2 = cs₁ ++ω p'.1.2.2.2 ∧
      (cs₁ = [] → Relation.TransGen (Det.DStep o)
        (pcfg p.1.1 p.1.2.1 p.1.2.2.1 [.loop bt body])
        (pcfg p'.1.1 p'.1.2.1 p'.1.2.2.1 [.loop bt body])) := by
    rintro ⟨⟨s', f', stk', ω'⟩, ht', hd', hback⟩
    rcases loop_stepI hT hH hE es ihB ht' hd' with hout |
        ⟨np, nr, s₁, f₁, vs, l₁, cs₁, ω₂, har, har₁, hbody, hl₁, hω, ht₁, hd₁, hlink⟩
    · exact (hno (hback hout)).elim
    · refine ⟨⟨⟨s₁, f₁, vs.take np ++ stk'.drop np, ω₂⟩, ht₁, hd₁, fun h => hback ?_⟩,
        np, nr, vs, l₁, cs₁, har, har₁, hbody, rfl, hl₁, hω, hlink⟩
      rw [hω]
      exact infOut_lift (fun _ h => InfLXP.loopBack har hbody h)
        (fun _ _ h => ReachLXP.loopBack har hbody h) hl₁
        (fun h0 => ⟨_, lifts_id, link_cons_rtg es (hlink h0).to_reflTransGen⟩) h
  choose nx np nr vs l₁ cs₁ har har' hbody hstk hres hω hlink using step
  let G : Nat → {p // Good p} := fun n => nx^[n] ⟨(s, f, stk, ω), typedP_head ht, hdv, id⟩
  have hG : ∀ n, G (n + 1) = nx (G n) := fun n => Function.iterate_succ_apply' nx n _
  have hA : ∀ n, Binaryen.arity (G n).1.2.1 bt = some (np (G 0), nr (G 0)) := by
    intro n
    induction n with
    | zero => exact har (G 0)
    | succ n ihn =>
      rw [hG, ← (har (G n)).symm.trans ihn]
      exact har' (G n)
  have hNP : ∀ n, np (G n) = np (G 0) := fun n => by
    have := (har (G n)).symm.trans (hA n)
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  have hfreq : ∀ N, ∃ n, N ≤ n ∧ cs₁ (G n) ≠ [] := by
    intro N
    by_contra hall
    push Not at hall
    have hchain : ∀ k, Relation.TransGen (Det.DStep o)
        (pcfg (G (N + k)).1.1 (G (N + k)).1.2.1 (G (N + k)).1.2.2.1 [.loop bt body])
        (pcfg (G (N + k + 1)).1.1 (G (N + k + 1)).1.2.1 (G (N + k + 1)).1.2.2.1
          [.loop bt body]) := by
      intro k
      rw [hG]
      exact hlink _ (hall _ (Nat.le_add_right _ _))
    have hdiv := trace_of_tgChain (x := fun k =>
      pcfg (G (N + k)).1.1 (G (N + k)).1.2.1 (G (N + k)).1.2.2.1 [.loop bt body]) hchain
    exact J.coreInf_not_diverges (typedP_ctx' (G N).2.1) hdiv (G N).2.2.1
  have hL : ∀ n, l₁ (G n) = [] → cs₁ (G n) = [] := by
    intro n h
    have := hres (G n)
    rw [h] at this
    exact substPre_nil_eq this
  have hfreqL : ∀ N, ∃ n, N ≤ n ∧ l₁ (G n) ≠ [] := fun N => by
    obtain ⟨n, hn, hne⟩ := hfreq N
    exact ⟨n, hn, fun h => hne (hL n h)⟩
  obtain ⟨ν, hν⟩ := Shape.exists_streamConcat (fun n => l₁ (G n))
    (Shape.unbounded_of_frequently _ hfreqL)
  have hchainω : ∀ n, (G n).1.2.2.2 = cs₁ (G n) ++ω (G (n + 1)).1.2.2.2 := fun n => by
    rw [hG]; exact hω (G n)
  have hcsω := Shape.streamConcat_of_chain (w := fun n => (G n).1.2.2.2) hchainω
    (Shape.unbounded_of_frequently _ hfreq)
  have hsub : Shape.SubstInf Cl (fun i => (ν i).lift) ω :=
    Shape.substInf_of_segments (u := fun n => (l₁ (G n)).map OCall.lift)
      (q := fun n => cs₁ (G n)) (fun n => hres (G n)) (Shape.streamConcat_map OCall.lift hν) hcsω
  have hloop : InfLXP s f stk (.loop bt body :: es) ν := by
    refine InfLXP.loopInf (np := np (G 0)) (nr := nr (G 0))
      (fun n => ((G n).1.1, (G n).1.2.1, (G n).1.2.2.1)) (fun n => l₁ (G n)) rfl
      (fun n => hA n) (fun n => ⟨vs (G n), ?_, ?_⟩) hν
    · have := hbody (G n)
      rw [← hG, hNP] at this
      exact this
    · have := hstk (G n)
      rw [← hG, hNP] at this
      exact this
  exact hno (.inl ⟨ν, hloop, hsub⟩)

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
