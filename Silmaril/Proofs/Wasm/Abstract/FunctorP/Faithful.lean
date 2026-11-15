module

public import Silmaril.Proofs.Wasm.Abstract.FunctorP.Reach
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Faithful

/-!
Proofs for `Silmaril.Wasm.Abstract.FunctorP.Thms`: exactness of the logged observations
(`evalLXP_iff`, `evalLXP_trap_iff`, `reachXP_iff`), and faithfulness of the denotation for them:
`opEquivP_iff` (trap payloads, i.e. `erasedRun`) and `opCollapseEquivP_iff` (trap ≈ divergence).

The tree lemma behind both: two trees with the same finished paths *to values* and the same
pending calls are equal (`tree_eq_of_val_pend`): a silent divergence at a reachable node is what
remains when there is neither a value nor a pending call, so it need not be observed.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FunctorP

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.FunctorP
  Silmaril.Wasm.Abstract.ExposePStruct
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall
  Silmaril.Proofs.Wasm.Abstract.CallX Silmaril.Proofs.Wasm.Abstract.ExposeE
  Silmaril.Proofs.Wasm.Abstract.ExposeP

/-! ## Values and pending calls determine a tree -/

section
universe u
variable {E : Sig.{u}} {Y : Type (u + 1)}

theorem observe_eq_of_val_pend :
    ∀ (n : Nat) (t t' : Tree (SigEv E) Y),
      (∀ cs v, Path t cs (.val v) ↔ Path t' cs (.val v)) →
      (∀ cs m, Pend t cs m ↔ Pend t' cs m) → t.observe n = t'.observe n
  | 0, _, _, _, _ => rfl
  | n + 1, t, t', hv, hq => by
    rw [observe_succ_eq_out, observe_succ_eq_out]
    rcases cases_visible t with rfl | ⟨v, rfl⟩ | ⟨R, ⟨m, hm⟩, k, rfl⟩
    · rcases cases_visible t' with rfl | ⟨v, rfl⟩ | ⟨R', ⟨m', hm'⟩, k', rfl⟩
      · rfl
      · have := (path_diverge_inv ((hv [] v).2 (.ret rfl))).2
        cases this
      · subst hm'
        exact absurd ((hq [] m').2 (.here rfl)) not_pend_diverge
    · rw [path_nil_val ((hv [] v).1 (.ret rfl))]
    · subst hm
      have hp := (hq [] m).1 (.here rfl)
      rcases cases_visible t' with rfl | ⟨v, rfl⟩ | ⟨R', ⟨m', hm'⟩, k', rfl⟩
      · exact absurd hp not_pend_diverge
      · exact absurd hp not_pend_ret
      · subst hm'
        rcases pend_vis_inv hp with ⟨-, hmm⟩ | ⟨_, _, hc, -⟩
        · change m = m' at hmm
          subst hmm
          have hk : ∀ r, (k r).observe n = (k' r).observe n := fun r =>
            observe_eq_of_val_pend n (k r) (k' r)
              (fun cs x => by
                rw [← path_vis_cons (e := ⟨m, rfl⟩) (k := k) (r := r),
                  ← path_vis_cons (e := ⟨m, rfl⟩) (k := k') (r := r)]
                exact hv _ _)
              (fun cs x => by
                rw [← pend_vis_cons (e := ⟨m, rfl⟩) (k := k) (r := r),
                  ← pend_vis_cons (e := ⟨m, rfl⟩) (k := k') (r := r)]
                exact hq _ _)
          rw [out_vis (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩ k,
            out_vis (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩ k']
          change Part.map _ (Part.some _) = Part.map _ (Part.some _)
          rw [Part.map_some, Part.map_some]
          change Part.some (Visible.vis _ fun r => (k r).observe n) =
            Part.some (Visible.vis _ fun r => (k' r).observe n)
          rw [funext hk]
        · cases hc

theorem tree_eq_of_val_pend {t t' : Tree (SigEv E) Y}
    (hv : ∀ cs v, Path t cs (.val v) ↔ Path t' cs (.val v))
    (hq : ∀ cs m, Pend t cs m ↔ Pend t' cs m) : t = t' :=
  Tree.ext fun n => observe_eq_of_val_pend n t t' hv hq

end

variable {H : Type}

/-! ## Exactness of the logged observations -/

section
variable {C : CallRel H}

theorem evalLXP_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (Call (CallSig H))} {s' : Store H} {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    EvalLXP C s f stk es cs (s', f', o) ↔
      Answered C cs ∧ Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs
        (.val (.ok (⟨(f', o)⟩, ⟨s'⟩))) := by
  constructor
  · intro h
    obtain ⟨hA, hp⟩ := evalLXP_path h
    exact ⟨hA, endRP_ok ho ▸ hp⟩
  · rintro ⟨hA, hp⟩
    obtain ⟨⟨s₁, f₁, o₁⟩, hev, he⟩ := list_ansL es s f stk cs _ hA hp (by simp)
    obtain ⟨-, h1, h2⟩ := endRP_ok_inv he
    simp only [ULift.up.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    subst h2
    exact hev

theorem evalLXP_trap_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (Call (CallSig H))} :
    (∃ s' f', EvalLXP C s f stk es cs (s', f', .flow .trap)) ↔
      Answered C cs ∧ Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs
        (.val (.error ⟨⟩)) := by
  constructor
  · rintro ⟨s', f', h⟩
    exact evalLXP_path h
  · rintro ⟨hA, hp⟩
    obtain ⟨⟨s₁, f₁, o₁⟩, hev, he⟩ := list_ansL es s f stk cs _ hA hp (by simp)
    obtain rfl := endRP_err_inv he
    exact ⟨s₁, f₁, hev⟩

theorem reachXP_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (Call (CallSig H))} {y : Nat × List Val × Store H} :
    ReachXP C s f stk es cs y ↔
      Answered C cs ∧ Pend (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs y :=
  ⟨reachXP_pend, fun ⟨hA, hp⟩ => list_reachL es s f stk cs y hA hp⟩

theorem frameLXP_iff {s : Store H} {a : Nat} {args : List Val} {cs : List (Call (CallSig H))}
    {s' : Store H} {fl : Flow} (hfl : fl ≠ .trap) :
    FrameLXP C s a args cs (s', fl) ↔
      Answered C cs ∧ Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs
        (.val (.ok (⟨fl⟩, ⟨s'⟩))) := by
  constructor
  · intro h
    obtain ⟨hA, hp⟩ := frameLXP_path h
    exact ⟨hA, endF_ok hfl ▸ hp⟩
  · rintro ⟨hA, hp⟩
    obtain ⟨⟨s₁, fl₁⟩, hb, he⟩ := path_frameLXP hA hp (by simp)
    obtain ⟨-, h1, h2⟩ := endF_ok_inv he
    cases h1
    cases h2
    exact hb

theorem frameLXP_trap_iff {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} :
    (∃ s', FrameLXP C s a args cs (s', .trap)) ↔
      Answered C cs ∧ Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs
        (.val (.error ⟨⟩)) := by
  constructor
  · rintro ⟨s', h⟩
    exact frameLXP_path h
  · rintro ⟨hA, hp⟩
    obtain ⟨⟨s₁, fl₁⟩, hb, he⟩ := path_frameLXP hA hp (by simp)
    obtain rfl := endF_err_inv he
    exact ⟨s₁, hb⟩

theorem frameReachXP_iff {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} {y : Nat × List Val × Store H} :
    FrameReachXP C s a args cs y ↔
      Answered C cs ∧ Pend (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs y :=
  ⟨frameReachXP_pend, fun ⟨hA, hp⟩ => pend_frameReachXP hA hp⟩

/-- An `EvalOXP` outcome is a logged run with some log. -/
theorem evalOXP_iff_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    EvalOXP C s f stk es (s', f', o) ↔ ∃ cs, EvalLXP C s f stk es cs (s', f', o) := by
  rw [Silmaril.Proofs.Wasm.Abstract.ExposeP.evalOXP_iff ho]
  simp only [evalLXP_iff ho]

theorem evalOXP_trap_iff_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    (∃ s' f', EvalOXP C s f stk es (s', f', .flow .trap)) ↔
      ∃ cs s' f', EvalLXP C s f stk es cs (s', f', .flow .trap) := by
  rw [Silmaril.Proofs.Wasm.Abstract.ExposeP.evalOXP_trap_iff]
  constructor
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨s', f', h⟩ := evalLXP_trap_iff.2 ⟨hA, hp⟩
    exact ⟨cs, s', f', h⟩
  · rintro ⟨cs, s', f', h⟩
    exact ⟨cs, evalLXP_trap_iff.1 ⟨s', f', h⟩⟩

end

/-! ## Faithfulness -/

/-- The universal oracle. -/
def topRel : CallRel H := fun _ _ _ _ => True

theorem answered_top (cs : List (Call (CallSig H))) : Answered topRel cs := fun _ _ => trivial

theorem erasedRun_denL (es : List BExpr) (s : St H) (c : Cfg) :
    erasedRun (denL (H := H) es) s c =
      run' (denListXP es c.down.1 c.down.2 : M (CallSig H) H ResP) s := by
  unfold erasedRun
  have : (fun r : Except PUnit.{2} (ResP × St H) => (pure (eraseTrap r) :
      Tree (SigEv (CallSig H)) _)) = pure := by
    funext r; rcases r with ⟨⟨⟩⟩ | _ <;> rfl
  rw [this, bind_pure]
  rfl

/-- The finished paths of the exposed body, read by the logged runs at the universal oracle. -/
theorem path_val_iff (es : List BExpr) (s : Store H) (f : Frame) (stk : List Val)
    (cs : List (Call (CallSig H))) (v : Except PUnit.{2} (ResP × St H)) :
    Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs (.val v) ↔
      ∃ r, EvalLXP topRel s f stk es cs r ∧ endRP r = .val v := by
  constructor
  · intro h; exact list_ansL es s f stk cs _ (answered_top cs) h (by simp)
  · rintro ⟨r, h, hr⟩; rw [← hr]; exact (evalLXP_path h).2

theorem pend_iff_reach_top (es : List BExpr) (s : Store H) (f : Frame) (stk : List Val)
    (cs : List (Call (CallSig H))) (m : Nat × List Val × Store H) :
    Pend (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs m ↔
      ReachXP topRel s f stk es cs m :=
  (reachXP_iff.trans (and_iff_right (answered_top cs))).symm

/-- Equal trees from the exact operational equivalence. -/
theorem run_eq_of_opEquivP {es es' : List BExpr} (h : OpEquivP H es es') (s : Store H) (f : Frame)
    (stk : List Val) :
    run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩ =
      run' (denListXP es' f stk : M (CallSig H) H ResP) ⟨s⟩ := by
  have key : ∀ es es', OpEquivP H es es' → ∀ cs v,
      Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs (.val v) →
      Path (run' (denListXP es' f stk : M (CallSig H) H ResP) ⟨s⟩) cs (.val v) := by
    intro es es' h cs v hp
    obtain ⟨⟨s', f', o⟩, hev, hr⟩ := (path_val_iff es s f stk cs v).1 hp
    obtain ⟨h₁, h₂, -⟩ := h topRel s f stk cs
    refine (path_val_iff es' s f stk cs v).2 ?_
    by_cases ho : o = .flow .trap
    · subst ho
      obtain ⟨s'', f'', hev'⟩ := h₂.1 ⟨s', f', hev⟩
      exact ⟨_, hev', hr⟩
    · exact ⟨_, (h₁ s' f' o ho).1 hev, hr⟩
  have hsymm : OpEquivP H es' es := fun C s f stk cs => by
    obtain ⟨h₁, h₂, h₃⟩ := h C s f stk cs
    exact ⟨fun s' f' o ho => (h₁ s' f' o ho).symm, h₂.symm, fun y => (h₃ y).symm⟩
  refine tree_eq_of_val_pend (fun cs v => ⟨key es es' h cs v, key es' es hsymm cs v⟩)
    (fun cs m => ?_)
  exact (pend_iff_reach_top es s f stk cs m).trans
    (((h topRel s f stk cs).2.2 m).trans (pend_iff_reach_top es' s f stk cs m).symm)

theorem opEquivP_of_run_eq {es es' : List BExpr}
    (h : ∀ s f stk, run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩ =
      run' (denListXP es' f stk : M (CallSig H) H ResP) ⟨s⟩) : OpEquivP H es es' := by
  intro C s f stk cs
  refine ⟨fun s' f' o ho => ?_, ?_, fun y => ?_⟩
  · rw [evalLXP_iff ho, evalLXP_iff ho, h]
  · rw [evalLXP_trap_iff, evalLXP_trap_iff, h]
  · rw [reachXP_iff, reachXP_iff, h]

/-- **Exact faithfulness.** -/
theorem opEquivP_iff (es es' : List BExpr) :
    erasedRun (denL (H := H) es) = erasedRun (denL es') ↔ OpEquivP H es es' := by
  constructor
  · intro h
    refine opEquivP_of_run_eq fun s f stk => ?_
    have := congrFun (congrFun h ⟨s⟩) ⟨(f, stk)⟩
    rwa [erasedRun_denL, erasedRun_denL] at this
  · intro h
    funext s c
    rw [erasedRun_denL, erasedRun_denL]
    exact run_eq_of_opEquivP h s.down c.down.1 c.down.2

/-! ## Up to trap ≈ divergence -/

theorem path_collapse_val {t : Tree (SigEv (CallSig H)) (Except PUnit.{2} (ResP × St H))}
    {cs : List (Call (CallSig H))} {p : ResP × St H} :
    Path (t >>= trapDiverge) cs (.val p) ↔ Path t cs (.val (.ok p)) := by
  constructor
  · intro h
    rcases path_bind_inv h with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨h, -⟩
    · rcases v with e | p'
      · exact absurd (path_diverge_inv h₂).2 (by simp)
      · obtain ⟨rfl, hv⟩ := path_ret_inv rfl h₂
        cases hv
        simpa using h₁
    · cases h
  · intro h
    have := path_bind_ret (k := trapDiverge) (cs₂ := []) h (.ret rfl)
    simpa using this

theorem pend_collapse {t : Tree (SigEv (CallSig H)) (Except PUnit.{2} (ResP × St H))}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} :
    Pend (t >>= trapDiverge) cs m ↔ Pend t cs m := by
  refine Silmaril.Proofs.Wasm.Abstract.BodyTrace.pend_bind_iff ?_
  rintro (e | p) cs m
  · exact not_pend_diverge
  · exact not_pend_ret

theorem collapse_denL (es : List BExpr) (c : Cfg) (s : St H) :
    collapse (denL (H := H) es c) s =
      run' (denListXP es c.down.1 c.down.2 : M (CallSig H) H ResP) s >>= trapDiverge :=
  collapse_eq_bind _ s

/-- Non-trap finished paths, read by the logged runs at the universal oracle. -/
theorem path_ok_iff (es : List BExpr) (s : Store H) (f : Frame) (stk : List Val)
    (cs : List (Call (CallSig H))) (p : ResP × St H) :
    Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs (.val (.ok p)) ↔
      p.1.down.2 ≠ .flow .trap ∧ EvalLXP topRel s f stk es cs (p.2.down, p.1.down.1, p.1.down.2) := by
  obtain ⟨⟨f', o⟩, ⟨s'⟩⟩ := p
  constructor
  · intro h
    obtain ⟨r, hev, hr⟩ := (path_val_iff es s f stk cs _).1 h
    obtain ⟨s₁, f₁, o₁⟩ := r
    obtain ⟨hnt, h1, h2⟩ := endRP_ok_inv hr
    simp only [ULift.up.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    subst h2
    exact ⟨hnt, hev⟩
  · rintro ⟨hnt, hev⟩
    exact ((evalLXP_iff hnt).1 hev).2

theorem opCollapseEquivP_iff (es es' : List BExpr) :
    FullCollapseEquiv (denL (H := H) es) (denL es') ↔ OpCollapseEquivP H es es' := by
  rw [Silmaril.Wasm.Abstract.BodyTrace.fullCollapseEquiv_iff]
  constructor
  · intro h C s f stk cs
    have hT : run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩ >>= trapDiverge =
        run' (denListXP es' f stk : M (CallSig H) H ResP) ⟨s⟩ >>= trapDiverge := by
      have := congrFun (h ⟨(f, stk)⟩) ⟨s⟩
      rwa [collapse_denL, collapse_denL] at this
    refine ⟨fun s' f' o ho => ?_, fun y => ?_⟩
    · rw [evalLXP_iff ho, evalLXP_iff ho, ← path_collapse_val, ← path_collapse_val, hT]
    · have hP : ∀ m : (CallSig H).Op,
          Pend (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs m ↔
            Pend (run' (denListXP es' f stk : M (CallSig H) H ResP) ⟨s⟩) cs m := fun m => by
        rw [← pend_collapse, ← pend_collapse, hT]
      rw [reachXP_iff, reachXP_iff]
      exact and_congr_right fun _ => hP y
  · intro h c
    funext s
    rw [collapse_denL, collapse_denL]
    refine tree_eq_of_val_pend (fun cs p => ?_) (fun cs m => ?_)
    · rw [path_collapse_val, path_collapse_val, path_ok_iff, path_ok_iff]
      exact and_congr_right fun ho => (h topRel s.down c.down.1 c.down.2 cs).1 _ _ _ ho
    · rw [pend_collapse, pend_collapse]
      exact (pend_iff_reach_top es _ _ _ cs m).trans
        (((h topRel s.down c.down.1 c.down.2 cs).2 m).trans
          (pend_iff_reach_top es' _ _ _ cs m).symm)

/-! ## Frames of equivalent bodies -/

theorem frameXP_run_eq {s : Store H} {a b : Nat} {args : List Val} {fi fi' : FuncInst H}
    {fn fn' : Func} {ps rs ps' rs' : List Validation.CValType}
    (hfa : s.funcs[a]? = some fi) (hca : fi.code = .wasm fn)
    (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (hcb : fi'.code = .wasm fn')
    (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (hmod : fi.module = fi'.module) (hloc : fn.locals = fn'.locals)
    (hbody : OpEquivP H (liftInstrs fn.body) (liftInstrs fn'.body)) :
    run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩ =
      run' (frameXP b args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩ := by
  rw [run_frameXP hfa hca htya, run_frameXP hfb hcb htyb, StoreBody.run_bind, StoreBody.run_bind,
    hmod, hloc, run_eq_of_opEquivP hbody]

end Silmaril.Proofs.Wasm.Abstract.FunctorP
