module

public import Silmaril.Proofs.Wasm.Abstract.StoreBody.Basic
public import Silmaril.Wasm.Abstract.BodyTrace.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.StoreBody.Thms`: every abstract body of a
call-free tree list diverges or computes an outcome of the interpreter's
fuel-free big-step relation `Binaryen.Eval` (`list_good`). Loops use the
iteration of trees without events (`BodyTrace.iter_pure`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreBody

open Silmaril.Wasm Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody
  Silmaril.Elgot.ITree

variable {E : Sig.{0}} {H : Type}

/-- A body that diverges or computes an interpreter outcome satisfying `P`. -/
def Good (x : M E H Res) (s : St H) (P : Store H × Frame × Flow → Prop) : Prop :=
  run' x s = diverge ∨ ∃ r, P r ∧ run' x s = evalTree (some r)

theorem run_bind_diverge {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    (h : run' x s = diverge) : run' (x >>= k) s = diverge := by
  rw [run_bind, h, diverge_bind]

theorem pass_thenK {k : Frame → List Val → M E H Res} {y : M E H Res} {s : St H}
    {s' : Store H} {f' : Frame} {fl : Flow} (hy : run' y s = evalTree (some (s', f', fl)))
    (hfl : ¬ fl.IsNormal) : run' (y >>= thenK k) s = evalTree (some (s', f', fl)) := by
  rw [run_bind_eval hy]
  cases fl
  case normal => exact absurd trivial hfl
  all_goals rfl

theorem good_cont {es : List BExpr} {y : M E H Res} {s : St H} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {P : Store H × Frame × Flow → Prop}
    (hy : run' y s = evalTree (some (s₁, f₁, .normal stk₁)))
    (hk : Good (E := E) (denList es f₁ stk₁) ⟨s₁⟩ P) : Good (y >>= thenK (denList es)) s P := by
  unfold Good at hk ⊢
  rw [run_bind_eval hy]
  exact hk

theorem Good.mono {x : M E H Res} {s : St H} {P Q : Store H × Frame × Flow → Prop}
    (h : Good x s P) (hpq : ∀ r, P r → Q r) : Good x s Q := by
  rcases h with h | ⟨r, hr, h⟩
  · exact .inl h
  · exact .inr ⟨r, hpq r hr, h⟩

theorem good_div {x : M E H Res} {s : St H} {P : Store H × Frame × Flow → Prop}
    (h : run' x s = diverge) : Good x s P := .inl h

theorem good_pass {es : List BExpr} {y : M E H Res} {s : St H} {s' : Store H} {f' : Frame}
    {fl : Flow} {P : Store H × Frame × Flow → Prop}
    (hy : run' y s = evalTree (some (s', f', fl))) (hfl : ¬ fl.IsNormal) (hP : P (s', f', fl)) :
    Good (y >>= thenK (denList es)) s P :=
  .inr ⟨_, hP, pass_thenK hy hfl⟩

/-! ## Blocks -/

/-- The outcome of a block body after its exits. -/
theorem blockK_eval {np nr : Nat} {stk : List Val} {y : M E H Res} {s : St H}
    {s₁ : Store H} {f₁ : Frame} {fl : Flow} (hy : run' y s = evalTree (some (s₁, f₁, fl))) :
    (∃ vs, fl.blockVals = some vs ∧
        run' (y >>= blockK np nr stk) s =
          evalTree (some (s₁, f₁, .normal (vs.take nr ++ stk.drop np)))) ∨
      (∃ k vs, fl = .brk (k + 1) vs ∧
        run' (y >>= blockK np nr stk) s = evalTree (some (s₁, f₁, .brk k vs))) ∨
      (fl.Escapes ∧ run' (y >>= blockK np nr stk) s = evalTree (some (s₁, f₁, fl))) := by
  rw [run_bind_eval hy]
  cases fl with
  | normal vs => exact .inl ⟨vs, rfl, rfl⟩
  | brk k vs =>
    cases k with
    | zero => exact .inl ⟨vs, rfl, rfl⟩
    | succ k => exact .inr (.inl ⟨k, vs, rfl, rfl⟩)
  | ret vs => exact .inr (.inr ⟨trivial, rfl⟩)
  | trap => exact .inr (.inr ⟨trivial, rfl⟩)
  | throw a => exact .inr (.inr ⟨trivial, rfl⟩)

/-! ## Loops -/

/-- One iteration of a loop, at the tree level. -/
noncomputable abbrev loopG (bt : BlockType) (body : List BExpr) :=
  loopTree (E := E) (loopBody (E := E) (H := H) bt body)

theorem loopG_ret {bt : BlockType} {body : List BExpr} {p : ULift.{1} (Frame × List Val) × St H}
    {v : Except PUnit.{2} ((Res ⊕ ULift.{1} (Frame × List Val)) × St H)}
    (h : run' (loopBody bt body p.1 : M E H _) p.2 = ret v) :
    loopG (E := E) bt body p = ret (loopEnd v) := by
  show run' _ p.2 >>= _ = _
  rw [h]; exact pure_bind _ _

/-- One iteration: diverges, or runs the body to an interpreter outcome `r₁` and
then continues (`br 0`) or leaves. -/
theorem loopG_spec (bt : BlockType) (body : List BExpr)
    (ih : ∀ s f stk, Good (denList body f stk : M E H Res) ⟨s⟩ (Eval s f stk body))
    (p : ULift.{1} (Frame × List Val) × St H) :
    loopG (E := E) bt body p = diverge ∨
      ∃ np nr s₁ f₁ fl, arity p.1.down.1 bt = some (np, nr) ∧
        Eval p.2.down p.1.down.1 (p.1.down.2.take np) body (s₁, f₁, fl) ∧
        ((∃ vs, fl = .brk 0 vs ∧
            loopG (E := E) bt body p = ret (.inr (⟨(f₁, vs.take np ++ p.1.down.2.drop np)⟩, ⟨s₁⟩))) ∨
          (∃ vs, fl = .normal vs ∧
            loopG (E := E) bt body p =
              ret (.inl (.ok (⟨(f₁, .normal (vs.take nr ++ p.1.down.2.drop np))⟩, ⟨s₁⟩)))) ∨
          (∃ k vs, fl = .brk (k + 1) vs ∧
            loopG (E := E) bt body p = ret (.inl (.ok (⟨(f₁, .brk k vs)⟩, ⟨s₁⟩)))) ∨
          (fl.Escapes ∧ ∃ v, evalTree (E := E) (some (s₁, f₁, fl)) = ret v ∧
            loopG (E := E) bt body p = ret (.inl v))) := by
  obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
  cases ha : arity f bt with
  | none =>
    left
    show run' _ _ >>= _ = _
    have : run' (loopBody bt body ⟨(f, stk)⟩ : M E H _) ⟨s⟩ = diverge := by
      simp only [loopBody, ha]; rfl
    rw [this, diverge_bind]
  | some p =>
    obtain ⟨np, nr⟩ := p
    have hL : (loopBody bt body ⟨(f, stk)⟩ : M E H _) =
        denList body f (stk.take np) >>= loopK np nr stk := by
      simp only [loopBody, ha]
    rcases ih s f (stk.take np) with hd | ⟨⟨s₁, f₁, fl⟩, hev, hy⟩
    · left
      show run' _ _ >>= _ = _
      rw [hL, run_bind_diverge hd, diverge_bind]
    · right
      refine ⟨np, nr, s₁, f₁, fl, rfl, hev, ?_⟩
      have hb := run_bind_eval (k := loopK np nr stk) hy
      rw [← hL] at hb
      cases fl with
      | normal vs =>
        exact .inr (.inl ⟨vs, rfl, loopG_ret
          (v := .ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, ⟨s₁⟩)) (hb.trans rfl)⟩)
      | brk k vs =>
        cases k with
        | zero =>
          exact .inl ⟨vs, rfl, loopG_ret
            (v := .ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩)) (hb.trans rfl)⟩
        | succ k =>
          exact .inr (.inr (.inl ⟨k, vs, rfl, loopG_ret
            (v := .ok (.inl ⟨(f₁, .brk k vs)⟩, ⟨s₁⟩)) (hb.trans rfl)⟩))
      | ret vs =>
        exact .inr (.inr (.inr ⟨trivial, .ok (⟨(f₁, .ret vs)⟩, ⟨s₁⟩), rfl, loopG_ret
          (v := .ok (.inl ⟨(f₁, .ret vs)⟩, ⟨s₁⟩)) (hb.trans rfl)⟩))
      | throw a =>
        exact .inr (.inr (.inr ⟨trivial, .ok (⟨(f₁, .throw a)⟩, ⟨s₁⟩), rfl, loopG_ret
          (v := .ok (.inl ⟨(f₁, .throw a)⟩, ⟨s₁⟩)) (hb.trans rfl)⟩))
      | trap =>
        exact .inr (.inr (.inr ⟨trivial, .error ⟨⟩, rfl, loopG_ret
          (v := .error ⟨⟩) (hb.trans rfl)⟩))

/-- The continuation after a loop exit. -/
noncomputable def loopCont (es : List BExpr)
    (y : Except PUnit.{2} (Res × St H)) : Tree (SigEv E) (Except PUnit.{2} (Res × St H)) :=
  match y with
  | .ok (a, s') => run' (thenK (denList es) a : M E H Res) s'
  | .error e => ret (.error e)

theorem loop_good (bt : BlockType) (body es : List BExpr)
    (ih : ∀ s f stk, Good (denList body f stk : M E H Res) ⟨s⟩ (Eval s f stk body))
    (hes : ∀ s f stk, Good (denList es f stk : M E H Res) ⟨s⟩ (Eval s f stk es))
    (s : Store H) (f : Frame) (stk : List Val) :
    Good (den (.loop bt body) f stk >>= thenK (denList es) : M E H Res) ⟨s⟩
      (Eval s f stk (.loop bt body :: es)) := by
  have hrun : ∀ (f : Frame) (stk : List Val) (s : Store H),
      run' (den (.loop bt body) f stk >>= thenK (denList es) : M E H Res) ⟨s⟩ =
        (Silmaril.Elgot.iter (loopG (E := E) bt body) (⟨(f, stk)⟩, ⟨s⟩) :
          Tree (SigEv E) _) >>= loopCont (E := E) es := by
    intro f stk s
    rw [run_bind]
    have : run' (den (.loop bt body) f stk : M E H Res) ⟨s⟩ =
        (Silmaril.Elgot.iter (loopG (E := E) bt body) (⟨(f, stk)⟩, ⟨s⟩) : Tree (SigEv E) _) :=
      run_iter (loopBody bt body) _ _
    rw [this]
    congr 1
    funext y
    rcases y with e | ⟨a, s'⟩ <;> rfl
  have hpure : ∀ p, loopG (E := E) bt body p = diverge ∨
      ∃ v, loopG (E := E) bt body p = ret v := fun p => by
    rcases loopG_spec bt body ih p with h | ⟨_, _, _, _, _, _, _, h⟩
    · exact .inl h
    · rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
      all_goals exact .inr ⟨_, h⟩
  have key : ∀ (p : ULift.{1} (Frame × List Val) × St H) (y : Except PUnit.{2} (Res × St H)),
      PureReach (loopG (E := E) bt body) p y →
      loopCont (E := E) es y = diverge ∨ ∃ r, Eval p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) r ∧
        loopCont (E := E) es y = evalTree (some r) := by
    intro p y hr
    induction hr with
    | @done p y hx =>
      rcases loopG_spec bt body ih p with h | ⟨np, nr, s₁, f₁, fl, ha, hev, h⟩
      · rw [h] at hx; exact absurd hx.symm (ret_ne_diverge _)
      rcases h with ⟨vs, rfl, h⟩ | ⟨vs, rfl, h⟩ | ⟨k, vs, rfl, h⟩ | ⟨hesc, v, hv, h⟩
      · rw [h] at hx; cases ret_inj.1 hx
      · rw [h] at hx; cases ret_inj.1 hx
        rcases hes s₁ f₁ (vs.take nr ++ p.1.down.2.drop np) with hd | ⟨r, hk, hr⟩
        · exact .inl hd
        · exact .inr ⟨r, .loopOk ha hev hk, hr⟩
      · rw [h] at hx; cases ret_inj.1 hx
        exact .inr ⟨_, .loopBrk ha hev, rfl⟩
      · rw [h] at hx; cases ret_inj.1 hx
        refine .inr ⟨_, .loopEsc ha hev hesc, ?_⟩
        rw [hv]
        cases fl <;> first | exact absurd hesc id | (simp only [evalTree] at hv; cases ret_inj.1 hv; rfl)
    | @step p x' y hx _ ihr =>
      rcases loopG_spec bt body ih p with h | ⟨np, nr, s₁, f₁, fl, ha, hev, h⟩
      · rw [h] at hx; exact absurd hx.symm (ret_ne_diverge _)
      rcases h with ⟨vs, rfl, h⟩ | ⟨vs, rfl, h⟩ | ⟨k, vs, rfl, h⟩ | ⟨hesc, v, hv, h⟩
      · rw [h] at hx; cases ret_inj.1 hx
        rcases ihr with hd | ⟨r, hk, hr⟩
        · exact .inl hd
        · exact .inr ⟨r, .loopBack ha hev hk, hr⟩
      all_goals (rw [h] at hx; cases ret_inj.1 hx)
  rcases iter_pure hpure (⟨(f, stk)⟩, ⟨s⟩) with ⟨y, hr, hy⟩ | ⟨hd, -⟩
  · rcases key _ _ hr with hd | ⟨r, hk, hr'⟩
    · left; rw [hrun, hy]; exact (pure_bind _ _).trans hd
    · right; exact ⟨r, hk, by rw [hrun, hy]; exact (pure_bind _ _).trans hr'⟩
  · left; rw [hrun, hd, diverge_bind]

/-! ## The induction -/

theorem good_congr {x y : M E H Res} {k : Res → M E H Res} {s t : St H}
    {P : Store H × Frame × Flow → Prop} (h : run' x s = run' y t) (hy : Good (y >>= k) t P) :
    Good (x >>= k) s P := by
  unfold Good at hy ⊢
  rwa [run_bind_congr h]

theorem notCall {i : Instr} (hi : isCall i = false) : ∀ x, i ≠ .call x := by
  intro x h; subst h; simp [isCall] at hi

/-- A block body run, then its exits, then the continuation. -/
theorem block_cont {np nr : Nat} {stk : List Val} {es : List BExpr} {y : M E H Res} {s : St H}
    {s₁ : Store H} {f₁ : Frame} {fl : Flow} {P : Store H × Frame × Flow → Prop}
    (hy : run' y s = evalTree (some (s₁, f₁, fl)))
    (hes : ∀ s f stk, Good (denList es f stk : M E H Res) ⟨s⟩ (Eval s f stk es))
    (hok : ∀ vs r, fl.blockVals = some vs → Eval s₁ f₁ (vs.take nr ++ stk.drop np) es r → P r)
    (hbrk : ∀ k vs, fl = .brk (k + 1) vs → P (s₁, f₁, .brk k vs))
    (hesc : fl.Escapes → P (s₁, f₁, fl)) :
    Good ((y >>= blockK np nr stk) >>= thenK (denList es)) s P := by
  rcases blockK_eval (np := np) (nr := nr) (stk := stk) hy with
    ⟨vs, hvs, h⟩ | ⟨k, vs, hk, h⟩ | ⟨he, h⟩
  · exact (good_cont h (hes _ _ _)).mono fun r hr => hok vs r hvs hr
  · exact good_pass h Flow.notNormal_brk (hbrk k vs hk)
  · exact good_pass h (Flow.not_normal_of_escapes he) (hesc he)

mutual

theorem tree_good : ∀ (e : BExpr) (es : List BExpr), callFree e = true →
    (∀ s f stk, Good (denList es f stk : M E H Res) ⟨s⟩ (Eval s f stk es)) →
    ∀ s f stk, Good (den e f stk >>= thenK (denList es) : M E H Res) ⟨s⟩
      (Eval s f stk (e :: es))
  | .op i args, es, hc, hes, s, f, stk => by
    simp only [callFree, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rw [den]
    simp only [hc.1, Bool.false_eq_true, ↓reduceIte]
    rcases list_good args hc.2 s f stk with hd | ⟨⟨s₁, f₁, fl₁⟩, hev, hy⟩
    · exact good_div (run_bind_diverge (run_bind_diverge hd))
    cases fl₁
    case normal stk₁ =>
      have hx : run' (denList args f stk >>= thenK (flatK i) : M E H Res) ⟨s⟩ =
          evalTree (evalFlat s₁ f₁ stk₁ i) := by
        rw [run_bind_eval hy]; exact run_flatK i f₁ stk₁ s₁
      cases he : evalFlat s₁ f₁ stk₁ i with
      | none => rw [he] at hx; exact good_div (run_bind_diverge hx)
      | some r₂ =>
        obtain ⟨s₂, f₂, fl₂⟩ := r₂
        rw [he] at hx
        cases fl₂
        case normal stk₂ =>
          exact (good_cont hx (hes _ _ _)).mono fun r hr => .opOk (notCall hc.1) hev he hr
        all_goals
          refine good_pass hx ?_ (.opStop (notCall hc.1) hev he ?_) <;> simp [Flow.IsNormal]
    all_goals
      refine good_pass (pass_thenK hy ?_) ?_ (.argsAbort hev ?_) <;> simp [Flow.IsNormal]
  | .block bt body, es, hc, hes, s, f, stk => by
    simp only [callFree] at hc
    rw [den]
    cases ha : arity f bt with
    | none => exact good_div (run_bind_diverge (run_stuck _))
    | some p =>
      obtain ⟨np, nr⟩ := p
      simp only
      rcases list_good body hc s f (stk.take np) with hd | ⟨⟨s₁, f₁, fl⟩, hev, hy⟩
      · exact good_div (run_bind_diverge (run_bind_diverge hd))
      exact block_cont hy hes (fun vs r hvs hr => .blockOk ha hev hvs hr)
        (fun k vs hk => by subst hk; exact .blockBrk ha hev) (fun he => .blockEsc ha hev he)
  | .loop bt body, es, hc, hes, s, f, stk => by
    simp only [callFree] at hc
    exact loop_good bt body es (list_good body hc) hes s f stk
  | .if_ bt c t el, es, hc, hes, s, f, stk => by
    simp only [callFree, Bool.and_eq_true] at hc
    obtain ⟨⟨hcc, hct⟩, hce⟩ := hc
    rw [den]
    rcases list_good c hcc s f stk with hd | ⟨⟨s₁, f₁, fl₁⟩, hev, hy⟩
    · exact good_div (run_bind_diverge (run_bind_diverge hd))
    cases fl₁
    case normal stk₁ =>
      rcases stk₁ with _ | ⟨cv, stk₁⟩
      · refine good_div (run_bind_diverge ?_)
        rw [run_bind_eval hy]; rfl
      cases hb : truthy cv with
      | none =>
        refine good_div (run_bind_diverge ?_)
        rw [run_bind_eval hy]; simp only [bindTree, hb]; rfl
      | some b =>
        cases ha : arity f₁ bt with
        | none =>
          refine good_div (run_bind_diverge ?_)
          rw [run_bind_eval hy]; simp only [bindTree, hb, ha]; rfl
        | some p =>
          obtain ⟨np, nr⟩ := p
          have harm : Good ((if b then denList t f₁ (stk₁.take np) else
              denList el f₁ (stk₁.take np)) : M E H Res) ⟨s₁⟩
              (Eval s₁ f₁ (stk₁.take np) (if b then t else el)) := by
            cases b
            · exact list_good el hce s₁ f₁ _
            · exact list_good t hct s₁ f₁ _
          refine good_congr (y := (if b then denList t f₁ (stk₁.take np) else
              denList el f₁ (stk₁.take np)) >>= blockK np nr stk₁) (t := ⟨s₁⟩) ?_ ?_
          · rw [run_bind_eval hy]; simp only [bindTree, hb, ha]
          rcases harm with hd | ⟨⟨s₂, f₂, fl₂⟩, hev₂, hy₂⟩
          · exact good_div (run_bind_diverge (run_bind_diverge hd))
          exact block_cont hy₂ hes (fun vs r hvs hr => .ifOk hev hb ha hev₂ hvs hr)
            (fun k vs hk => by subst hk; exact .ifBrk hev hb ha hev₂)
            (fun he => .ifEsc hev hb ha hev₂ he)
    all_goals
      refine good_pass (fl := _) ?_ (by simp [Flow.IsNormal]) (.ifAbort hev (by simp [Flow.IsNormal]))
      rw [run_bind_eval hy]; rfl
  | .tryTable .., _, hc, _, _, _, _ => by simp [callFree] at hc

theorem list_good : ∀ (es : List BExpr), callFreeL es = true →
    ∀ s f stk, Good (denList es f stk : M E H Res) ⟨s⟩ (Eval s f stk es)
  | [], _, s, f, stk => .inr ⟨_, .nil, rfl⟩
  | e :: es, hc, s, f, stk => by
    simp only [callFreeL, Bool.and_eq_true] at hc
    rw [denList]
    exact tree_good e es hc.1 (list_good es hc.2) s f stk

end

end Silmaril.Proofs.Wasm.Abstract.StoreBody
