module

public import Silmaril.Wasm.Abstract.StoreBody.Defs

/-! Proofs for `Silmaril.Wasm.Abstract.StoreBody.Thms`: the lifted primitive. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreBody

open Silmaril.Wasm Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Elgot.ITree

variable {E : Sig.{0}} {H : Type}

theorem run_ofEval (o : Option (Store H × Frame × Flow)) (s : St H) :
    ((ofEval o : M E H Res).run s).run = evalTree o := by
  rcases o with _ | ⟨s', f', fl⟩
  · rfl
  · cases fl
    case trap =>
      simp [ofEval, evalTree, trap, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.run,
        ExceptT.mk, Functor.map, ExceptT.map, StateT.run]
      rfl
    all_goals
      simp only [ofEval, setState, evalTree, StateT.run_bind, StateT.run_set, ExceptT.run_bind]
      exact pure_bind _ _

theorem run_flatK (i : Instr) (f : Frame) (stk : List Val) (s : Store H) :
    ((flatK i f stk : M E H Res).run ⟨s⟩).run = evalTree (evalFlat s f stk i) := by
  simp only [flatK, getState, StateT.run_bind, StateT.run_get, ExceptT.run_bind, ExceptT.run_pure]
  refine (pure_bind _ _).trans ?_
  exact run_ofEval _ ⟨s⟩

/-- A body run from a store, as an interaction tree. -/
noncomputable abbrev run' {X : Type 1} (x : M E H X) (s : St H) :
    Tree (SigEv E) (Except PUnit.{2} (X × St H)) := (x.run s).run

theorem run_bind {X Y : Type 1} (x : M E H X) (k : X → M E H Y) (s : St H) :
    run' (x >>= k) s = run' x s >>= fun r =>
      match r with
      | .ok (a, s') => run' (k a) s'
      | .error e => pure (.error e) := by
  change ((x >>= k).run s).run = _
  rw [StateT.run_bind, ExceptT.run_bind]
  congr 1
  funext r
  rcases r with e | ⟨a, s'⟩ <;> rfl

/-- The run of `k` after an interpreter outcome. -/
noncomputable def bindTree {Y : Type 1} (k : Res → M E H Y) :
    Store H × Frame × Flow → Tree (SigEv E) (Except PUnit.{2} (Y × St H))
  | (_, _, .trap) => ret (.error ⟨⟩)
  | (s', f', fl) => run' (k ⟨(f', fl)⟩) ⟨s'⟩

/-- Bind after an interpreter outcome. -/
theorem run_bind_eval {Y : Type 1} {x : M E H Res} {k : Res → M E H Y} {s : St H}
    {r : Store H × Frame × Flow} (h : run' x s = evalTree (some r)) :
    run' (x >>= k) s = bindTree k r := by
  obtain ⟨s', f', fl⟩ := r
  rw [run_bind, h]
  cases fl <;> exact pure_bind _ _

theorem run_pure_res (r : Res) (s : St H) : run' (pure r : M E H Res) s = ret (.ok (r, s)) := rfl

/-- The interpreter's continuation after a tree. -/
def contR (n : Nat) (es : List BExpr) : Store H × Frame × Flow → Option (Store H × Frame × Flow)
  | (s', f', .normal stk') => run n s' f' stk' es
  | r => some r

theorem cont_sound {n : Nat} {es : List BExpr} {r : Store H × Frame × Flow}
    (IH : ∀ {s f stk r}, run n s f stk es = some r →
      run' (denList es f stk : M E H Res) ⟨s⟩ = evalTree (some r))
    {x : M E H Res} {s₀ : St H} {r₀ : Store H × Frame × Flow}
    (hx : run' x s₀ = evalTree (some r₀)) (h : contR n es r₀ = some r) :
    run' (x >>= thenK (denList es)) s₀ = evalTree (some r) := by
  rw [run_bind_eval hx]
  obtain ⟨s', f', fl⟩ := r₀
  cases fl <;> simp only [contR, bindTree, Option.some.injEq] at h ⊢
  all_goals first
    | (subst h; rfl)
    | exact IH h

theorem cont_pass {es : List BExpr} {r : Store H × Frame × Flow}
    {x : M E H Res} {s₀ : St H} {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (hx : run' x s₀ = evalTree (some (s₁, f₁, fl))) (hfl : ∀ stk, fl ≠ .normal stk)
    (h : some (s₁, f₁, fl) = some r) :
    run' (x >>= thenK (denList es)) s₀ = evalTree (some r) := by
  simp only [Option.some.injEq] at h
  subst h
  rw [run_bind_eval hx]
  cases fl
  case normal stk => exact absurd rfl (hfl stk)
  all_goals rfl

theorem run_op {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {args es : List BExpr} (hi : isCall i = false) :
    run (n + 1) s f stk (.op i args :: es) =
      match run n s f stk args with
      | some (s₁, f₁, .normal stk₁) => (evalFlat s₁ f₁ stk₁ i).bind (contR n es)
      | r => r := by
  rw [run.eq_def]
  simp only
  split
  · rename_i heq; simp only [BExpr.op.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; simp [isCall] at hi
  · rename_i heq; simp only [BExpr.op.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; rfl
  all_goals (rename_i heq; cases heq)

theorem run_bind_congr {X Y : Type 1} {x y : M E H X} {k : X → M E H Y} {s t : St H}
    (h : run' x s = run' y t) : run' (x >>= k) s = run' (y >>= k) t := by
  rw [run_bind, run_bind, h]

theorem den_loop_unfold (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (den (.loop bt body) f stk : M E H Res) =
      (loopBody bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => den (.loop bt body) c.down.1 c.down.2) := by
  rw [den]
  exact (congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M E H) (loopBody bt body))
    ⟨(f, stk)⟩).trans rfl

theorem run_stuck {X : Type 1} (s : St H) : run' (stuck : M E H X) s = diverge := rfl

/-- **Soundness against the native interpreter.** On call-free trees, every
outcome of `Binaryen.run` (with any fuel) is the abstract body's outcome: the
same final store, frame and flow, or a trap. -/
theorem run_sound : ∀ (n : Nat) {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow}, callFreeL es = true → run n s f stk es = some r →
    run' (denList es f stk : M E H Res) ⟨s⟩ = evalTree (some r)
  | 0, _, _, _, _, _, _, h => by rw [run.eq_def] at h; cases h
  | n + 1, s, f, stk, [], r, _, h => by rw [run.eq_def] at h; cases h; rfl
  | n + 1, s, f, stk, e :: es, r, hc₀, h => by
    have hc := hc₀
    simp only [callFreeL, Bool.and_eq_true] at hc
    have IH : ∀ {s f stk L r}, callFreeL L = true → run n s f stk L = some r →
        run' (denList L f stk : M E H Res) ⟨s⟩ = evalTree (some r) :=
      fun hL hr => run_sound n hL hr
    have IHes : ∀ {s f stk r}, run n s f stk es = some r →
        run' (denList es f stk : M E H Res) ⟨s⟩ = evalTree (some r) := fun hr => IH hc.2 hr
    rw [denList]
    cases e with
    | op i args =>
      simp only [callFree, Bool.and_eq_true, Bool.not_eq_true'] at hc
      rw [run_op hc.1.1] at h
      rw [den]
      simp only [hc.1.1, Bool.false_eq_true, ↓reduceIte]
      cases hr : run n s f stk args with
      | none => rw [hr] at h; cases h
      | some r₁ =>
        have h1 := IH hc.1.2 hr
        obtain ⟨s₁, f₁, fl₁⟩ := r₁
        rw [hr] at h
        cases fl₁
        case normal stk₁ =>
          simp only at h
          cases he : evalFlat s₁ f₁ stk₁ i with
          | none => rw [he] at h; cases h
          | some r₂ =>
            rw [he, Option.bind_some] at h
            refine cont_sound IHes ?_ h
            rw [run_bind_eval h1]
            simp only [bindTree, thenK]
            exact (run_flatK i f₁ stk₁ s₁).trans (by rw [he])
        all_goals exact cont_pass (by rw [run_bind_eval h1]; rfl) (by simp) h
    | block bt body =>
      simp only [callFree] at hc
      rw [run.eq_def] at h; simp only at h
      rw [den]
      cases ha : arity f bt with
      | none => rw [ha] at h; cases h
      | some p =>
        obtain ⟨np, nr⟩ := p
        simp only [ha] at h ⊢
        cases hr : run n s f (stk.take np) body with
        | none => rw [hr] at h; cases h
        | some r₁ =>
          have h1 := IH hc.1 hr
          obtain ⟨s₁, f₁, fl₁⟩ := r₁
          rw [hr] at h
          cases fl₁
          case normal vs =>
            refine cont_sound IHes (r₀ := (s₁, f₁, .normal (vs.take nr ++ stk.drop np))) ?_ h
            rw [run_bind_eval h1]; rfl
          case brk k vs =>
            cases k with
            | zero =>
              refine cont_sound IHes (r₀ := (s₁, f₁, .normal (vs.take nr ++ stk.drop np))) ?_ h
              rw [run_bind_eval h1]; rfl
            | succ k =>
              simp only [Option.some.injEq] at h
              subst h
              refine cont_sound IHes (r₀ := (s₁, f₁, .brk k vs)) ?_ rfl
              rw [run_bind_eval h1]; rfl
          all_goals exact cont_pass (by rw [run_bind_eval h1]; rfl) (by simp) h
    | loop bt body =>
      simp only [callFree] at hc
      rw [run.eq_def] at h; simp only at h
      cases ha : arity f bt with
      | none => rw [ha] at h; cases h
      | some p =>
        obtain ⟨np, nr⟩ := p
        simp only [ha] at h
        have hG : ∀ {r₁ : Store H × Frame × Flow}, run n s f (stk.take np) body = some r₁ →
            run' (loopBody bt body ⟨(f, stk)⟩ : M E H _) ⟨s⟩ =
              bindTree (loopK np nr stk) r₁ := by
          intro r₁ hr
          simp only [loopBody, ha]
          exact run_bind_eval (IH hc.1 hr)
        cases hr : run n s f (stk.take np) body with
        | none => rw [hr] at h; cases h
        | some r₁ =>
          obtain ⟨s₁, f₁, fl₁⟩ := r₁
          have hg := hG hr
          rw [hr] at h
          cases fl₁
          case normal vs =>
            refine cont_sound IHes (r₀ := (s₁, f₁, .normal (vs.take nr ++ stk.drop np))) ?_ h
            rw [den_loop_unfold, run_bind, hg]
            exact pure_bind _ _
          case brk k vs =>
            cases k with
            | zero =>
              have hl : run' (den (.loop bt body) f stk : M E H Res) ⟨s⟩ =
                  run' (den (.loop bt body) f₁ (vs.take np ++ stk.drop np) : M E H Res) ⟨s₁⟩ := by
                rw [den_loop_unfold, run_bind, hg]
                exact pure_bind _ _
              rw [run_bind_congr hl, ← denList]
              exact IH hc₀ h
            | succ k =>
              simp only [Option.some.injEq] at h
              subst h
              refine cont_sound IHes (r₀ := (s₁, f₁, .brk k vs)) ?_ rfl
              rw [den_loop_unfold, run_bind, hg]
              exact pure_bind _ _
          all_goals exact cont_pass (by rw [den_loop_unfold, run_bind, hg]; exact pure_bind _ _) (by simp) h
    | if_ bt c t el =>
      simp only [callFree, Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hcc, hct⟩, hce⟩, -⟩ := hc
      rw [run.eq_def] at h; simp only at h
      rw [den]
      cases hr : run n s f stk c with
      | none => rw [hr] at h; cases h
      | some r₁ =>
        have h1 := IH hcc hr
        obtain ⟨s₁, f₁, fl₁⟩ := r₁
        rw [hr] at h
        cases fl₁
        case normal stk₁ =>
          rcases stk₁ with _ | ⟨cv, stk₁⟩
          · simp only at h; cases h
          simp only at h
          cases ht : truthy cv with
          | none => rw [ht] at h; cases h
          | some b =>
            cases ha : arity f₁ bt with
            | none => rw [ht, ha] at h; cases h
            | some p =>
              obtain ⟨np, nr⟩ := p
              rw [ht, ha] at h
              simp only at h
              have hb : ∀ {r₂}, run n s₁ f₁ (stk₁.take np) (if b then t else el) = some r₂ →
                  run' ((if b then denList t f₁ (stk₁.take np) else denList el f₁ (stk₁.take np)) :
                    M E H Res) ⟨s₁⟩ = evalTree (some r₂) := by
                intro r₂ h₂
                cases b
                · exact IH hce h₂
                · exact IH hct h₂
              cases hr₂ : run n s₁ f₁ (stk₁.take np) (if b then t else el) with
              | none => rw [hr₂] at h; cases h
              | some r₂ =>
                obtain ⟨s₂, f₂, fl₂⟩ := r₂
                have h2 := hb hr₂
                rw [hr₂] at h
                have hx : ∀ {r₀}, bindTree (E := E) (blockK np nr stk₁) (s₂, f₂, fl₂) = evalTree (some r₀) →
                    run' (denList c f stk >>= fun r => match r with
                      | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
                        match truthy cv, arity f₁ bt with
                        | some b, some (np, nr) =>
                          (if b then denList t f₁ (stk₁.take np) else denList el f₁ (stk₁.take np)) >>=
                            blockK np nr stk₁
                        | _, _ => stuck
                      | ⟨(_, .normal [])⟩ => stuck
                      | r => pure r : M E H Res) ⟨s⟩ = evalTree (some r₀) := by
                  intro r₀ h₀
                  rw [run_bind_eval h1]
                  simp only [bindTree, ht, ha]
                  rw [run_bind_eval h2]
                  exact h₀
                cases fl₂
                case normal vs =>
                  exact cont_sound IHes (r₀ := (s₂, f₂, .normal (vs.take nr ++ stk₁.drop np)))
                    (hx rfl) h
                case brk k vs =>
                  cases k with
                  | zero =>
                    exact cont_sound IHes (r₀ := (s₂, f₂, .normal (vs.take nr ++ stk₁.drop np)))
                      (hx rfl) h
                  | succ k =>
                    simp only [Option.some.injEq] at h
                    subst h
                    exact cont_sound IHes (r₀ := (s₂, f₂, .brk k vs)) (hx rfl) rfl
                all_goals exact cont_pass (hx rfl) (by simp) h
        all_goals exact cont_pass (by rw [run_bind_eval h1]; rfl) (by simp) h
    | tryTable bt cs body => simp [callFree] at hc

end Silmaril.Proofs.Wasm.Abstract.StoreBody
