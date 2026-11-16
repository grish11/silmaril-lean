module

public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.OpW

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: **the stack tensor on checked
stack-pure code.** Running checked code on `stk ++ rest`, with `stk` at the checked height, is
running it on `stk` with `rest` appended below every fallthrough, read at the arities of the
branch and return targets (`trimP`); and its results satisfy `GoodR`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Interp

variable {H : Type}

theorem arity_module (f : Frame) (bt : BlockType) : arity f bt = blockArity f.module bt := by
  cases bt <;> rfl

theorem endsAt_inv {r : Option (Option Nat)} {n : Nat} (h : endsAt r n = true) :
    ∃ ob, r = some ob ∧ (ob = none ∨ ob = some n) := by
  rcases r with _ | _ | k
  · simp [endsAt] at h
  · exact ⟨none, rfl, .inl rfl⟩
  · simp only [endsAt, beq_iff_eq] at h
    exact ⟨some k, rfl, .inr (by rw [h])⟩

section Chk

variable {tags : List TagInst} {F : List (FuncInst H)} {env : Env}

theorem chk_cons' {h : Nat} {e : BExpr} {es : List BExpr} {o : Option Nat} :
    chkE (ehExt tags) F env.mi env.nl env.ret env.labels (some h) (e :: es) = some o ↔
      ∃ o₁, chk1E (ehExt tags) F env.mi env.nl env.ret env.labels h e = some o₁ ∧
        chkE (ehExt tags) F env.mi env.nl env.ret env.labels o₁ es = some o := by
  simp only [chkE, Option.bind_eq_some_iff]

theorem chk1_op' {h : Nat} {i : Instr} {args : List BExpr} {o : Option Nat}
    (hc : chk1E (ehExt tags) F env.mi env.nl env.ret env.labels h (.op i args) = some o) :
    ∃ oa, chkE (ehExt tags) F env.mi env.nl env.ret env.labels (some h) args = some oa ∧
      ∀ h₁, oa = some h₁ →
        flatChkE (ehExt tags) F env.mi env.nl env.ret env.labels h₁ i = some o := by
  simp only [chk1E, Option.bind_eq_some_iff] at hc
  obtain ⟨oa, ha, hb⟩ := hc
  exact ⟨oa, ha, by rintro h₁ rfl; exact hb⟩

theorem chk1_block' {h : Nat} {bt : BlockType} {body : List BExpr} {o : Option Nat}
    (hc : chk1E (ehExt tags) F env.mi env.nl env.ret env.labels h (.block bt body) = some o) :
    ∃ np nr, blockArity env.mi bt = some (np, nr) ∧ np ≤ h ∧
      (∃ ob, chkE (ehExt tags) F (env.push nr).mi (env.push nr).nl (env.push nr).ret
        (env.push nr).labels (some np) body = some ob ∧ (ob = none ∨ ob = some nr)) ∧
      o = some (h - np + nr) := by
  simp only [chk1E] at hc
  split at hc
  · rename_i np nr ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1, endsAt_inv hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem chk1_loop' {h : Nat} {bt : BlockType} {body : List BExpr} {o : Option Nat}
    (hc : chk1E (ehExt tags) F env.mi env.nl env.ret env.labels h (.loop bt body) = some o) :
    ∃ np nr, blockArity env.mi bt = some (np, nr) ∧ np ≤ h ∧
      (∃ ob, chkE (ehExt tags) F (env.push np).mi (env.push np).nl (env.push np).ret
        (env.push np).labels (some np) body = some ob ∧ (ob = none ∨ ob = some nr)) ∧
      o = some (h - np + nr) := by
  simp only [chk1E] at hc
  split at hc
  · rename_i np nr ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1, endsAt_inv hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem chk1_if' {h : Nat} {bt : BlockType} {c t el : List BExpr} {o : Option Nat}
    (hc : chk1E (ehExt tags) F env.mi env.nl env.ret env.labels h (.if_ bt c t el) = some o) :
    ∃ oc, chkE (ehExt tags) F env.mi env.nl env.ret env.labels (some h) c = some oc ∧
      ∀ h₁, oc = some h₁ → ∃ np nr, blockArity env.mi bt = some (np, nr) ∧ np + 1 ≤ h₁ ∧
        (∃ ot, chkE (ehExt tags) F (env.push nr).mi (env.push nr).nl (env.push nr).ret
          (env.push nr).labels (some np) t = some ot ∧ (ot = none ∨ ot = some nr)) ∧
        (∃ oe, chkE (ehExt tags) F (env.push nr).mi (env.push nr).nl (env.push nr).ret
          (env.push nr).labels (some np) el = some oe ∧ (oe = none ∨ oe = some nr)) ∧
        o = some (h₁ - 1 - np + nr) := by
  simp only [chk1E, Option.bind_eq_some_iff] at hc
  obtain ⟨oc, hcc, hb⟩ := hc
  refine ⟨oc, hcc, ?_⟩
  rintro h₁ rfl
  simp only at hb
  split at hb
  · rename_i np nr ha
    split at hb
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1.1, endsAt_inv hcond.1.2, endsAt_inv hcond.2,
        (Option.some.inj hb).symm⟩
    · cases hb
  · cases hb

end Chk

/-! ## Exits keep the invariant -/

theorem blockKP_lands {env : Env} {np nr h : Nat} {stk : List Val} (hs : stk.length = h)
    (hle : np ≤ h) {ob : Option Nat} (hob : ob = none ∨ ob = some nr) (r : ResP)
    (hr : GoodR (env.push nr) ob r) :
    Lands (H := H) (GoodR env (some (h - np + nr))) (blockKP np nr stk r) := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs =>
      obtain ⟨hm, hl⟩ := hr
      have : vs.length = nr := by rcases hob with rfl | rfl <;> simp_all
      refine lands_pure ⟨hm, ?_⟩
      simp only [List.length_append, List.length_take, List.length_drop]
      congr 1
      omega
    | brk k vs =>
      obtain ⟨hm, n, hn, hl⟩ := hr
      cases k with
      | zero =>
        simp only [Env.push, List.getElem?_cons_zero, Option.some.injEq] at hn
        subst hn
        refine lands_pure ⟨hm, ?_⟩
        simp only [List.length_append, List.length_take, List.length_drop]
        congr 1
        omega
      | succ k =>
        simp only [Env.push, List.getElem?_cons_succ] at hn
        exact lands_pure ⟨hm, n, hn, hl⟩
    | ret vs => exact lands_pure hr
    | _ => exact lands_pure trivial
  · exact lands_pure trivial

/-- The loop's states: the frame's instance and the loop's height. -/
def LoopSt (env : Env) (h : Nat) (c : Cfg) : Prop := c.down.1.module = env.mi ∧ c.down.2.length = h

theorem loopKP_landsG {env : Env} {np nr h : Nat} {stk : List Val} (hs : stk.length = h)
    (hle : np ≤ h) {ob : Option Nat} (hob : ob = none ∨ ob = some nr) (r : ResP)
    (hr : GoodR (env.push np) ob r) :
    Lands (H := H) (Sum.elim (GoodR env (some (h - np + nr))) (LoopSt env h))
      (loopKP np nr stk r) := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs =>
      obtain ⟨hm, hl⟩ := hr
      have : vs.length = nr := by rcases hob with rfl | rfl <;> simp_all
      refine lands_pure (P := Sum.elim _ _) (a := .inl _) ⟨hm, ?_⟩
      simp only [List.length_append, List.length_take, List.length_drop]
      congr 1
      omega
    | brk k vs =>
      obtain ⟨hm, n, hn, hl⟩ := hr
      cases k with
      | zero =>
        simp only [Env.push, List.getElem?_cons_zero, Option.some.injEq] at hn
        subst hn
        refine lands_pure (P := Sum.elim _ _) (a := .inr _) ⟨hm, ?_⟩
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      | succ k =>
        simp only [Env.push, List.getElem?_cons_succ] at hn
        exact lands_pure (P := Sum.elim _ _) (a := .inl _) ⟨hm, n, hn, hl⟩
    | ret vs => exact lands_pure (P := Sum.elim _ _) (a := .inl _) hr
    | _ => exact lands_pure (P := Sum.elim _ _) (a := .inl _) trivial
  · exact lands_pure (P := Sum.elim _ _) (a := .inl _) trivial

theorem brkOk_of_good {env : Env} {bt : BlockType} {np nr : Nat}
    (hbt : blockArity env.mi bt = some (np, nr)) {ob : Option Nat} (r : ResP)
    (hr : GoodR (env.push np) ob r) :
    BrkOk (fun f => f.module = env.mi) bt np nr r := by
  rintro f vs rfl
  obtain ⟨hm, n, hn, hl⟩ := hr
  simp only [Env.push, List.getElem?_cons_zero, Option.some.injEq] at hn
  subst hn
  exact ⟨hm, by rw [arity_module, hm]; exact hbt, hl⟩

/-! ## The induction -/

theorem denXP_op' (i : Instr) (args : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.op i args) f stk) = denListXP args f stk >>= thenKP (opCXP i) :=
  congrFun (denT_op i args) ⟨(f, stk)⟩

theorem denXP_block' (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.block bt body) f stk) = blockP bt (denL body) ⟨(f, stk)⟩ :=
  congrFun (denT_block bt body) ⟨(f, stk)⟩

theorem denXP_loop' (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.loop bt body) f stk) = loopP bt (denL body) ⟨(f, stk)⟩ :=
  congrFun (denT_loop bt body) ⟨(f, stk)⟩

theorem denXP_if' (bt : BlockType) (c t el : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.if_ bt c t el) f stk) =
      denListXP c f stk >>= ifKP bt (denL t) (denL el) :=
  congrFun (denT_if bt c t el) ⟨(f, stk)⟩

theorem obsP_map {L : List Nat} {R : Nat} (rest : List Val) (x : M (CallSig H) H ResP) :
    obsP L R (whiskP rest <$> x) = x >>= fun r => pure (trimP L R (whiskP rest r)) := by
  simp only [obsP, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

theorem take_len {stk : List Val} {np h : Nat} (hs : stk.length = h) (hle : np ≤ h) :
    (stk.take np).length = np := by
  rw [List.length_take, hs]; omega

variable {tags : List TagInst} {F : List (FuncInst H)}

mutual

theorem treeW : ∀ (env : Env) (e : BExpr) (h : Nat) (o : Option Nat) (f : Frame)
    (stk : List Val), stackPure e = true →
    chk1E (ehExt tags) F env.mi env.nl env.ret env.labels h e = some o →
    f.module = env.mi → stk.length = h →
    Lands (GoodR env o) (denXP (H := H) e f stk) ∧ ∀ rest,
      obsP env.labels env.ret (denXP (H := H) e f (stk ++ rest)) =
        denXP e f stk >>= fun r => pure (trimP env.labels env.ret (whiskP rest r))
  | env, .op i args, h, o, f, stk, hp, hc, hf, hs => by
    simp only [stackPure, Bool.and_eq_true] at hp
    obtain ⟨oa, ha, hsome⟩ := chk1_op' hc
    have IH := listW env args h oa f stk hp.2 ha hf hs
    refine ⟨?_, fun rest => ?_⟩
    · rw [denXP_op']
      exact cont_lands IH.1 (thenKP_notNormal _) fun f' vs hm hlen =>
        (op_whisk hp.1 (hsome _ hlen) hm []).1
    · rw [denXP_op', denXP_op']
      exact cont_whisk rest IH.1 (IH.2 rest) (thenKP_notNormal _) fun f' vs hm hlen =>
        (op_whisk hp.1 (hsome _ hlen) hm rest).2
  | env, .block bt body, h, o, f, stk, hp, hc, hf, hs => by
    simp only [stackPure] at hp
    obtain ⟨np, nr, hbt, hle, ⟨ob, hob, hobv⟩, rfl⟩ := chk1_block' hc
    have har : arity f bt = some (np, nr) := by rw [arity_module, hf]; exact hbt
    have IH := listW (env.push nr) body np ob f (stk.take np) hp hob hf (take_len hs hle)
    refine ⟨?_, fun rest => ?_⟩
    · rw [denXP_block']
      simp only [blockP, har]
      exact lands_bind IH.1 fun r hr => blockKP_lands hs hle hobv r hr
    · rw [denXP_block', denXP_block']
      have hw := blockP_whisk bt (denL (H := H) body) rest ⟨(f, stk)⟩ har (by simp only [hs]; exact hle)
      simp only [wcfg] at hw
      rw [hw, obsP_map]
  | env, .loop bt body, h, o, f, stk, hp, hc, hf, hs => by
    simp only [stackPure] at hp
    obtain ⟨np, nr, hbt, hle, ⟨ob, hob, hobv⟩, rfl⟩ := chk1_loop' hc
    have har : arity f bt = some (np, nr) := by rw [arity_module, hf]; exact hbt
    have IHb : ∀ c : Cfg, c.down.1.module = env.mi → np ≤ c.down.2.length →
        Lands (GoodR (env.push np) ob) (denL (H := H) body ⟨(c.down.1, c.down.2.take np)⟩) :=
      fun c hm hl => (listW (env.push np) body np ob c.down.1 (c.down.2.take np) hp hob hm
        (take_len rfl hl)).1
    refine ⟨?_, fun rest => ?_⟩
    · rw [denXP_loop']
      refine lands_iter (loopStepP bt (denL body)) (LoopSt env h) _ (fun c hc => ?_) _ ⟨hf, hs⟩
      have hac : arity c.down.1 bt = some (np, nr) := by rw [arity_module, hc.1]; exact hbt
      simp only [loopStepP, hac]
      exact lands_bind (IHb c hc.1 (by rw [hc.2]; exact hle)) fun r hr =>
        loopKP_landsG hc.2 hle hobv r hr
    · rw [denXP_loop', denXP_loop']
      have hw := loopP_whisk (fun f => f.module = env.mi) bt (denL (H := H) body) rest
        (fun c hc => lands_mono (fun r hr => brkOk_of_good hbt r hr) (IHb c hc.1 hc.2.2))
        ⟨(f, stk)⟩ ⟨hf, har, by simp only [hs]; exact hle⟩
      simp only [wcfg] at hw
      rw [hw, obsP_map]
  | env, .if_ bt c t el, h, o, f, stk, hp, hc, hf, hs => by
    simp only [stackPure, Bool.and_eq_true] at hp
    obtain ⟨oc, hcc, hsome⟩ := chk1_if' hc
    have IHc := listW env c h oc f stk hp.1.1 hcc hf hs
    refine ⟨?_, fun rest => ?_⟩
    · rw [denXP_if']
      refine cont_lands IHc.1 (ifKP_notNormal _ _ _) fun f₁ vs hm hlen => ?_
      obtain ⟨np, nr, hbt, hle, ⟨ot, hot, hotv⟩, ⟨oe, hoe, hoev⟩, rfl⟩ := hsome vs.length hlen
      obtain ⟨cv, stk₁, rfl⟩ : ∃ cv stk₁, vs = cv :: stk₁ := by
        cases vs with
        | nil => simp at hle
        | cons cv stk₁ => exact ⟨cv, stk₁, rfl⟩
      have har : arity f₁ bt = some (np, nr) := by rw [arity_module, hm]; exact hbt
      have hle₁ : np ≤ stk₁.length := by simp only [List.length_cons] at hle; omega
      have hlen₁ : (cv :: stk₁).length - 1 - np + nr = stk₁.length - np + nr := by simp
      rw [hlen₁]
      simp only [ifKP, har]
      cases truthy cv with
      | none => exact lands_stuck
      | some b =>
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          exact lands_bind (listW (env.push nr) el np oe f₁ (stk₁.take np) hp.2 hoe hm
            (take_len rfl hle₁)).1 fun r hr => blockKP_lands rfl hle₁ hoev r hr
        · simp only [ite_true]
          exact lands_bind (listW (env.push nr) t np ot f₁ (stk₁.take np) hp.1.2 hot hm
            (take_len rfl hle₁)).1 fun r hr => blockKP_lands rfl hle₁ hotv r hr
    · rw [denXP_if', denXP_if']
      refine cont_whisk rest IHc.1 (IHc.2 rest) (ifKP_notNormal _ _ _) fun f₁ vs hm hlen => ?_
      obtain ⟨np, nr, hbt, hle, -, -, -⟩ := hsome vs.length hlen
      obtain ⟨cv, stk₁, rfl⟩ : ∃ cv stk₁, vs = cv :: stk₁ := by
        cases vs with
        | nil => simp at hle
        | cons cv stk₁ => exact ⟨cv, stk₁, rfl⟩
      have har : arity f₁ bt = some (np, nr) := by rw [arity_module, hm]; exact hbt
      have hle₁ : np ≤ stk₁.length := by simp only [List.length_cons] at hle; omega
      rw [List.cons_append, ifKP_whisk bt _ _ rest f₁ cv stk₁ har hle₁, obsP_map]
  | env, .tryTable bt cs body, h, o, f, stk, hp, hc, hf, hs => by
    simp [stackPure] at hp

theorem listW : ∀ (env : Env) (es : List BExpr) (h : Nat) (o : Option Nat) (f : Frame)
    (stk : List Val), stackPureL es = true →
    chkE (ehExt tags) F env.mi env.nl env.ret env.labels (some h) es = some o →
    f.module = env.mi → stk.length = h →
    Lands (GoodR env o) (denListXP (H := H) es f stk) ∧ ∀ rest,
      obsP env.labels env.ret (denListXP (H := H) es f (stk ++ rest)) =
        denListXP es f stk >>= fun r => pure (trimP env.labels env.ret (whiskP rest r))
  | env, [], h, o, f, stk, _, hc, hf, hs => by
    have ho : o = some h := (Option.some.inj hc).symm
    subst ho
    refine ⟨?_, fun rest => ?_⟩
    · rw [denListXP_nil]; exact lands_pure ⟨hf, by rw [hs]⟩
    · rw [denListXP_nil, denListXP_nil, obsP, pure_bind, pure_bind]; rfl
  | env, e :: es, h, o, f, stk, hp, hc, hf, hs => by
    simp only [stackPureL, Bool.and_eq_true] at hp
    obtain ⟨o₁, h1, h2⟩ := chk_cons'.1 hc
    have IHe := treeW env e h o₁ f stk hp.1 h1 hf hs
    refine ⟨?_, fun rest => ?_⟩
    · rw [denListXP_cons]
      exact cont_lands IHe.1 (thenKP_notNormal _) fun f' vs hm hlen =>
        (listW env es vs.length o f' vs hp.2 (by rw [← hlen]; exact h2) hm rfl).1
    · rw [denListXP_cons, denListXP_cons]
      exact cont_whisk rest IHe.1 (IHe.2 rest) (thenKP_notNormal _) fun f' vs hm hlen =>
        (listW env es vs.length o f' vs hp.2 (by rw [← hlen]; exact h2) hm rfl).2 rest

end

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct
