module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding

/-- Distinct original syntax stays distinct in the extension. -/
theorem term_injective {k : ℕ} : Function.Injective (@term k) := by
  intro a b
  induction a <;> cases b <;> simp_all [term] <;> aesop


@[simp]
theorem term_wkn {k : ℕ} (t : ETm k) (j : ℕ) :
    term (t.wkn j) = (term t).wkn j := by
  induction t generalizing j <;> simp_all [ETm.wkn, Tm.wkn, term, apply_ite]

@[simp]
theorem term_wk0 {k : ℕ} (t : ETm k) : term t.wk0 = (term t).wk0 :=
  term_wkn t 0

@[simp]
theorem term_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) :
    term (t.castLE h) = (term t).castLE h := by
  induction t generalizing m <;> simp_all [ETm.castLE, Tm.castLE, term]

@[simp]
theorem term_open {k : ℕ} (t : ETm (k + 1)) (x : String) :
    term (t.open x) = (term t).open x := by
  induction k, t using ETm.open.induct with
  | case2 k i =>
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [ETm.open, Tm.open, term]
  | _ => simp_all [ETm.open, Tm.open, term]

@[simp]
theorem term_lst {k : ℕ} (t : ETm (k + 1)) (v : ETm 0) :
    term (t.lst v) = (term t).lst (term v) := by
  induction k, t using ETm.lst.induct with
  | case2 k i =>
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [ETm.lst, Tm.lst, term]
  | _ => simp_all [ETm.lst, Tm.lst, term]

@[simp]
theorem term_arr {k : ℕ} (A B : ETm k) : term (A.arr B) = (term A).arr (term B) := by
  simp [ETm.arr, Tm.arr, term]

@[simp]
theorem context_dv (Γ : ECtx) : (context Γ).dv = Γ.dv := by
  induction Γ <;> simp_all [context, Ctx.dv, ECtx.dv]

theorem lookup {Γ : ECtx} {x : String} {A : ETm 0} (h : Γ.Lookup x A) :
    (context Γ).Lookup x (term A) := by
  induction h with
  | here => exact .here _ _ _
  | there _ _ _ _ _ _ hxy ih => exact .there _ _ _ _ _ ih hxy

/-- Every original inference remains derivable, including arbitrary hypothesis leaves. -/
theorem preserves {H : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqH H Γ A a b) :
    Ctx.JEqH (theory H) (context Γ) (term A) (term a) (term b) := by
  induction h with
  | hyp hj => exact .hyp ⟨_, hj, rfl⟩
  | nil_ok => exact .nil_ok
  | cons_ok _ hx _ ihΓ ihA => exact .cons_ok ihΓ (by simpa [term, context] using hx) ihA
  | var _ hx ih => exact .var ih (lookup hx)
  | univ _ ih => exact .univ ih
  | empty _ ih => exact .empty ih
  | unit _ ih => exact .unit ih
  | nats _ ih => exact .nats ih
  | zero _ ih => exact .zero ih
  | succ _ ih => exact .succ ih
  | pi _ _ ihA ihB => exact .pi ihA (by simpa [term, context] using ihB)
  | sigma _ _ ihA ihB => exact .sigma ihA (by simpa [term, context] using ihB)
  | id _ _ _ ihA iha ihb => exact .id ihA iha ihb
  | abs _ _ _ ihA ihB ihb => exact .abs ihA (by simpa [term, context] using ihB) (by simpa [term, context] using ihb)
  | app _ _ _ _ ihA ihB ihf iha =>
    simpa [term] using Ctx.JEqH.app ihA (by simpa [term, context] using ihB) ihf iha
  | pair _ _ _ _ ihA ihB iha ihb =>
    exact .pair ihA (by simpa [term, context] using ihB) iha (by simpa [term, context] using ihb)
  | fst _ _ _ ihA ihB ihp => exact .fst ihA (by simpa [term, context] using ihB) ihp
  | snd _ _ _ ihA ihB ihp =>
    simpa [term] using Ctx.JEqH.snd ihA (by simpa [term, context] using ihB) ihp
  | natrec _ _ _ _ ihC ihz ihs ihm =>
    simpa [term] using Ctx.JEqH.natrec (by simpa [term, context] using ihC) (by simpa [term, context] using ihz)
      (by simpa [term, context] using ihs) ihm
  | refl _ ih => exact .refl ih
  | absurd _ _ ihC ihe => exact .absurd ihC ihe
  | beta_app _ _ _ _ ihA ihB ihb iha =>
    simpa [term] using Ctx.JEqH.beta_app ihA (by simpa [term, context] using ihB) (by simpa [term, context] using ihb) iha
  | beta_fst _ _ _ _ ihA ihB iha ihb =>
    exact .beta_fst ihA (by simpa [term, context] using ihB) iha (by simpa [term, context] using ihb)
  | beta_snd _ _ _ _ ihA ihB iha ihb =>
    simpa [term] using Ctx.JEqH.beta_snd ihA (by simpa [term, context] using ihB) iha (by simpa [term, context] using ihb)
  | beta_natrec_zero _ _ _ ihC ihz ihs =>
    simpa [term] using Ctx.JEqH.beta_natrec_zero (by simpa [term, context] using ihC) (by simpa [term, context] using ihz)
      (by simpa [term, context] using ihs)
  | beta_natrec_succ _ _ _ _ ihC ihz ihs ihm =>
    simpa [term] using Ctx.JEqH.beta_natrec_succ (by simpa [term, context] using ihC) (by simpa [term, context] using ihz)
      (by simpa [term, context] using ihs) ihm
  | reflect _ _ _ iha ihb ihp => exact .reflect iha ihb ihp
  | id_uip _ _ _ iha ihb ihp => exact .id_uip iha ihb ihp
  | unit_ext _ ih => exact .unit_ext ih
  | pi_ext _ _ _ _ _ ihA ihB ihf ihg ihfg =>
    exact .pi_ext ihA (by simpa [term, context] using ihB) ihf ihg (by simpa [term, context] using ihfg)
  | sigma_ext _ _ _ _ _ _ ihA ihB ihp ihq ih1 ih2 =>
    exact .sigma_ext ihA (by simpa [term, context] using ihB) ihp ihq ih1 (by simpa [term, context] using ih2)
  | symm _ ih => exact .symm ih
  | trans _ _ ihab ihbc => exact .trans ihab ihbc
  | conv _ _ ihA iha => exact .conv ihA iha
  | cumul hmn _ ihA => exact .cumul hmn ihA

/-- Closed-theory base derivations remain closed-theory derivations in the extension. -/
theorem preserves_closed {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEq Γ A a b) :
    (context Γ).JEq (term A) (term a) (term b) := by
  simpa [theory] using preserves (h.toJEqH (H := ∅))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding
