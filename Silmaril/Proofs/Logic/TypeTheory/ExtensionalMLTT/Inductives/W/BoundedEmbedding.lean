module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding

/-- Every base inference is translated at the same bound, including theory leaves
and all members of cofinite premise families. -/
theorem preserves_bounded {levels : ℕ} {H : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) :
    Ctx.JEqB levels (theory H) (context Γ) (term A) (term a) (term b) := by
  induction h with
  | hyp hj => exact .hyp ⟨_, hj, rfl⟩
  | nil_ok => exact .nil_ok
  | cons_ok hn _ hx _ ihΓ ihA => exact .cons_ok hn ihΓ (by simpa [term, context] using hx) ihA
  | var _ hx ih => exact .var ih (lookup hx)
  | univ hn _ ih => exact .univ hn ih
  | empty hn _ ih => exact .empty hn ih
  | unit hn _ ih => exact .unit hn ih
  | nats hn _ ih => exact .nats hn ih
  | zero _ ih => exact .zero ih
  | succ _ ih => exact .succ ih
  | pi hn _ _ ihA ihB => exact .pi hn ihA (by simpa [term, context] using ihB)
  | sigma hn _ _ ihA ihB => exact .sigma hn ihA (by simpa [term, context] using ihB)
  | id hn _ _ _ ihA iha ihb => exact .id hn ihA iha ihb
  | abs hn _ _ _ ihA ihB ihb => exact .abs hn ihA (by simpa [term, context] using ihB) (by simpa [term, context] using ihb)
  | app hn _ _ _ _ ihA ihB ihf iha =>
    simpa [term] using Ctx.JEqB.app hn ihA (by simpa [term, context] using ihB) ihf iha
  | pair hn _ _ _ _ ihA ihB iha ihb =>
    exact .pair hn ihA (by simpa [term, context] using ihB) iha (by simpa [term, context] using ihb)
  | fst hn _ _ _ ihA ihB ihp => exact .fst hn ihA (by simpa [term, context] using ihB) ihp
  | snd hn _ _ _ ihA ihB ihp =>
    simpa [term] using Ctx.JEqB.snd hn ihA (by simpa [term, context] using ihB) ihp
  | natrec hn _ _ _ _ ihC ihz ihs ihm =>
    simpa [term] using Ctx.JEqB.natrec hn (by simpa [term, context] using ihC) (by simpa [term, context] using ihz)
      (by simpa [term, context] using ihs) ihm
  | refl _ ih => exact .refl ih
  | absurd hn _ _ ihC ihe => exact .absurd hn ihC ihe
  | beta_app hn _ _ _ _ ihA ihB ihb iha =>
    simpa [term] using Ctx.JEqB.beta_app hn ihA (by simpa [term, context] using ihB) (by simpa [term, context] using ihb) iha
  | beta_fst hn _ _ _ _ ihA ihB iha ihb =>
    exact .beta_fst hn ihA (by simpa [term, context] using ihB) iha (by simpa [term, context] using ihb)
  | beta_snd hn _ _ _ _ ihA ihB iha ihb =>
    simpa [term] using Ctx.JEqB.beta_snd hn ihA (by simpa [term, context] using ihB) iha (by simpa [term, context] using ihb)
  | beta_natrec_zero hn _ _ _ ihC ihz ihs =>
    simpa [term] using Ctx.JEqB.beta_natrec_zero hn (by simpa [term, context] using ihC) (by simpa [term, context] using ihz)
      (by simpa [term, context] using ihs)
  | beta_natrec_succ hn _ _ _ _ ihC ihz ihs ihm =>
    simpa [term] using Ctx.JEqB.beta_natrec_succ hn (by simpa [term, context] using ihC) (by simpa [term, context] using ihz)
      (by simpa [term, context] using ihs) ihm
  | reflect _ _ _ iha ihb ihp => exact .reflect iha ihb ihp
  | id_uip _ _ _ iha ihb ihp => exact .id_uip iha ihb ihp
  | unit_ext _ ih => exact .unit_ext ih
  | pi_ext hn _ _ _ _ _ ihA ihB ihf ihg ihfg =>
    exact .pi_ext hn ihA (by simpa [term, context] using ihB) ihf ihg (by simpa [term, context] using ihfg)
  | sigma_ext hn _ _ _ _ _ _ ihA ihB ihp ihq ih1 ih2 =>
    exact .sigma_ext hn ihA (by simpa [term, context] using ihB) ihp ihq ih1 (by simpa [term, context] using ih2)
  | symm _ ih => exact .symm ih
  | trans _ _ ihab ihbc => exact .trans ihab ihbc
  | conv hn _ _ ihA iha => exact .conv hn ihA iha
  | cumul hn hmn _ ihA => exact .cumul hn hmn ihA


/-- The embedding preserves every universe occurrence, including erased annotations. -/
theorem term_universeBound {k : ℕ} (t : ETm k) : (term t).universeBound = t.universeBound := by
  induction t <;> simp_all only [term, Tm.universeBound, ETm.universeBound]

theorem context_universeBound (Γ : ECtx) : (context Γ).universeBound = Γ.universeBound := by
  induction Γ <;> simp_all only [context, Ctx.universeBound, ECtx.universeBound, term_universeBound]

theorem judgment_universeBound (j : EJdg) : (judgment j).universeBound = j.universeBound := by
  simp only [judgment, Jdg.universeBound, EJdg.universeBound, context_universeBound, term_universeBound]

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding
