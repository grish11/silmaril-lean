module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open Silmaril.Elgot.ITree
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Trees

variable {E : Type → Type} {X Y : Type 1}

theorem total_pure_proof (x : X) : Total (pure x : Tree E X) := .ret x

theorem total_bind_proof {t : Tree E X} {k : X → Tree E Y} (first : Total t) (rest : ∀ x, Total (k x)) :
    Total (t >>= k) := by
  induction first with
  | ret x => exact (pure_bind x k).symm ▸ rest x
  | vis e l _ ih => exact (vis_bind e l k).symm ▸ .vis e _ ih

/-- A tree without divergence is maximal for inclusion of observations. -/
theorem eq_of_total_traceLE_proof {t s : Tree E X} (total : Total t) (below : TraceLE t s) : t = s := by
  induction total generalizing s with
  | ret x =>
    have returned : out s = Part.some (.ret x) := below (.result x) (out_ret x)
    exact (out_injective (returned.trans (out_ret x).symm)).symm
  | vis e k _ ih =>
    obtain ⟨l, root⟩ := below (.request e) (hasTrace_vis_request e k)
    have shape : s = vis e l := out_injective (root.trans (out_vis e l).symm)
    subst shape
    exact congrArg (vis e) (funext fun reply => ih reply fun p seen =>
      (hasTrace_vis_exchange_iff e l reply p).mp (below _ ((hasTrace_vis_exchange_iff e k reply p).mpr seen)))

end Trees

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

theorem total_eval_proof (f : Φ) (x : Val (instrSrc f)) : Total ((model Φ).eval f x) := by
  rw [← bind_pure ((model Φ).eval f x), model_eval_bind]
  exact .vis _ _ fun reply => .ret _

set_option backward.isDefEq.respectTransparency false in
/-- Acyclic terms have no divergence at the free interpretation. -/
theorem total_denote_proof {n : Nat} {β : Context n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty Empty}
    (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Val β) :
    Total (d.denote Val (model Φ) (fun x => x.elim) ρ) := by
  induction d with
  | fv h => rename_i x _; exact x.elim
  | bv => exact total_pure_proof _
  | unit => exact total_pure_proof _
  | op ha ih => exact total_bind_proof (ih ρ) fun x => total_eval_proof _ x
  | let₁ ha hb iha ihb => exact total_bind_proof (iha ρ) fun x => ihb _
  | pair ha hb iha ihb =>
    exact total_bind_proof (iha ρ) fun x => total_bind_proof (ihb ρ) fun y => total_pure_proof _
  | let₂ ha hc iha ihc => exact total_bind_proof (iha ρ) fun x => ihc _
  | inl ha ih => exact total_bind_proof (ih ρ) fun x => total_pure_proof _
  | inr ha ih => exact total_bind_proof (ih ρ) fun x => total_pure_proof _
  | case he hl hr ihe ihl ihr =>
    refine total_bind_proof (ihe ρ) fun x => ?_
    cases x with
    | inl a => exact ihl _
    | inr b => exact ihr _
  | abort ha ih => exact total_bind_proof (ih ρ) fun x => nomatch x

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free
