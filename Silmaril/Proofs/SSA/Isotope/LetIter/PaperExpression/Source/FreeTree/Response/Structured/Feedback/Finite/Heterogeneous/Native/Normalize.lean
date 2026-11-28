module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Decision
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect Tm AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs

variable {n : Nat} {F : Family n} {S B : Code}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "Control" => (Code.sum B S)

theorem row_subst {a : Expr Ops} (r : RowSyntax F S B a) (σ : Nat → Expr Ops) :
    a.subst σ = a := by
  cases r with
  | ret v => simp only [Expr.subst, closed_subst v]
  | call f v d => simp only [Expr.subst, closed_subst v, decision_subst d closed_subst (Expr.liftSubst σ) rfl]

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {e : ε}

local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))
local notation "Δ₀" => ([] : EffectCtx (Ty Unit) ε)

theorem row_wf {a : Expr Ops} (r : RowSyntax F S B a) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf Γ a (Control).ty e := by
  cases r with
  | ret v => exact .inl (closed_wf v)
  | call f v d => exact .let₁ (.op (hf f) (closed_wf v)) (decision_wf d closed_wf)

theorem row_eqv {a : Expr Ops} (r : RowSyntax F S B a) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv Δ₀ (Control).ty e a r.read.source := by
  cases r with
  | ret v => exact .inl (closed_eqv v)
  | call f v d =>
    exact .let1 (.op (hf f) (closed_eqv v))
      (decision_eqv d closed_subst closed_wf (fun w => (Control).literal (d.read w).2.read)
        (fun _ => literal_subst _ _) (fun _ => literal_wf _ _) (fun w => closed_eqv (d.read w).2))

variable [EffectIteration ε]

theorem program_typed (p : Program F S B e) :
    HasTypeEffect Free .nil p.native B.ty e := by
  have a : Wf Δ₀ p.initial S.ty e := closed_wf p.initialSyntax
  obtain ⟨_, ha, ta⟩ := a.toLetIter
  obtain ⟨_, hb, tb⟩ := (decision_wf (Γ := Δ₀) p.bodySyntax (fun r => row_wf r p.effects)).toLetIter
  exact .iter p.iterative (Option.some.inj (ha.symm.trans p.initial_lowers) ▸ ta)
    (Option.some.inj (hb.symm.trans p.body_lowers) ▸ tb)

/-- Derive the native equation using source beta and constructor decisions
before any observations are compared. -/
theorem lower_rendering (p : Program F S B e) :
    ∃ (a : Tm Empty Ops 0) (b : Tm Empty Ops 1),
      (S.literal p.start).toLetIter 0 = some a ∧ p.table.source.toLetIter 1 = some b ∧
      HasTypeEffect Free .nil a S.ty e ∧ HasTypeEffect Free (.snoc .nil S.ty) b (Control).ty e ∧
      AbortEquiv (⊥ : ε) Free .nil p.native (.iter a b) B.ty := by
  have initial : Eqv Δ₀ S.ty e p.initial (S.literal p.start) := closed_eqv p.initialSyntax
  have body : Eqv [slot[S]] (Control).ty e p.body p.table.source :=
    decision_eqv p.bodySyntax row_subst (fun r => row_wf r p.effects)
      (fun v => ((p.bodySyntax.read v).2.read).source)
      (fun v => ((p.bodySyntax.read v).2.read).source_subst)
      (fun v => ((p.bodySyntax.read v).2.read).source_wf p.effects)
      (fun v => row_eqv (p.bodySyntax.read v).2 p.effects)
  obtain ⟨a, ha, ta⟩ := initial.endpoints_wf.2.toLetIter
  obtain ⟨b, hb, tb⟩ := body.endpoints_wf.2.toLetIter
  exact ⟨a, b, ha, hb, ta, tb,
    .iter (initial.toLetIter p.initial_lowers ha) (body.toLetIter p.body_lowers hb)⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs
