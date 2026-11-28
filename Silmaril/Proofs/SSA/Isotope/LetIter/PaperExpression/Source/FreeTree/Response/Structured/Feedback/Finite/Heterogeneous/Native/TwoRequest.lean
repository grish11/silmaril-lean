module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.TwoRequest.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Reflection
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Decision
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Normalize

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasTypeEffect AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.TwoRequest.Proofs

variable {n : Nat} {F : Family n} {S T B : Code}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "Control" => Code.sum B S

private theorem row_subst {a : Expr Ops} (r : RowSyntax F S B a) (σ : Nat → Expr Ops) :
    a.subst σ = a := by
  cases r with
  | one r => exact Native.Proofs.row_subst r σ
  | two f v d =>
    simp only [Expr.subst, Native.Proofs.closed_subst v,
      Native.Proofs.decision_subst d Native.Proofs.row_subst (Expr.liftSubst σ) rfl]

private theorem plan_subst (p : Plan F S B) (σ : Nat → Expr Ops) : p.source.subst σ = p.source := by
  cases p with
  | one r => exact r.source_subst σ
  | two f x k =>
    simp only [Plan.source, Expr.subst, literal_subst,
      dispatch_subst f.replyCode (fun v => (k v).source_subst) (Expr.liftSubst σ), Expr.liftSubst]

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {e : ε}

local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))
local notation "Δ₀" => ([] : EffectCtx (Ty Unit) ε)

private theorem row_wf {a : Expr Ops} (r : RowSyntax F S B a) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf Γ a (Control).ty e := by
  cases r with
  | one r => exact Native.Proofs.row_wf r hf
  | two f v d =>
    exact .let₁ (.op (hf f) (Native.Proofs.closed_wf v))
      (Native.Proofs.decision_wf d (fun r => Native.Proofs.row_wf r hf))

private theorem plan_wf (p : Plan F S B) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf Γ p.source (Control).ty e := by
  cases p with
  | one r => exact r.source_wf hf
  | two f x k =>
    exact .let₁ (.op (hf f) (literal_wf f.argCode x))
      (dispatch_wf f.replyCode (fun v => (k v).source_wf hf) (.var 0 bot_le))

theorem row_eqv {a : Expr Ops} (r : RowSyntax F S B a) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv Δ₀ (Control).ty e a r.read.source := by
  cases r with
  | one r => exact r.eqv_render hf
  | two f v d =>
    exact .let1 (.op (hf f) (Native.Proofs.closed_eqv v))
      (Native.Proofs.decision_eqv d Native.Proofs.row_subst (fun r => Native.Proofs.row_wf r hf)
        (fun w => (d.read w).2.read.source) (fun w => (d.read w).2.read.source_subst)
        (fun w => (d.read w).2.read.source_wf hf) (fun w => (d.read w).2.eqv_render hf))

variable [EffectIteration ε]

theorem program_typed (p : Program F S B e) :
    HasTypeEffect Free .nil p.native B.ty e := by
  have a : Wf Δ₀ p.initial S.ty e := Native.Proofs.closed_wf p.initialSyntax
  obtain ⟨_, ha, ta⟩ := a.toLetIter
  obtain ⟨_, hb, tb⟩ := (Native.Proofs.decision_wf (Γ := Δ₀) p.bodySyntax (fun r => row_wf r p.effects)).toLetIter
  exact .iter p.iterative (Option.some.inj (ha.symm.trans p.initial_lowers) ▸ ta)
    (Option.some.inj (hb.symm.trans p.body_lowers) ▸ tb)

theorem lower_expansion (p : Program F S B e) :
    Native.Proofs.Renders p.table p.start p.native e := by
  have initial : Eqv Δ₀ S.ty e p.initial (S.literal p.initialSyntax.read) :=
    Native.Proofs.closed_eqv p.initialSyntax
  have body : Eqv [slot[S]] (Control).ty e p.body p.plans.source :=
    Native.Proofs.decision_eqv p.bodySyntax row_subst (fun r => row_wf r p.effects)
      (fun v => (p.plans v).source) (fun v => plan_subst (p.plans v))
      (fun v => plan_wf (p.plans v) p.effects) (fun v => row_eqv (p.bodySyntax.read v).2 p.effects)
  obtain ⟨a, ha, _⟩ := initial.endpoints_wf.2.toLetIter
  obtain ⟨b, hb, _⟩ := body.endpoints_wf.2.toLetIter
  have widen : Wf Δ₀ (p.plans.stateCode.literal p.start : Expr Ops) p.plans.stateCode.ty e :=
    literal_wf p.plans.stateCode p.start
  obtain ⟨a', ha', ta'⟩ := widen.toLetIter
  obtain ⟨b', hb', tb'⟩ := (p.table.step_wf p.effects).toLetIter
  have normal : AbortEquiv (⊥ : ε) Free .nil p.native (.iter a b) B.ty :=
    .iter (initial.toLetIter p.initial_lowers ha) (body.toLetIter p.body_lowers hb)
  unfold Native.Proofs.Renders
  exact ⟨a', b', ha', hb', ta', tb', normal.trans (p.plans.expand_eq p.initialSyntax.read ha hb ha' hb')⟩

local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

theorem denote_eq_run (p : Program F S B e) (d : Derivation Ops Free .nil p.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    d.denote D (instructions carriers P) γ ρ₀ = p.table.run p.start :=
  Native.Proofs.renders_denote (lower_expansion p) d P visible p.effects

theorem abortEquiv_iff_denote_eq (p : Program F S B e) (q : Program F T B e)
    (dp : Derivation Ops Free .nil p.native B.ty) (dq : Derivation Ops Free .nil q.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    AbortEquiv (⊥ : ε) Free .nil p.native q.native B.ty ↔
      dp.denote D (instructions carriers P) γ ρ₀ = dq.denote D (instructions carriers P) γ ρ₀ := by
  refine ⟨fun eq => sound carriers P eq dp dq ρ₀, fun obs => ?_⟩
  rw [denote_eq_run p dp P visible, denote_eq_run q dq P visible] at obs
  exact Native.Proofs.renders_reflect (lower_expansion p) (lower_expansion q) P visible p.effects p.iterative obs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.TwoRequest.Proofs
