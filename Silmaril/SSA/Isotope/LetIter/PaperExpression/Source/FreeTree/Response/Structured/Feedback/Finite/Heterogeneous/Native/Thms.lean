module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Normalize
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Reflection

/-! # Native reflection by extracting finite feedback tables -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect Tm Derivation AbortEquiv)
open Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic (Term)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
  (repairedDenoteInSyntax repairedDenoteInSyntax_eq_iff)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source (Eqv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native

variable {n : Nat} {F : Family n} {S T B : Code} {ε : Type}
  [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε] {e : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

/-- Extract a row and prove its renderer equation at the supplied bound. -/
theorem RowSyntax.eqv_render {a : Expr Ops} (r : RowSyntax F S B a) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B S).ty e a r.read.source :=
  Proofs.row_eqv r hf

variable [EffectIteration ε]

/-- The actual lowered endpoint has its declared exact result and effect. -/
theorem Program.typed (p : Program F S B e) : HasTypeEffect Free .nil p.native B.ty e :=
  Proofs.program_typed p

/-- The admitted native program as an endpoint in the fixed typing fiber. -/
@[expose] def Program.endpoint (p : Program F S B e) : Term Ops Free .nil B.ty e :=
  ⟨p.native, p.typed⟩

/-- The rerendered extraction lowers at the same bound. The native equation
is obtained from source constructor beta, let beta, and congruence. -/
theorem Program.lower_rendering (p : Program F S B e) :
    ∃ (a : Tm Empty Ops 0) (b : Tm Empty Ops 1),
      (S.literal p.start).toLetIter 0 = some a ∧ p.table.source.toLetIter 1 = some b ∧
      HasTypeEffect Free .nil a S.ty e ∧ HasTypeEffect Free (.snoc .nil S.ty) b (Code.sum B S).ty e ∧
      AbortEquiv (⊥ : ε) Free .nil p.native (.iter a b) B.ty :=
  Proofs.lower_rendering p

/-- Interpret the actual native term using the extracted table. -/
theorem Program.denote_eq_run (p : Program F S B e) (d : Derivation Ops Free .nil p.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    d.denote D (instructions carriers P) γ ρ₀ = p.table.run p.start :=
  Proofs.denote_eq_run p d P visible

/-- Reflection at the common supplied effect bound, using the extracted
table runs and the native equations to the renderings. -/
theorem Program.abortEquiv_iff_run_eq (p : Program F S B e) (q : Program F T B e)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    AbortEquiv (⊥ : ε) Free .nil p.native q.native B.ty ↔ p.table.run p.start = q.table.run q.start :=
  Proofs.abortEquiv_iff_run_eq p q P visible

/-- Compare the actual weak denotations of independently written native loops. -/
theorem Program.abortEquiv_iff_denote_eq (p : Program F S B e) (q : Program F T B e)
    (dp : Derivation Ops Free .nil p.native B.ty) (dq : Derivation Ops Free .nil q.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    AbortEquiv (⊥ : ε) Free .nil p.native q.native B.ty ↔
      dp.denote D (instructions carriers P) γ ρ₀ = dq.denote D (instructions carriers P) γ ρ₀ := by
  rw [p.denote_eq_run dp P visible, q.denote_eq_run dq P visible]
  exact p.abortEquiv_iff_run_eq q P visible

/-- Repaired packed equality of the actual endpoints coincides with their
weak denotation equality in this fragment. -/
theorem Program.packed_eq_iff_denote_eq (p : Program F S B e) (q : Program F T B e)
    (dp : Derivation Ops Free .nil p.native B.ty) (dq : Derivation Ops Free .nil q.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    repairedDenoteInSyntax (⊥ : ε) dp = repairedDenoteInSyntax (⊥ : ε) dq ↔
      dp.denote D (instructions carriers P) γ ρ₀ = dq.denote D (instructions carriers P) γ ρ₀ :=
  (repairedDenoteInSyntax_eq_iff (⊥ : ε) dp dq).trans (p.abortEquiv_iff_denote_eq q dp dq P visible)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native
