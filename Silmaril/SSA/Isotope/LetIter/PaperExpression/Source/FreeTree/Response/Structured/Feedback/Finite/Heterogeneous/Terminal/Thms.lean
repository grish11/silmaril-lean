module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Reflection

/-! # Reflection after contracting terminal feedback -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasTypeEffect AbortEquiv)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic (repairedDenoteInSyntax)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S T B : Code}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

/-- Every surviving repeat enters a call row. -/
theorem Table.contract_guarded (M : Table F S B) : Guarded M.contract :=
  TerminalProofs.contract_guarded M

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

/-- Contract every repeat into an immediate return by native codiagonal and
fixpoint. The same initializer and the two rendered bodies retain the
supplied iterative effect bound. -/
theorem Table.contract_eq (M : Table F S B) (s : S.Value) (hf : ∀ f : Ops, instrEff f ≤ e)
    (he : IsIterative e) {a : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (hb' : M.contract.source.toLetIter 1 = some b') :
    HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a b') B.ty :=
  TerminalProofs.contract_eq M s hf he ha hb hb'

/-- Contraction preserves the table observations by native soundness. -/
theorem Table.contract_run (M : Table F S B) (s : S.Value) (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (hf : ∀ f : Ops, instrEff f ≤ e) :
    M.run s = M.contract.run s :=
  TerminalProofs.contract_run M s P visible hf

namespace Terminal

variable {L : Table F S B} {R : Table F T B} {s : S.Value} {t : T.Value}

/-- Reflect weak observation equality for all rendered heterogeneous tables.
Contract terminal targets before replaying the two cover projections. -/
theorem replay_of_run_eq (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f)
    (obs : L.run s = R.run t) (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s).toLetIter 0 = some a ∧ (T.literal t).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty :=
  TerminalProofs.replay_full P visible obs hf he

/-- Original table run equality characterizes repaired packed equality. -/
theorem packed_eq_iff_run_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      L.run s = R.run t :=
  TerminalProofs.packed_eq_iff_full ha hb ha' hb' da db da' db' P visible hf he

/-- Compare the actual weak denotations of the original lowered loops. -/
theorem packed_eq_iff_rendered_denote_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      (da.iter db).denote D (instructions carriers P) γ ρ₀ =
      (da'.iter db').denote D (instructions carriers P) γ ρ₀ := by
  rw [loop_denote P visible L hf s ha hb da db, loop_denote P visible R hf t ha' hb' da' db']
  exact packed_eq_iff_run_eq ha hb ha' hb' da db da' db' P visible hf he

end Terminal

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
