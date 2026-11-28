module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseOperand

/-! # Term case separation under checked default observation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing

universe u
variable {Φ : Type u} [HasTy Φ (Ty Empty)]

/-- A default-Paper observer marks term cases in operands and otherwise
supplies the given closed, typed left reply. It still validates the
standalone returned-call sequencing step. -/
theorem term_case_operand_ne {reply q v a b c : Tm Φ} {p : Φ} {l r s : Region Φ}
    {A B : Ty Empty} {L : List (Ty Empty)} {i : Nat}
    (reply_typed : ∀ (f : Φ), Tm.BranchValue [] (.inl reply) (instrTrg f : Ty Empty))
    (payload : Tm.BranchValue [] reply A)
    (query : Tm.BranchValue [(Ty.unit : Ty Empty)] q (instrSrc p))
    (ret : Tm.BranchValue [A, Ty.unit] v B) :
    ¬ Paper.Extension.Eqv Paper.WithComputedCallReturns.Step [Ty.unit] (.case (.op p (.case a b c)) l r)
      (.case (.op p q) (.br i v) s) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.term_case_operand_ne
    reply_typed payload query ret

/-- The exact unit-return instance of region let₁-case is distinguishable
in any extension whose seeds change only operands at typed primitive call sites. -/
theorem unit_case_return_ne_of_call_sites
    {Seed : VCtx (Ty Empty) → Region Φ → Region Φ → LCtx (Ty Empty) → Prop}
    (sites : ∀ {Γ L r s}, Seed Γ r s L →
      (∃ (p : Φ) (a b : Tm Φ) (k : Region Φ), r = .let₁ (.op p a) k ∧ s = .let₁ (.op p b) k) ∨
      (∃ (p : Φ) (a b : Tm Φ) (l k : Region Φ), r = .case (.op p a) l k ∧ s = .case (.op p b) l k)) :
    ¬ Paper.Extension.Eqv Seed [Ty.coprod Ty.unit Ty.unit]
      (.let₁ (.case (.var 0) .unit .unit) (.br 0 (.var 0)))
      (.case (.var 0) (.let₁ .unit (.br 0 (.var 0))) (.let₁ .unit (.br 0 (.var 0)))) [Ty.unit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.unit_case_return_ne_of_call_sites
    sites

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing
