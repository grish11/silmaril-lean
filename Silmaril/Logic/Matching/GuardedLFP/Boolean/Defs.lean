module

public import Silmaril.Logic.FirstOrderLFP.Boolean.Thms
public import Silmaril.Logic.Matching.GuardedLFP.Institution
public import Silmaril.Logic.Matching.FixedPoint.Dual.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

/-- Negative free predicates are interpreted by complement after restricting
raw native sets to genuine encoded tuples. Inactive padding is allowed. -/
def restrictEnv (M : Model S) {r : Nat} {P : Fin r → Profile S}
    (σ : Fin r → Bool)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    FirstOrderLFP.RelEnv (decode M) P :=
  fun i => if σ i then GuardedLFP.restrictEnv M η i else (GuardedLFP.restrictEnv M η i)ᶜ

/-- Signed Boolean source recursion becomes native tuple-valued μ. The recursive body
binds precisely the tuple prefix; Γ remains the captured parameter context. -/
def formula {S : FOL.Signature} : {r k : Nat} → {P : Fin r → Profile S} →
    {Γ : Fin k → S.S} → {σ : Fin r → Bool} → FirstOrderLFP.Boolean.Formula S P Γ σ →
    FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Γ) (.base .truth)
  | _, _, _, _, _, .base p => .base ((baseSignature S).pattern (GuardedFOL.formula p))
  | _, _, _, _, _, .pred i _positive args => tupleDefined (.conj (packTerms args) (.setvar i))
  | _, _, _, _, _, .neg p => (formula p).dual
  | _, _, _, _, _, .conj p q => .conj (formula p) (formula q)
  | _, _, _, _, _, .disj p q => .disj (formula p) (formula q)
  | _, _, _, _, _, @FirstOrderLFP.Boolean.Formula.all _ _ _ _ _ Δ p =>
      .all (objSort (Δ 0)) ((context_extend Δ) ▸
        .disj (.base ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ)))) (formula p))
  | _, _, _, _, _, @FirstOrderLFP.Boolean.Formula.ex _ _ _ _ _ Δ p =>
      .ex (objSort (Δ 0)) ((context_extend Δ) ▸
        .conj (.base ((baseSignature S).pattern (GuardedFOL.activeGuard Δ))) (formula p))
  | _, _, _, _Γ, _σ, @FirstOrderLFP.Boolean.Formula.lfp _ _ _ P' _ _ _Δ ht hp body args =>
      tupleDefined (.conj (packTerms args) (.mu (tupleBody ht hp (formula body))))
end Silmaril.Logic.Matching.GuardedLFP.Boolean
