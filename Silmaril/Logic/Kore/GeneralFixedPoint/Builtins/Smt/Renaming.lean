module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Thms

/-! Names can be identified: no injectivity premise is needed for free-variable
renaming. This is typed semantic renaming, not a claim about rewriting raw bytes. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Smt

def Pattern.rename (f : ValueSort → String → String) : {s : ValueSort} → Pattern s → Pattern s
  | _, .variable s name => .variable s (f s name)
  | _, .integer n => .integer n
  | _, .boolean b => .boolean b
  | _, .top s => .top s
  | _, .bottom s => .bottom s
  | _, .neg p => .neg (p.rename f)
  | _, .conj p q => .conj (p.rename f) (q.rename f)
  | _, .disj p q => .disj (p.rename f) (q.rename f)
  | _, .intEq p q => .intEq (p.rename f) (q.rename f)
  | _, .boolNot p => .boolNot (p.rename f)

theorem rename_denote (f : ValueSort → String → String) (v : Valuation)
    {s : ValueSort} (p : Pattern s) :
    (p.rename f).denote v = p.denote (fun s name => v s (f s name)) := by
  induction p <;> simp_all [Pattern.rename, Pattern.denote]

theorem renamed_compile_correct (f : ValueSort → String → String) (v : Valuation)
    {s : ValueSort} (p : Pattern s) {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
    (values : ∀ i, (target v).carriers.value (Γ i))
    (out : Uflia.Quantified.Term signature Γ s.code) :
    Uflia.Quantified.Formula.Holds ((p.rename f).compile out) (target v) values ↔
      Uflia.Quantified.eval (target v) values out ∈
        p.denote (fun s name => v s (f s name)) := by
  rw [compile_correct, rename_denote]

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
