module

public import Silmaril.Logic.TypeTheory.LambdaPi.Encoding.Thms

@[expose] public section

/-!
# An optional η-extensional λΠ profile

η is represented by one scoped rewrite schema, using separate variables for
the domain annotation and function. The default LF profile stays β-only.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- `λ x : A, f x → f`, with `f` shifted beneath the binder to avoid capture. -/
def etaRule : RewriteRule where
  arity := 2
  lhs := .lam (.var 0) (.app (.var 2) (.var 0))
  rhs := .var 1
  lhs_scoped := by change 0 < 2 ∧ 2 < 3 ∧ 0 < 3; decide
  rhs_scoped := by change 1 < 2; decide

/-- Add η as a user rewrite schema, retaining every declaration and existing rule. -/
def Calculus.withEta (C : Calculus) : Calculus where
  declared := C.declared
  rules := C.rules ∪ {etaRule}

/-- A separately named βη profile; `Calculus.lf` remains the β-only profile. -/
def Calculus.lfBetaEta (declared : String → Term → Prop) : Calculus :=
  (Calculus.lf declared).withEta

/-- Annotated raw βη convertibility, independently stated without rewrite schemas. -/
inductive BetaEtaConversion : Term → Term → Prop where
  | refl (t) : BetaEtaConversion t t
  | symm {t u} : BetaEtaConversion t u → BetaEtaConversion u t
  | trans {t u v} : BetaEtaConversion t u → BetaEtaConversion u v → BetaEtaConversion t v
  | beta (A b a) : BetaEtaConversion (.app (.lam A b) a) (b.substOne a)
  | eta (A f) : BetaEtaConversion (.lam A (.app (f.rename Nat.succ) (.var 0))) f
  | app {f g a b} : BetaEtaConversion f g → BetaEtaConversion a b →
      BetaEtaConversion (.app f a) (.app g b)
  | lam {A B t u} : BetaEtaConversion A B → BetaEtaConversion t u →
      BetaEtaConversion (.lam A t) (.lam B u)
  | pi {A B t u} : BetaEtaConversion A B → BetaEtaConversion t u →
      BetaEtaConversion (.pi A t) (.pi B u)

/-- Every existing presentation includes structurally into its η extension. -/
def Calculus.includeEta (C : Calculus) : Morphism C C.withEta where
  constants := id
  declared := by
    intro c A hd
    change C.declared c (A.mapConstants id)
    simpa only [Silmaril.Proofs.Logic.TypeTheory.LambdaPi.map_id] using hd
  rules r hr := by
    change r.mapConstants id ∈ C.rules ∪ {etaRule}
    simpa only [Silmaril.Proofs.Logic.TypeTheory.LambdaPi.rule_map_id] using
      (Set.mem_union_left {etaRule} hr)

end Silmaril.Logic.TypeTheory.LambdaPi
