module

public import Silmaril.Logic.TypeTheory.CIC.Syntax.Defs

@[expose] public section

/-! # PCUIC universe substitution on raw terms

Unlike a structural change of the universe-name type, PCUIC universe-instance
substitution keeps declaration-context metadata unchanged. Case universe
instances, parameters, return types and branch bodies are substituted.
-/

namespace Silmaril.Logic.TypeTheory.CIC.Term

universe u

/-- Same-name-type universe substitution, preserving case declaration metadata. -/
def substUniverses {Level : Type u} (σ : Level → UniverseExpr Level) :
    Term Level → Term Level
  | .rel i => .rel i
  | .free x => .free x
  | .sort s => .sort (s.map (UniverseExpr.subst σ))
  | .prod na A B => .prod na (substUniverses σ A) (substUniverses σ B)
  | .lam na A b => .lam na (substUniverses σ A) (substUniverses σ b)
  | .letIn na a A b => .letIn na (substUniverses σ a) (substUniverses σ A) (substUniverses σ b)
  | .app f a => .app (substUniverses σ f) (substUniverses σ a)
  | .constant c ui => .constant c (ui.map (UniverseExpr.subst σ))
  | .inductiveType i ui => .inductiveType i (ui.map (UniverseExpr.subst σ))
  | .constructor i c ui => .constructor i c (ui.map (UniverseExpr.subst σ))
  | .caseOf ci p c brs =>
      .caseOf ci
        { p with
          parameters := p.parameters.map (fun a => substUniverses σ a)
          universeInstance := p.universeInstance.map (UniverseExpr.subst σ)
          returnType := substUniverses σ p.returnType }
        (substUniverses σ c)
        (brs.map fun b => { b with body := substUniverses σ b.body })
  | .projection p c => .projection p (substUniverses σ c)
  | .fix ds i =>
      .fix (ds.map fun d => { d with
        type := substUniverses σ d.type
        body := substUniverses σ d.body }) i
  | .cofix ds i =>
      .cofix (ds.map fun d => { d with
        type := substUniverses σ d.type
        body := substUniverses σ d.body }) i
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    first
    | have h := List.sizeOf_lt_of_mem (by assumption)
      try cases p
      try cases b
      try cases d
      simp_all only [Predicate.mk.sizeOf_spec, Branch.mk.sizeOf_spec, FixDef.mk.sizeOf_spec]
      omega
    | cases p
      simp only [Predicate.mk.sizeOf_spec]
      omega

end Silmaril.Logic.TypeTheory.CIC.Term
