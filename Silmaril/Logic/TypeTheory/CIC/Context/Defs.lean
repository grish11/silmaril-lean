module

public import Silmaril.Logic.TypeTheory.CIC.Reduction.Defs

@[expose] public section

/-! # CIC dependent contexts and telescope instances -/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Substitute in an oldest-first telescope, at each declaration's preceding scope. -/
def Context.substTelescope (terms : List Expr) (cutoff : ℕ) (Δ : Context) : Context :=
  Δ.mapIdx fun i d => d.mapTerms (Term.subst terms (cutoff + i))

def Context.lift (amount cutoff : ℕ) (Γ : Context) : Context :=
  Γ.mapAt fun i => Term.lift amount (i + cutoff)

/-- Abstract newest-first assumptions as products and local definitions as lets. -/
def Context.abstractProducts (Γ : Context) (t : Expr) : Expr :=
  Γ.foldl (fun body d => match d.value with
    | none => .prod d.binder d.type body
    | some value => .letIn d.binder value d.type body) t

/-- Abstract newest-first assumptions as lambdas and local definitions as lets. -/
def Context.abstractLambdas (Γ : Context) (t : Expr) : Expr :=
  Γ.foldl (fun body d => match d.value with
    | none => .lam d.binder d.type body
    | some value => .letIn d.binder value d.type body) t

/-- References to assumptions in application order; definitions occupy no arguments. -/
def Context.extendedList : Context → ℕ → List Expr
  | [], _ => []
  | d :: Γ, cutoff =>
      match d.value with
      | none => Context.extendedList Γ (cutoff + 1) ++ [.rel cutoff]
      | some _ => Context.extendedList Γ (cutoff + 1)

/-- Remove definitions from a context, substituting them into its more recent entries. -/
def Context.smash (acc : Context) : Context → Context
  | [] => acc
  | d :: Γ =>
      match d.value with
      | none => smash (acc ++ [d]) Γ
      | some value => smash (Context.subst [value] 0 acc) Γ

/-- Expand one context's definitions underneath a fixed number of additional binders. -/
def Context.expandLetsAt (Γ : Context) (cutoff : ℕ) (t : Expr) : Expr :=
  (t.lift Γ.assumptionCount (cutoff + Γ.length)).subst (Γ.extendedSubst 0) cutoff

/-- Expand one context's definitions in a dependent context. -/
def Context.expandLetsContext (Γ : Context) (cutoff : ℕ) (Δ : Context) : Context :=
  Context.subst (Γ.extendedSubst 0) cutoff
    (Context.lift Γ.assumptionCount (cutoff + Γ.length) Δ)

/-- The abstract instance of a polymorphic declaration consists of its local parameters. -/
def UniverseDeclaration.abstractInstance : UniverseDeclaration → List Universe
  | .monomorphic _ => []
  | .polymorphic count _ => (List.range count).map fun i => .level (.parameter i)

/-- Mutual arities are declared newest-first and have the relevance of Type. -/
def MutualInductiveBody.aritiesContext (block : MutualInductiveBody) : Context :=
  (block.bodies.map fun body =>
    { binder := { name := some body.name }, type := body.type }).reverse

/-- Substitute global inductive references for the locally bound mutual-block names. -/
def inductiveSubstitution (block : String) (ui : List Universe)
    (bodies : List InductiveBody) : List Expr :=
  (List.range bodies.length).reverse.map fun i => .inductiveType ⟨block, i⟩ ui

end Silmaril.Logic.TypeTheory.CIC
