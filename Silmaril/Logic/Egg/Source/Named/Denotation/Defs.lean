module

public import Silmaril.Logic.Egg.Source.Named.Syntax.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named

abbrev Valuation {D : Declarations} (M : Core.Model D.signature)
    (Γ : CheckedContext D) := ∀ i, M.carrier (Γ.profile i)

/-- Direct interpretation of names and annotations. Neither resolution nor any
compiled term appears in the definition. Every algebra, including empty sorts
and nonfree operations, is allowed. -/
inductive RawTerm.Denotes {D : Declarations} (M : Core.Model D.signature)
    (Γ : CheckedContext D) (ρ : Valuation M Γ) : RawTerm →
      (s : D.checked.LocalSort) → M.carrier s → Prop where
  | var (i : Fin Γ.bindings.length) (name : String)
      (named : (Γ.bindings.get i).name = name) :
      Denotes M Γ ρ (.var name) (Γ.profile i) (ρ i)
  | app {n : Nat} {w : Fin n → D.checked.LocalSort} {s : D.checked.LocalSort}
      (o : D.signature.Op n w s) (name result : String)
      (named : o.val.name = name) (annotated : s.val = result)
      (arguments : Fin n → RawTerm) (values : ∀ i, M.carrier (w i))
      (denotes : ∀ i, Denotes M Γ ρ (arguments i) (w i) (values i)) :
      Denotes M Γ ρ (.app name result n arguments) s (M.op o values)

def RawEquality.Holds {D : Declarations} (M : Core.Model D.signature)
    (Γ : CheckedContext D) (ρ : Valuation M Γ) (e : RawEquality) : Prop :=
  ∃ (s : D.checked.LocalSort) (x y : M.carrier s),
    e.left.Denotes M Γ ρ s x ∧ e.right.Denotes M Γ ρ s y ∧ x = y

/-- Quantification is over the full source context, never just occurring names. -/
def RawRule.Holds {D : Declarations} (M : Core.Model D.signature) (r : RawRule) : Prop :=
  ∃ Γ : CheckedContext D, Γ.bindings = r.context ∧
    ∀ ρ : Valuation M Γ, (∀ e ∈ r.guards, e.Holds M Γ ρ) → r.conclusion.Holds M Γ ρ

/-- All rules in all files use one shared algebra. -/
def RawProgram.Holds {D : Declarations} (M : Core.Model D.signature)
    (p : RawProgram) : Prop := ∀ r ∈ p, r.Holds M

end Silmaril.Logic.Egg.Source.Named
