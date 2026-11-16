module

public import Silmaril.Logic.Egglog.Source.Named.Declarations.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named

/-- A finite dependent assignment to precisely the explicit source binders.
It imposes no inhabitants at sorts absent from the context. -/
abbrev Valuation {D : Declarations} (M : Core.Model D.signature)
    (Γ : CheckedContext D) := ∀ i, M.carrier (Γ.profile i)

/-- Independent relational meaning of named terms. This definition never calls
resolution, compiled term evaluation, or a byte decoder. -/
inductive RawTerm.Denotes {D : Declarations} (M : Core.Model D.signature)
    (Γ : CheckedContext D) (ρ : Valuation M Γ) : RawTerm →
      (s : D.LocalSort) → M.carrier s → Prop where
  | var (i : Fin Γ.bindings.length) (name : String)
      (named : (Γ.bindings.get i).name = name) :
      Denotes M Γ ρ (.var name) (Γ.profile i) (ρ i)
  | app {n : Nat} {w : Fin n → D.LocalSort} {s : D.LocalSort}
      (o : D.signature.Op n w s) (name : String)
      (named : o.val.name = name) (arguments : Fin n → RawTerm)
      (values : ∀ i, M.carrier (w i))
      (denotes : ∀ i, Denotes M Γ ρ (arguments i) (w i) (values i)) :
      Denotes M Γ ρ (.app name n arguments) s (M.op o values)

/-- Rows remain genuinely partial. Equality and predicates are interpreted in
the same model as every other atom, with every ordered argument retained. -/
def RawAtom.Holds {D : Declarations} (M : Core.Model D.signature)
    (Γ : CheckedContext D) (ρ : Valuation M Γ) : RawAtom → Prop
  | .equal left right => ∃ (s : D.LocalSort) (x y : M.carrier s),
      left.Denotes M Γ ρ s x ∧ right.Denotes M Γ ρ s y ∧ x = y
  | .relation name n arguments =>
      ∃ (w : Fin n → D.LocalSort) (r : D.signature.Rel n w)
        (values : ∀ i, M.carrier (w i)), r.val.name = name ∧
          (∀ i, (arguments i).Denotes M Γ ρ (w i) (values i)) ∧ M.rel r values
  | .row name n arguments value =>
      ∃ (w : Fin n → D.LocalSort) (s : D.LocalSort) (f : D.signature.Function n w s)
        (values : ∀ i, M.carrier (w i)) (output : M.carrier s),
          f.val.name = name ∧
          (∀ i, (arguments i).Denotes M Γ ρ (w i) (values i)) ∧
          value.Denotes M Γ ρ s output ∧ M.row f values output

/-- Rules universally quantify over the complete context; a query uses one
shared existential assignment for all goals. Invalid contexts have no meaning. -/
def RawSentence.Holds {D : Declarations} (M : Core.Model D.signature) :
    RawSentence → Prop
  | .rule context body head => ∃ Γ : CheckedContext D, Γ.bindings = context ∧
      ∀ ρ : Valuation M Γ, (∀ a ∈ body, a.Holds M Γ ρ) → head.Holds M Γ ρ
  | .query context goals => ∃ Γ : CheckedContext D, Γ.bindings = context ∧
      ∃ ρ : Valuation M Γ, ∀ a ∈ goals, a.Holds M Γ ρ

/-- Independent ambient meaning uses the actual vocabulary interpretation. -/
def RawSentence.HoldsIn {S : Core.Signature} (view : NameView S)
    (M : Core.Model S) (sentence : RawSentence) : Prop :=
  sentence.Holds ((Core.Model.reduct view.symbols).obj M)

/-- Every entry of a complete program is interpreted in one shared model. -/
def ProgramHolds {D : Declarations} (M : Core.Model D.signature)
    (sentences : List RawSentence) : Prop :=
  ∀ sentence ∈ sentences, sentence.Holds M

end Silmaril.Logic.Egglog.Source.Named
