module

public import Silmaril.Calculi.LambdaCube.PER.PTSMorphism

@[expose] public section

/-!
# The λΠ calculus with explicit rewrite schemas

The raw binding syntax and capture-avoiding operations are reused from the
public lambda-cube library. Atoms distinguish `Type`, `Kind` and global
constants; constants are never affected by variable substitution. Rewrite
schemas carry an explicit number of free variables.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi

open Silmaril.Calculi.LambdaCube

/-- The two sorts of the λΠ calculus. `Kind` has no sort axiom. -/
inductive SortTag where
  | type
  | kind
  deriving DecidableEq

/-- Sorts and global constants share the atom position in the reused raw syntax. -/
inductive Atom where
  | sort : SortTag → Atom
  | constant : String → Atom
  deriving DecidableEq

/-- De Bruijn terms with explicit abstraction domains. -/
abbrev Term := Pseudo Atom

namespace Term

/-- A sort term. -/
abbrev univ (s : SortTag) : Term := Pseudo.sort (.sort s)

/-- A global constant. -/
abbrev constant (c : String) : Term := Pseudo.sort (.constant c)

/-- A raw term uses only indices below its ambient context size. -/
def Scoped (n : ℕ) : Term → Prop
  | .sort _ => True
  | .var i => i < n
  | .app f a => Scoped n f ∧ Scoped n a
  | .lam A b => Scoped n A ∧ Scoped (n + 1) b
  | .pi A B => Scoped n A ∧ Scoped (n + 1) B

/-- Translate names in atoms while keeping both sorts fixed. -/
def atomMap (f : String → String) : Atom → Atom
  | .sort s => .sort s
  | .constant c => .constant (f c)

/-- Translate global names using the public syntax's atom-map operation. -/
def mapConstants (f : String → String) : Term → Term := Pseudo.mapSorts (atomMap f)

end Term

/-- An open rewrite schema; instantiation substitutes its free variables. -/
structure RewriteRule where
  arity : ℕ
  lhs : Term
  rhs : Term
  lhs_scoped : lhs.Scoped arity
  rhs_scoped : rhs.Scoped arity
  deriving DecidableEq

/-- A raw λΠ-modulo presentation: declarations and rewrite schemas.

Admissibility conditions such as subject reduction and confluence are separate
properties. Arbitrary rule sets are not claimed to define consistent calculi.
-/
structure Calculus where
  declared : String → Term → Prop
  rules : Set RewriteRule

namespace Calculus

/-- Edinburgh LF's β-only profile over a chosen constant declaration relation. -/
def lf (declared : String → Term → Prop) : Calculus := ⟨declared, ∅⟩

/-- Compatible β/rewrite convertibility, before imposing any typing judgment. -/
inductive Conversion (C : Calculus) : Term → Term → Prop where
  | refl (t) : Conversion C t t
  | symm {t u : Term} : Conversion C t u → Conversion C u t
  | trans {t u v : Term} : Conversion C t u → Conversion C u v → Conversion C t v
  | beta (A b a : Term) : Conversion C (.app (.lam A b) a) (b.substOne a)
  | rewrite (r : RewriteRule) (hr : r ∈ C.rules) (σ : ℕ → Term) :
      Conversion C (r.lhs.subst σ) (r.rhs.subst σ)
  | app {f g a b : Term} : Conversion C f g → Conversion C a b → Conversion C (.app f a) (.app g b)
  | lam {A B t u : Term} : Conversion C A B → Conversion C t u → Conversion C (.lam A t) (.lam B u)
  | pi {A B t u : Term} : Conversion C A B → Conversion C t u → Conversion C (.pi A t) (.pi B u)

end Calculus

/-- A hypothetical typing judgment, including its local context. -/
structure Judgment where
  context : List Term
  term : Term
  type : Term

namespace Judgment

/-- Translate constants in the context, subject and type of a judgment. -/
def mapConstants (f : String → String) (J : Judgment) : Judgment :=
  ⟨J.context.map (Term.mapConstants f), J.term.mapConstants f, J.type.mapConstants f⟩

end Judgment

/-- The λΠ typing rules, closed under explicitly named judgment hypotheses.

Only `Type`-sorted domains may extend a context. Products may have codomain
sort `Type` or `Kind`. Declaration use requires a derivation that its type has
a sort; the data in `Calculus` is not itself a certificate of well-formedness.
-/
inductive Derives (C : Calculus) (H : Set Judgment) : Judgment → Prop where
  | hyp {J} (h : J ∈ H) : Derives C H J
  | type : Derives C H ⟨[], Term.univ .type, Term.univ .kind⟩
  | constant {c A s} (hdecl : C.declared c A)
      (hA : Derives C H ⟨[], A, Term.univ s⟩) :
      Derives C H ⟨[], Term.constant c, A⟩
  | var {Γ A} (hA : Derives C H ⟨Γ, A, Term.univ .type⟩) :
      Derives C H ⟨A :: Γ, .var 0, A.rename Nat.succ⟩
  | weak {Γ t A B} (ht : Derives C H ⟨Γ, t, A⟩)
      (hB : Derives C H ⟨Γ, B, Term.univ .type⟩) :
      Derives C H ⟨B :: Γ, t.rename Nat.succ, A.rename Nat.succ⟩
  | pi {Γ A B s} (hA : Derives C H ⟨Γ, A, Term.univ .type⟩)
      (hB : Derives C H ⟨A :: Γ, B, Term.univ s⟩) :
      Derives C H ⟨Γ, .pi A B, Term.univ s⟩
  | lam {Γ A b B s} (hb : Derives C H ⟨A :: Γ, b, B⟩)
      (hpi : Derives C H ⟨Γ, .pi A B, Term.univ s⟩) :
      Derives C H ⟨Γ, .lam A b, .pi A B⟩
  | app {Γ f a A B} (hf : Derives C H ⟨Γ, f, .pi A B⟩)
      (ha : Derives C H ⟨Γ, a, A⟩) :
      Derives C H ⟨Γ, .app f a, B.substOne a⟩
  | conv {Γ t A B s} (ht : Derives C H ⟨Γ, t, A⟩)
      (heq : C.Conversion A B) (hB : Derives C H ⟨Γ, B, Term.univ s⟩) :
      Derives C H ⟨Γ, t, B⟩

end Silmaril.Logic.TypeTheory.LambdaPi
