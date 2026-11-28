module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Abstraction logic

The shared binder slots of a shape follow Obua's *Abstraction Logic* (2021), "Algebra" and
"Syntax", and *Logic is Algebra*, §4. Templates, inference rules, logical orders, and valuation
spaces follow *A Primer in Abstraction Logic*, §3 of
*Abstraction Logic: A Complete Logic over Second-Order Abstract Syntax*. See
`docs/projects/abstraction-logic.md` for the source versions and the representation contract.
-/

namespace Silmaril.Logic.Abstraction

open CategoryTheory

/-- The global binder slots of an abstraction, and the slots in scope in each argument.
Every declared slot must be in scope in at least one argument. The sets may overlap. -/
structure Shape where
  valence : Nat
  arity : Nat
  scope : Fin arity → Finset (Fin valence)
  covers : ∀ slot : Fin valence, ∃ arg : Fin arity, slot ∈ scope arg

/-- The arity of the template expected in an argument. -/
abbrev Shape.binders (s : Shape) (arg : Fin s.arity) : Nat := (s.scope arg).card

/-- The slot named by a local parameter. Parameters list the in-scope slots in increasing order. -/
def Shape.slot (s : Shape) (arg : Fin s.arity) (i : Fin (s.binders arg)) : Fin s.valence :=
  (s.scope arg).orderEmbOfFin rfl i

/-- An ordinary operation with no binders. Constants have shape `ordinary 0`. -/
def Shape.ordinary (arity : Nat) : Shape where
  valence := 0
  arity := arity
  scope _ := ∅
  covers i := Fin.elim0 i

/-- Symbols indexed by their entire binding shape. -/
structure Signature where
  Symbol : Shape → Type

/-- A signature map preserves arity, valence, and all argument scopes. -/
structure Signature.Hom (S T : Signature) where
  symbol : ∀ {s : Shape}, S.Symbol s → T.Symbol s

instance : Category.{0} Signature where
  Hom := Signature.Hom
  id _ := ⟨fun a => a⟩
  comp f g := ⟨fun a => g.symbol (f.symbol a)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {S T : Signature}

/-- Nameless terms with `k` local parameters. Each argument sees the outer parameters followed
by the slots in its own scope. Free variable identity includes arity. -/
inductive Term (S : Signature) : Nat → Type
  | bound {k : Nat} (i : Fin k) : Term S k
  | free {k n : Nat} (name : Nat) (args : Fin n → Term S k) : Term S k
  | app {k : Nat} {s : Shape} (a : S.Symbol s)
      (args : (i : Fin s.arity) → Term S (k + s.binders i)) : Term S k

/-- The body of a template has exactly its formal parameter context and may use free schemata. -/
abbrev Template (S : Signature) (n : Nat) := Term S n

/-- The occurrence of a free variable at arity zero. -/
def Term.var {k : Nat} (name : Nat) : Term S k :=
  .free (n := 0) name Fin.elim0

/-- Rename abstraction symbols while leaving all variables and scopes alone. -/
def Term.map (f : S ⟶ T) : {k : Nat} → Term S k → Term T k
  | _, .bound i => .bound i
  | _, .free x args => .free x (fun i => (args i).map f)
  | _, .app a args => .app (f.symbol a) (fun i => (args i).map f)

/-- Rename local parameters. The new parameters of each abstraction argument stay local. -/
def Term.rename : {k l : Nat} → (Fin k → Fin l) → Term S k → Term S l
  | _, _, ρ, .bound i => .bound (ρ i)
  | _, _, ρ, .free x args => .free x (fun i => (args i).rename ρ)
  | _, _, ρ, .app a args => .app a (fun i =>
      (args i).rename (Fin.addCases (fun j => Fin.castAdd _ (ρ j)) (Fin.natAdd _)))

/-- Instantiate local parameters by terms, weakening the replacements under each binder. -/
def Term.instantiate : {k l : Nat} → (Fin k → Term S l) → Term S k → Term S l
  | _, _, σ, .bound i => σ i
  | _, _, σ, .free x args => .free x (fun i => (args i).instantiate σ)
  | _, _, σ, .app a args => .app a (fun i =>
      (args i).instantiate
        (Fin.addCases (fun j => (σ j).rename (Fin.castAdd _)) (fun j => .bound (Fin.natAdd _ j))))

/-- A partial substitution for free variable–arity pairs. Template parameters are local. -/
abbrev Substitution (S : Signature) := (n : Nat) → Nat → Option (Template S n)

def Substitution.map (f : S ⟶ T) (σ : Substitution S) : Substitution T :=
  fun n x => (σ n x).map (Term.map f)

/-- Simultaneous capture-avoiding substitution of free schemata. Only the original arguments
are recursively substituted before applying the replacement template. -/
def Term.subst (σ : Substitution S) : {k : Nat} → Term S k → Term S k
  | _, .bound i => .bound i
  | _, .free (n := n) x args =>
      let args' := fun i => (args i).subst σ
      match σ n x with
      | none => .free x args'
      | some body => body.instantiate args'
  | _, .app a args => .app a (fun i => (args i).subst σ)

/-- An operation on the one-sorted carrier. A nullary operation is represented by a function
from the empty tuple type. -/
abbrev Operation (U : Type) (n : Nat) := (Fin n → U) → U

/-- A nonempty carrier and an operator on tuples of operations for each shaped symbol. -/
structure Algebra (S : Signature) where
  Carrier : Type
  nonempty : Nonempty Carrier
  op : ∀ {s : Shape}, S.Symbol s → ((i : Fin s.arity) → Operation Carrier (s.binders i)) → Carrier

/-- Valuations assign operations independently at each variable–arity pair. -/
abbrev Valuation (U : Type) := (n : Nat) → Nat → Operation U n

/-- Update a variable at arity zero, as used when opening a template with a fresh name. -/
def Valuation.update {U : Type} (ν : Valuation U) (x : Nat) (u : U) : Valuation U
  | 0, y => if y = x then fun _ => u else ν 0 y
  | n + 1, y => ν (n + 1) y

/-- Evaluate a term at a valuation and an environment for its local parameters. A shaped
argument denotes the entire operation obtained by varying its own local parameters. -/
def Term.eval (A : Algebra S) (ν : Valuation A.Carrier) :
    {k : Nat} → Term S k → (Fin k → A.Carrier) → A.Carrier
  | _, .bound i, env => env i
  | _, .free (n := n) x args, env => ν n x (fun i => (args i).eval A ν env)
  | _, .app a args, env => A.op a (fun i values => (args i).eval A ν (Fin.addCases env values))

/-- Reinterpret source symbols through a shape-preserving map. Carrier and operations
available to valuations are shared with the target. -/
def Algebra.reduct (f : S ⟶ T) (A : Algebra T) : Algebra S where
  Carrier := A.Carrier
  nonempty := A.nonempty
  op a := A.op (f.symbol a)

/-- Interpret a partial syntactic substitution as a valuation update at all its entries. -/
def Algebra.substValuation (A : Algebra S) (ν : Valuation A.Carrier)
    (σ : Substitution S) : Valuation A.Carrier :=
  fun n x => match σ n x with
    | none => ν n x
    | some body => body.eval A ν

/-- The Primer's truth values as a complete lattice embedded as a retract of the universe.
In particular the carrier contains a value classified as the top truth value. -/
structure LogicalOrder (U : Type) where
  Truth : Type
  lattice : CompleteLattice Truth
  includeValue : Truth → U
  classify : U → Truth
  classify_include (t : Truth) : classify (includeValue t) = t

/-- Admissible valuations, closed under nullary updates and interpretation of substitutions. -/
structure ValuationSpace (A : Algebra S) where
  admissible : Set (Valuation A.Carrier)
  nonempty : admissible.Nonempty
  update_closed {ν : Valuation A.Carrier} (h : ν ∈ admissible)
    (x : Nat) (u : A.Carrier) : ν.update x u ∈ admissible
  subst_closed {ν : Valuation A.Carrier} (h : ν ∈ admissible)
    (σ : Substitution S) : A.substValuation ν σ ∈ admissible

/-- A full valuation space, using every operation of each arity. -/
def ValuationSpace.full (A : Algebra S) : ValuationSpace A where
  admissible := Set.univ
  nonempty := A.nonempty.elim fun u => ⟨fun _ _ _ => u, Set.mem_univ _⟩
  update_closed _ _ _ := Set.mem_univ _
  subst_closed _ _ := Set.mem_univ _

/-- A premise is a template with its own parameter count. -/
abbrev Premise (S : Signature) := Σ n, Template S n

def Premise.map (f : S ⟶ T) (p : Premise S) : Premise T := ⟨p.1, p.2.map f⟩

def Premise.subst (σ : Substitution S) (p : Premise S) : Premise S := ⟨p.1, p.2.subst σ⟩

/-- An institutional sentence is an inference rule. Premises have finite list representatives;
their order and multiplicity are immaterial to satisfaction. There are no unbound local
parameters in the conclusion. Free schemata are universally valued by satisfaction. -/
structure Rule (S : Signature) where
  premises : List (Premise S)
  conclusion : Term S 0

abbrev Sentence := Rule

/-- A term used as a premise-free rule. -/
def Rule.formula (t : Term S 0) : Rule S := ⟨[], t⟩

/-- Translate only the abstraction symbols of a rule. -/
def Rule.map (f : S ⟶ T) (r : Rule S) : Rule T :=
  ⟨r.premises.map (Premise.map f), r.conclusion.map f⟩

/-- Substitute schemata throughout a rule, keeping its premise templates' parameter counts. -/
def Rule.subst (σ : Substitution S) (r : Rule S) : Rule S :=
  ⟨r.premises.map (Premise.subst σ), r.conclusion.subst σ⟩

/-- A lower-bound presentation of the Primer's rule inequality. Every common lower bound
of the premise truth values (at every tuple of template parameters) lies below the truth
value of the conclusion. Equivalently, the meet of the premise infima lies below it. -/
def Rule.HoldsAt (r : Rule S) (A : Algebra S) (O : LogicalOrder A.Carrier)
    (ν : Valuation A.Carrier) : Prop :=
  letI := O.lattice
  ∀ b : O.Truth, (∀ p ∈ r.premises, ∀ args : Fin p.1 → A.Carrier,
    b ≤ O.classify (p.2.eval A ν args)) →
    b ≤ O.classify (r.conclusion.eval A ν Fin.elim0)

/-- The models over a signature, before imposing any theory. -/
structure Model (S : Signature) where
  algebra : Algebra S
  truth : LogicalOrder algebra.Carrier
  space : ValuationSpace algebra

/-- Rule validity in one model: its inequality holds for every admissible valuation. -/
def Model.Sat (M : Model S) (r : Sentence S) : Prop :=
  ∀ ν ∈ M.space.admissible, r.HoldsAt M.algebra M.truth ν

end Silmaril.Logic.Abstraction
