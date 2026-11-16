module

public import Silmaril.Logic.Egglog.Core.Defs
public import Mathlib.Data.List.OfFn

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.FiniteSupport
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- Actual ambient symbols retain arity and their entire ordered dependent
profile. No equality or enumeration of the ambient signature is assumed. -/
abbrev Constructor (S : Core.Signature) :=
  Σ n, Σ w : Fin n → S.S, Σ s : S.S, S.Op n w s
abbrev Relation (S : Core.Signature) := Σ n, Σ w : Fin n → S.S, S.Rel n w
abbrev FunctionSymbol (S : Core.Signature) :=
  Σ n, Σ w : Fin n → S.S, Σ s : S.S, S.Function n w s

/-- A finite occurrence list, allowing aliases/repetition. It is not a global
naming view. Sort collection includes every profile and every scoped binder. -/
structure Footprint (S : Core.Signature) where
  sorts : List S.S
  constructors : List (Constructor S)
  relations : List (Relation S)
  functions : List (FunctionSymbol S)

def Footprint.empty (S : Core.Signature) : Footprint S := ⟨[], [], [], []⟩
def Footprint.append {S : Core.Signature} (left right : Footprint S) : Footprint S :=
  ⟨left.sorts ++ right.sorts, left.constructors ++ right.constructors,
    left.relations ++ right.relations, left.functions ++ right.functions⟩
def Footprint.merge {S : Core.Signature} (entries : List (Footprint S)) : Footprint S :=
  entries.foldr Footprint.append (Footprint.empty S)

def term {S : Core.Signature} {n : Nat} {Γ : Fin n → S.S} {s : S.S} :
    EQ.Term S.toSignature Γ s → Footprint S
  | .var i => ⟨[Γ i], [], [], []⟩
  | .app (n := k) (w := w) (s := output) symbol arguments =>
      (⟨output :: List.ofFn w, [⟨k, w, output, symbol⟩], [], []⟩ : Footprint S).append
        (Footprint.merge (List.ofFn (fun i => term (arguments i))))

def atom {S : Core.Signature} {n : Nat} {Γ : Fin n → S.S} : Core.Atom S Γ → Footprint S
  | .equal equality => (term equality.lhs).append (term equality.rhs)
  | .relation (n := k) (w := w) predicate arguments =>
      (⟨List.ofFn w, [], [⟨k, w, predicate⟩], []⟩ : Footprint S).append
        (Footprint.merge (List.ofFn (fun i => term (arguments i))))
  | .row (n := k) (w := w) (s := s) function arguments value =>
      (⟨s :: List.ofFn w, [], [], [⟨k, w, s, function⟩]⟩ : Footprint S).append
        ((Footprint.merge (List.ofFn (fun i => term (arguments i)))).append (term value))

/-- The finite support of a sentence contains its whole context, even positions
unused by every term/atom. This collection is independent of all model carriers. -/
def sentence {S : Core.Signature} : Core.Sentence S → Footprint S
  | .rule rule =>
      (⟨List.ofFn rule.context, [], [], []⟩ : Footprint S).append
        ((Footprint.merge (rule.body.map atom)).append (atom rule.head))
  | .query query =>
      (⟨List.ofFn query.context, [], [], []⟩ : Footprint S).append
        (Footprint.merge (query.goals.map atom))

def Footprint.Subset {S : Core.Signature} (left right : Footprint S) : Prop :=
  (∀ s ∈ left.sorts, s ∈ right.sorts) ∧
  (∀ o ∈ left.constructors, o ∈ right.constructors) ∧
  (∀ r ∈ left.relations, r ∈ right.relations) ∧
  (∀ f ∈ left.functions, f ∈ right.functions)

/-- Explicit syntactic support conditions used to lift a typed term into the
finite subsignature. They require every full profile, not just result sorts. -/
def SupportsTerm {S : Core.Signature} (support : Footprint S) {n : Nat}
    {Γ : Fin n → S.S} {s : S.S} (expression : EQ.Term S.toSignature Γ s) : Prop :=
  EQ.Term.rec (motive := fun _ _ => Prop)
    (fun i => Γ i ∈ support.sorts)
    (fun {k} {w} {output} symbol _ children =>
      output ∈ support.sorts ∧ (∀ i, w i ∈ support.sorts) ∧
        (⟨k, w, output, symbol⟩ : Constructor S) ∈ support.constructors ∧ ∀ i, children i)
    expression

def SupportsAtom {S : Core.Signature} (support : Footprint S) {n : Nat}
    {Γ : Fin n → S.S} : Core.Atom S Γ → Prop
  | .equal equality => SupportsTerm support equality.lhs ∧ SupportsTerm support equality.rhs
  | .relation (n := k) (w := w) predicate arguments =>
      (∀ i, w i ∈ support.sorts) ∧
        (⟨k, w, predicate⟩ : Relation S) ∈ support.relations ∧
        ∀ i, SupportsTerm support (arguments i)
  | .row (n := k) (w := w) (s := s) function arguments value =>
      s ∈ support.sorts ∧ (∀ i, w i ∈ support.sorts) ∧
        (⟨k, w, s, function⟩ : FunctionSymbol S) ∈ support.functions ∧
        (∀ i, SupportsTerm support (arguments i)) ∧ SupportsTerm support value

def SupportsSentence {S : Core.Signature} (support : Footprint S) : Core.Sentence S → Prop
  | .rule rule => (∀ i, rule.context i ∈ support.sorts) ∧
      (∀ a ∈ rule.body, SupportsAtom support a) ∧ SupportsAtom support rule.head
  | .query query => (∀ i, query.context i ∈ support.sorts) ∧
      ∀ a ∈ query.goals, SupportsAtom support a

/-- The actual finite subsignature selected by occurrence support. Its models
remain ordinary Core models; this construction only restricts syntax. -/
def Footprint.signature {S : Core.Signature} (support : Footprint S) : Core.Signature where
  S := {s : S.S // s ∈ support.sorts}
  Op := fun n w s => {symbol : S.Op n (fun i => (w i).val) s.val //
    (⟨n, (fun i => (w i).val), s.val, symbol⟩ : Constructor S) ∈ support.constructors}
  Rel := fun n w => {symbol : S.Rel n (fun i => (w i).val) //
    (⟨n, (fun i => (w i).val), symbol⟩ : Relation S) ∈ support.relations}
  Function := fun n w s => {symbol : S.Function n (fun i => (w i).val) s.val //
    (⟨n, (fun i => (w i).val), s.val, symbol⟩ : FunctionSymbol S) ∈ support.functions}

/-- Inclusion is an actual Core signature homomorphism. -/
def Footprint.inclusion {S : Core.Signature} (support : Footprint S) : support.signature ⟶ S where
  sorts := Subtype.val
  ops := Subtype.val
  rels := Subtype.val
  functions := Subtype.val

/-- Lift the entire context, including all unused binders. -/
def Footprint.context {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (supported : ∀ i, Γ i ∈ support.sorts) :
    Fin n → support.signature.S := fun i => ⟨Γ i, supported i⟩

/-- Every recorded symbol's complete profile is present in the sort support.
This makes occurrence metadata sufficient to build checked named declarations. -/
def Footprint.Closed {S : Core.Signature} (support : Footprint S) : Prop :=
  (∀ symbol ∈ support.constructors,
    symbol.2.2.1 ∈ support.sorts ∧ ∀ i, symbol.2.1 i ∈ support.sorts) ∧
  (∀ symbol ∈ support.relations, ∀ i, symbol.2.1 i ∈ support.sorts) ∧
  (∀ symbol ∈ support.functions,
    symbol.2.2.1 ∈ support.sorts ∧ ∀ i, symbol.2.1 i ∈ support.sorts)

/-- Package an actual supported ambient constructor with all its local subtype sorts. -/
def Footprint.constructorFromMember {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (entry : {packet : Constructor S // packet ∈ support.constructors}) :
    Constructor support.signature :=
  let symbol := entry.val
  let profile := closed.1 symbol entry.property
  ⟨symbol.1, (fun i => ⟨symbol.2.1 i, profile.2 i⟩), ⟨symbol.2.2.1, profile.1⟩, ⟨symbol.2.2.2,
    by simpa using entry.property⟩⟩

/-- Package an actual supported ambient relation with all its local subtype sorts. -/
def Footprint.relationFromMember {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (entry : {packet : Relation S // packet ∈ support.relations}) :
    Relation support.signature :=
  let symbol := entry.val
  let profile := closed.2.1 symbol entry.property
  ⟨symbol.1, (fun i => ⟨symbol.2.1 i, profile i⟩), ⟨symbol.2.2,
    by simpa using entry.property⟩⟩

/-- Package an actual supported ambient function with all its local subtype sorts. -/
def Footprint.functionFromMember {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (entry : {packet : FunctionSymbol S // packet ∈ support.functions}) :
    FunctionSymbol support.signature :=
  let symbol := entry.val
  let profile := closed.2.2 symbol entry.property
  ⟨symbol.1, (fun i => ⟨symbol.2.1 i, profile.2 i⟩), ⟨symbol.2.2.1, profile.1⟩, ⟨symbol.2.2.2,
    by simpa using entry.property⟩⟩

end Silmaril.Logic.Egglog.Source.Named.FiniteSupport
