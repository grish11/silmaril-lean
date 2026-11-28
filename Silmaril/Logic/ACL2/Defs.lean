module

public import Silmaril.Logic.Institution.Pi.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2

open CategoryTheory

/-- Package-qualified, already resolved ACL2 symbol names. The source reader is external. -/
structure Name where
  package : String
  symbol : String
  deriving DecidableEq, Repr

/-- ACL2 has one logical sort. Tests such as `consp` return values of this same sort. -/
inductive LogicalSort where
  | value
  deriving DecidableEq, Repr

/-- A partial arity table for user functions. Primitive operations have fixed syntax and arities. -/
structure Signature where
  arity : Name → Option Nat

namespace Signature

/-- The declared user functions of a given arity. -/
abbrev Symbol (S : Signature) (n : Nat) := {f : Name // S.arity f = some n}

/-- Resolve a package-qualified user function at a call site's arity. -/
def resolve (S : Signature) (f : Name) (n : Nat) : Option (S.Symbol n) :=
  if h : S.arity f = some n then some ⟨f, h⟩ else none

/-- Signature arrows are inclusions of named declarations. They preserve package, name and arity. -/
structure Hom (S T : Signature) : Type where
  preserve : ∀ {f n}, S.arity f = some n → T.arity f = some n

instance : Category Signature where
  Hom := Hom
  id _ := ⟨id⟩
  comp f g := ⟨fun h => g.preserve (f.preserve h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def Hom.symbol {S T : Signature} (σ : S ⟶ T) {n : Nat} (f : S.Symbol n) : T.Symbol n :=
  ⟨f.val, σ.preserve f.property⟩

@[simp] theorem Hom.symbol_id {S : Signature} {n : Nat} (f : S.Symbol n) :
    (Hom.symbol (𝟙 S) f) = f := rfl

theorem Hom.symbol_comp {S T U : Signature} (σ : S ⟶ T) (τ : T ⟶ U)
    {n : Nat} (f : S.Symbol n) : (σ ≫ τ).symbol f = τ.symbol (σ.symbol f) := rfl

def empty : Signature := ⟨fun _ => none⟩

end Signature

/-- The number of free variables is explicit. All arguments and results have sort `value`. -/
inductive Term (S : Signature) (vars : Nat) where
  | var (i : Fin vars)
  | app {n : Nat} (f : S.Symbol n) (args : Fin n → Term S vars)
  | nil
  | truth
  | cons (car cdr : Term S vars)
  | car (x : Term S vars)
  | cdr (x : Term S vars)
  | consp (x : Term S vars)
  | equal (lhs rhs : Term S vars)
  | ite (test yes no : Term S vars)

namespace Term

variable {S T : Signature} {n m : Nat}

def map (σ : S ⟶ T) : Term S n → Term T n
  | .var i => .var i
  | .app f args => .app (σ.symbol f) (fun j => map σ (args j))
  | .nil => .nil
  | .truth => .truth
  | .cons x y => .cons (map σ x) (map σ y)
  | .car x => .car (map σ x)
  | .cdr x => .cdr (map σ x)
  | .consp x => .consp (map σ x)
  | .equal x y => .equal (map σ x) (map σ y)
  | .ite x y z => .ite (map σ x) (map σ y) (map σ z)

/-- Simultaneous substitution into the finite free-variable context. -/
def subst (s : Fin n → Term S m) : Term S n → Term S m
  | .var i => s i
  | .app f args => .app f (fun j => subst s (args j))
  | .nil => .nil
  | .truth => .truth
  | .cons x y => .cons (subst s x) (subst s y)
  | .car x => .car (subst s x)
  | .cdr x => .cdr (subst s x)
  | .consp x => .consp (subst s x)
  | .equal x y => .equal (subst s x) (subst s y)
  | .ite x y z => .ite (subst s x) (subst s y) (subst s z)

/-- ACL2's two-argument `implies` on logical values. -/
def implies (p q : Term S n) : Term S n := .ite p (.ite q .truth .nil) .truth

end Term

/-- An ACL2 statement asserts that a term is non-NIL under every assignment of its free variables. -/
structure Sentence (S : Signature) where
  vars : Nat
  term : Term S vars

namespace Sentence

variable {S T : Signature} {n : Nat}

def map (σ : S ⟶ T) (p : Sentence S) : Sentence T := ⟨p.vars, p.term.map σ⟩

def eq (lhs rhs : Term S n) : Sentence S := ⟨n, .equal lhs rhs⟩

end Sentence

/-- Interpretation of the built-in fragment. These laws hold of the corresponding logical
ACL2 primitives. The carrier may include values other than conses and the two named atoms. -/
structure Primitives where
  Value : Type
  [decEq : DecidableEq Value]
  nil : Value
  truth : Value
  cons : Value → Value → Value
  car : Value → Value
  cdr : Value → Value
  consp : Value → Bool
  truth_ne_nil : truth ≠ nil
  consp_nil : consp nil = false
  consp_truth : consp truth = false
  consp_cons : ∀ x y, consp (cons x y) = true
  car_cons : ∀ x y, car (cons x y) = x
  cdr_cons : ∀ x y, cdr (cons x y) = y
  car_atom : ∀ x, consp x = false → car x = nil
  cdr_atom : ∀ x, consp x = false → cdr x = nil

attribute [instance] Primitives.decEq

def Primitives.ofBool (P : Primitives) (b : Bool) : P.Value :=
  if b then P.truth else P.nil

def Primitives.equal (P : Primitives) (x y : P.Value) : P.Value :=
  P.ofBool (decide (x = y))

def Primitives.ite (P : Primitives) (x y z : P.Value) : P.Value :=
  if x = P.nil then z else y

/-- A model gives total denotations to each declared user function. -/
structure Model (S : Signature) where
  primitives : Primitives
  interpret : ∀ {n}, S.Symbol n → (Fin n → primitives.Value) → primitives.Value

/-- Only identities between models are used. The morphisms are small even though models
contain a carrier type. -/
instance Model.category (S : Signature) : Category.{0} (Model S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

instance Model.homSubsingleton {S : Signature} (M N : Model S) : Subsingleton (M ⟶ N) :=
  inferInstanceAs (Subsingleton (PLift (M = N)))

/-- A function out of the discrete category of models gives a functor. -/
def Model.functor {S : Signature} {C : Type*} [Category C] (F : Model S → C) : Model S ⥤ C where
  obj := F
  map f := eqToHom (congrArg F f.down)
  map_id _ := rfl
  map_comp f g := by rcases f with ⟨⟨⟩⟩; rcases g with ⟨⟨⟩⟩; simp

def Model.reduct {S T : Signature} (σ : S ⟶ T) (M : Model T) : Model S :=
  ⟨M.primitives, fun f => M.interpret (σ.symbol f)⟩

def Term.eval {S : Signature} {n : Nat} (M : Model S) (env : Fin n → M.primitives.Value) :
    Term S n → M.primitives.Value
  | .var i => env i
  | .app f args => M.interpret f (fun j => eval M env (args j))
  | .nil => M.primitives.nil
  | .truth => M.primitives.truth
  | .cons x y => M.primitives.cons (eval M env x) (eval M env y)
  | .car x => M.primitives.car (eval M env x)
  | .cdr x => M.primitives.cdr (eval M env x)
  | .consp x => M.primitives.ofBool (M.primitives.consp (eval M env x))
  | .equal x y => M.primitives.equal (eval M env x) (eval M env y)
  | .ite x y z => M.primitives.ite (eval M env x) (eval M env y) (eval M env z)

def Sentence.Holds {S : Signature} (M : Model S) (p : Sentence S) : Prop :=
  ∀ env, p.term.eval M env ≠ M.primitives.nil

/-- Derivations use only the displayed rules. In particular theorem events cannot be added
by exhibiting semantic validity or by supplying an unchecked theorem name. -/
inductive Derives {S : Signature} (Γ : Set (Sentence S)) : Sentence S → Prop
  | hyp {p} : p ∈ Γ → Derives Γ p
  | truth {n : Nat} : Derives Γ ⟨n, .truth⟩
  | refl {n : Nat} (x : Term S n) : Derives Γ (.eq x x)
  | symm {n : Nat} {x y : Term S n} : Derives Γ (.eq x y) → Derives Γ (.eq y x)
  | trans {n : Nat} {x y z : Term S n} :
      Derives Γ (.eq x y) → Derives Γ (.eq y z) → Derives Γ (.eq x z)
  | congr {n m : Nat} (body : Term S n) (lhs rhs : Fin n → Term S m) :
      (∀ i, Derives Γ (.eq (lhs i) (rhs i))) → Derives Γ (.eq (body.subst lhs) (body.subst rhs))
  | eqMp {n : Nat} {x y : Term S n} : Derives Γ (.eq x y) → Derives Γ ⟨n, x⟩ → Derives Γ ⟨n, y⟩
  | mp {n : Nat} {p q : Term S n} : Derives Γ ⟨n, p.implies q⟩ → Derives Γ ⟨n, p⟩ → Derives Γ ⟨n, q⟩
  | subst {n m : Nat} {x : Term S n} (s : Fin n → Term S m) :
      Derives Γ ⟨n, x⟩ → Derives Γ ⟨m, x.subst s⟩
  | carCons {n : Nat} (x y : Term S n) : Derives Γ (.eq (.car (.cons x y)) x)
  | cdrCons {n : Nat} (x y : Term S n) : Derives Γ (.eq (.cdr (.cons x y)) y)
  | conspCons {n : Nat} (x y : Term S n) : Derives Γ (.eq (.consp (.cons x y)) .truth)
  | carAtom {n : Nat} {x : Term S n} :
      Derives Γ (.eq (.consp x) .nil) → Derives Γ (.eq (.car x) .nil)
  | cdrAtom {n : Nat} {x : Term S n} :
      Derives Γ (.eq (.consp x) .nil) → Derives Γ (.eq (.cdr x) .nil)
  | conspNil {n : Nat} : Derives Γ (.eq (.consp (.nil : Term S n)) .nil)
  | conspTruth {n : Nat} : Derives Γ (.eq (.consp (.truth : Term S n)) .nil)
  | ifNil {n : Nat} (x y : Term S n) : Derives Γ (.eq (.ite .nil x y) y)
  | ifTruth {n : Nat} (x y : Term S n) : Derives Γ (.eq (.ite .truth x y) x)
  | ifSame {n : Nat} (x y : Term S n) : Derives Γ (.eq (.ite x y y) y)

/-- Models form a discrete category. Signature change acts by restriction of denotations. -/
def room (S : Signature) : Institution.Room.{0, 0, 1} :=
  ⟨Sentence S, Cat.of (Model S), fun M p => p.Holds M⟩

end Silmaril.Logic.ACL2
