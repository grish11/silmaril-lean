module

public import Silmaril.Logic.Algebraic.Initial.Thms
public import Silmaril.Logic.Matching.FixedPoint

/-! A finite, one-sort constructor slice of actual initial-algebra constraints.
Models are all algebras, not only free ones. The native target has structural
operation-graph laws only; initiality is compiled to a genuine μ formula. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Ambient symbols may be infinite. A nullary symbol makes every actual
algebra carrier inhabited. Maps need not preserve the selected witness. -/
structure Signature where
  Op : Nat → Type
  constant : Op 0

structure Signature.Hom (A B : Signature) where
  operations : ∀ {n}, A.Op n → B.Op n

@[ext] theorem Signature.Hom.ext {A B : Signature} (f g : Signature.Hom A B)
    (h : ∀ n op, @f.operations n op = @g.operations n op) : f = g := by
  cases f; cases g; congr; funext n op; exact h n op

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨fun op => op⟩
  comp f g := ⟨fun op => g.operations (f.operations op)⟩
  id_comp _ := Signature.Hom.ext _ _ (fun _ _ => rfl)
  comp_id _ := Signature.Hom.ext _ _ (fun _ _ => rfl)
  assoc _ _ _ := Signature.Hom.ext _ _ (fun _ _ => rfl)

def Signature.public (A : Signature) : EQ.Signature := ⟨Unit, fun n _ _ => A.Op n⟩
def Signature.publicMap {A B : Signature} (f : A ⟶ B) : A.public ⟶ B.public :=
  ⟨id, f.operations⟩

def signatures : Signature ⥤ EQ.Signature where
  obj := Signature.public
  map := Signature.publicMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A finite constructor domain; no equations are imposed on its term algebra. -/
structure Constructors where
  count : Nat
  arity : Fin count → Nat
  constant : Fin count
  nullary : arity constant = 0

def Constructors.signature (A : Constructors) : Signature where
  Op n := {c : Fin A.count // A.arity c = n}
  constant := ⟨A.constant, A.nullary⟩

/-- Original constructor names and their contextual interpretation are retained.
In particular two different constructors may map to one ambient symbol. -/
structure Constraint (B : Signature) where
  constructors : Constructors
  operation : (c : Fin constructors.count) → B.Op (constructors.arity c)

def Constraint.map {B C : Signature} (f : B ⟶ C) (p : Constraint B) : Constraint C :=
  ⟨p.constructors, fun c => f.operations (p.operation c)⟩

def Constraint.context {B : Signature} (p : Constraint B) : p.constructors.signature ⟶ B where
  operations := fun ⟨c, h⟩ => h ▸ p.operation c

/-- This is the existing actual freeness constraint, with only its context
translated. No initiality assertion is stored in an algebra or native model. -/
def Constraint.actual {B : Signature} (p : Constraint B) : Initial.Constraint B.public :=
  Silmaril.Logic.Institution.Structured.Constraints.translate Initial.equational
    (Signature.publicMap p.context) (Initial.initialConstraint (Initial.emptyPresentation p.constructors.signature.public))

inductive Tree (A : Constructors) where
  | node (constructor : Fin A.count) (arguments : Fin (A.arity constructor) → Tree A)

/-- Independent constructor-tree evaluation into the actual public reduct. -/
def Tree.eval {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public) :
    Tree p.constructors → M.carrier ()
  | .node c args => M.op (w := fun _ => ()) (s := ()) (p.operation c)
      (fun i => Tree.eval p M (args i))

inductive Operation (A : Signature) : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | constructor {n w s} (op : A.Op n) : Operation A n w s
  /-- Universal definedness graph; it does not inspect a sentence's truth. -/
  | ceil {w s} : Operation A 1 w s

def nativeSignature (A : Signature) : ManySorted.Signature Unit := ⟨Operation A⟩
def nativeMap {A B : Signature} (f : A ⟶ B) : nativeSignature A ⟶ nativeSignature B :=
  ⟨fun op => match op with
    | .constructor c => .constructor (f.operations c)
    | .ceil => .ceil⟩

/-- The target is independently a native matching model. Constructor graphs
are total singletons and ceil is universal. There is no generatedness,
no-confusion, initiality or satisfaction field. -/
structure Model (A : Signature) where
  native : Silmaril.Logic.Matching.FirstOrder.Model (nativeSignature A)
  constructor : ∀ {n : Nat} {w : Fin n → Unit} {s : Unit} (op : A.Op n) (args : ∀ i, native.carrier (w i)),
    ∃! value : native.carrier s, value ∈ native.operation (.constructor (s := s) op) args
  ceil : ∀ {w : Fin 1 → Unit} {s : Unit} (args : ∀ i : Fin 1, native.carrier (w i)),
    native.operation (Operation.ceil (s := s)) args = Set.univ

abbrev Model.Hom {A : Signature} (M N : Model A) := M.native ⟶ N.native
instance {A : Signature} : Category (Model A) where
  Hom := Model.Hom
  id M := 𝟙 M.native
  comp f g := f ≫ g
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

def Model.decode {A : Signature} (M : Model A) : EQ.Algebra A.public where
  carrier := M.native.carrier
  op op args := Classical.choose (M.constructor op args)

def expand {A : Signature} (M : EQ.Algebra A.public) : Model A where
  native :=
    { carrier := M.carrier
      nonempty := fun s => ⟨M.op (w := Fin.elim0) (s := s) A.constant (fun i => i.elim0)⟩
      operation := fun op args => match op with
        | .constructor c => {M.op c args}
        | .ceil => Set.univ }
  constructor := fun op args => ⟨M.op op args, rfl, fun _ h => h⟩
  ceil := fun _ => rfl

abbrev Pat (A : Signature) (r k : Nat) :=
  Silmaril.Logic.Matching.FixedPoint.Pattern (nativeSignature A) (fun _ : Fin r => ()) (fun _ : Fin k => ()) ()
abbrev Raw (A : Signature) (k : Nat) :=
  Silmaril.Logic.Matching.FirstOrder.Pattern (nativeSignature A) (fun _ : Fin k => ()) ()

def bottom {A : Signature} {r k} : Pat A r k :=
  .base (.conj (.ex () (.var 0)) (.neg (.ex () (.var 0))))
def top {A : Signature} {r k} : Pat A r k := .base (.ex () (.var 0))

def disjunction {A : Signature} {r k} : List (Pat A r k) → Pat A r k
  | [] => bottom
  | p :: ps => .disj p (disjunction ps)
def conjunction {A : Signature} {r k} : List (Pat A r k) → Pat A r k
  | [] => top
  | p :: ps => .conj p (conjunction ps)

def closeAll {A : Signature} {r} : (k : Nat) → Pat A r k → Pat A r 0
  | 0, p => p
  | k+1, p => closeAll k (.all () p)

def generatedBody {B : Signature} (p : Constraint B) : Pat B 1 0 :=
  disjunction ((List.finRange p.constructors.count).map fun c =>
    .app (.constructor (p.operation c)) (fun _ => .setvar 0))
def generated {B : Signature} (p : Constraint B) : Pat B 0 0 := .mu (generatedBody p)

/-- On singleton-valued arguments, ceil of intersection is a truth-valued
native equality test. It is built from operation graphs, not a truth label. -/
def equal {A : Signature} {k} (a b : Raw A k) : Raw A k :=
  .app .ceil (fun _ => .conj a b)
def implies {A : Signature} {k} (a b : Raw A k) : Raw A k := .neg (.conj a (.neg b))

def constructorLeft {B : Signature} (p : Constraint B) (c d : Fin p.constructors.count) :
    Raw B (p.constructors.arity c + p.constructors.arity d) :=
  .app (.constructor (p.operation c)) (fun i => .var (Fin.castAdd _ i))
def constructorRight {B : Signature} (p : Constraint B) (c d : Fin p.constructors.count) :
    Raw B (p.constructors.arity c + p.constructors.arity d) :=
  .app (.constructor (p.operation d)) (fun i => .var (Fin.natAdd _ i))

def disjointClause {B : Signature} (p : Constraint B) (c d : Fin p.constructors.count) : Pat B 0 0 :=
  if c = d then top else
    closeAll _ (.base (.neg (equal (constructorLeft p c d) (constructorRight p c d))))

def injectiveClause {B : Signature} (p : Constraint B) (c : Fin p.constructors.count)
    (i : Fin (p.constructors.arity c)) : Pat B 0 0 :=
  closeAll _ (.base (implies (equal (constructorLeft p c c) (constructorRight p c c))
    (equal (.var (Fin.castAdd _ i)) (.var (Fin.natAdd _ i)))))

def noConfusion {B : Signature} (p : Constraint B) : Pat B 0 0 :=
  conjunction ((List.finRange p.constructors.count).flatMap fun c =>
    (List.finRange p.constructors.count).map (disjointClause p c) ++
    (List.finRange (p.constructors.arity c)).map (injectiveClause p c))

def compile {B : Signature} (p : Constraint B) : Silmaril.Logic.Matching.FixedPoint.Sentence (nativeSignature B) :=
  ⟨0, 0, (fun _ => ()), (fun _ => ()), (), .conj (generated p) (noConfusion p)⟩

/-- Semantic constructor properties, proved equivalent to native syntax below. -/
def Generated {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public) : Prop :=
  Function.Surjective (Tree.eval p M)

def NoConfusion {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public) : Prop :=
  (∀ c, Function.Injective (fun args => M.op (w := fun _ => ()) (s := ()) (p.operation c) args)) ∧
  ∀ c d, c ≠ d → ∀ xs ys,
    M.op (w := fun _ => ()) (s := ()) (p.operation c) xs ≠
      M.op (w := fun _ => ()) (s := ()) (p.operation d) ys

end Silmaril.Logic.Algebraic.Initial.Matching
