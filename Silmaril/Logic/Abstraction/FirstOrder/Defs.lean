module

public import Silmaril.Logic.Abstraction.Thms
public import Silmaril.Logic.Institution.Examples.Unsorted
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Silmaril.Logic.Abstraction.FirstOrder

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Inst (Disc)
open Silmaril.Logic.Institution.Examples

variable {S T : UFOL.Signature}

/-- The universal abstraction binds one slot in its only argument. -/
abbrev universalShape : Shape where
  valence := 1
  arity := 1
  scope _ := {0}
  covers := by decide

/-- UFOL operations and predicates become ordinary abstractions. The logical symbols
are distinguished and are fixed by translated signature maps. -/
inductive Symbol (S : UFOL.Signature) : Shape → Type
  | op {n : Nat} : S.Op n → Symbol S (Shape.ordinary n)
  | rel {n : Nat} : S.Rel n → Symbol S (Shape.ordinary n)
  | eq : Symbol S (Shape.ordinary 2)
  | tt : Symbol S (Shape.ordinary 0)
  | not : Symbol S (Shape.ordinary 1)
  | and : Symbol S (Shape.ordinary 2)
  | all : Symbol S universalShape

/-- The shaped signature carrying the translation. -/
def signature (S : UFOL.Signature) : Signature := ⟨Symbol S⟩

/-- Extend a UFOL signature map to the shaped signature. -/
def symbolMap (f : S ⟶ T) : {s : Shape} → Symbol S s → Symbol T s
  | _, .op o => .op (f.ops o)
  | _, .rel r => .rel (f.rels r)
  | _, .eq => .eq
  | _, .tt => .tt
  | _, .not => .not
  | _, .and => .and
  | _, .all => .all

/-- Signature translation into the full abstraction institution. -/
def signatureFunctor : UFOL.Signature ⥤ Signature where
  obj := signature
  map f := ⟨symbolMap f⟩
  map_id S := by
    apply congrArg (fun (g : ∀ {s}, Symbol S s → Symbol S s) =>
      (⟨g⟩ : signature S ⟶ signature S))
    funext _ a
    cases a <;> rfl
  map_comp {S _ U} _ _ := by
    apply congrArg (fun (g : ∀ {s}, Symbol S s → Symbol U s) =>
      (⟨g⟩ : signature S ⟶ signature U))
    funext _ a
    cases a <;> rfl

/-- Apply an ordinary symbol to arguments in the same local context. -/
def ordinary {n k : Nat} (a : Symbol S (Shape.ordinary n))
    (args : Fin n → Term (signature S) k) : Term (signature S) k :=
  .app a args

/-- Translate object terms, sending UFOL variables to the specified local parameters. -/
def term {k l : Nat} (scope : Fin k → Fin l) : UFOL.Term S k → Term (signature S) l
  | .var i => .bound (scope i)
  | .app o args => ordinary (.op o) (fun j => term scope (args j))

/-- UFOL prepends its new variable at index zero. An abstraction argument appends it
after the outer local parameters. -/
def underBinder {k l : Nat} (scope : Fin k → Fin l) : Fin (k + 1) → Fin (l + 1) :=
  Fin.cons (Fin.last l) (fun i => (scope i).castSucc)

/-- Translate a UFOL formula to a term with a separate tagged Boolean result in canonical
models. The scope specifies where each UFOL variable is read in the local parameter list. -/
def formula : {k l : Nat} → (Fin k → Fin l) → UFOL.Formula S k → Term (signature S) l
  | _, _, scope, .eq t u => ordinary .eq ![term scope t, term scope u]
  | _, _, scope, .rel r args => ordinary (.rel r) (fun j => term scope (args j))
  | _, _, _, .tt => ordinary .tt Fin.elim0
  | _, _, scope, .not φ => ordinary .not ![formula scope φ]
  | _, _, scope, .and φ ψ => ordinary .and ![formula scope φ, formula scope ψ]
  | _, _, scope, .all φ => .app (.all : Symbol S universalShape)
      (fun _ => formula (underBinder scope) φ)

/-- A translated closed formula is a premise-free abstraction rule. -/
def sentence (φ : UFOL.Sentence S) : Sentence (signature S) :=
  Rule.formula (formula id φ)

/-- Encode the classical truth of a proposition on the Boolean side of the carrier. -/
noncomputable def truthValue {D : Type} (p : Prop) : D ⊕ Bool :=
  .inr (@decide p (Classical.propDecidable p))

/-- Only the tagged value true is classified as true. -/
def classifiesTrue {D : Type} (u : D ⊕ Bool) : Prop := u = .inr true

/-- Decode an object input. The default makes operations total on the whole single-sorted
carrier. Translated object terms only use the left branch. -/
def object {D : Type} (default : D) : D ⊕ Bool → D
  | .inl x => x
  | .inr _ => default

/-- Interpret UFOL over separate copies of the object carrier and the two Boolean values.
Universal quantification evaluates its argument at every embedded object, even when the object
carrier is a singleton. Equality compares carrier values and thus restricts to object equality. -/
noncomputable def algebra (M : UFOL.Structure S) : Algebra (signature S) where
  Carrier := M.carrier ⊕ Bool
  nonempty := ⟨.inr true⟩
  op
    | .op o, args => .inl (M.op o (fun i => object (Classical.choice M.nonempty) (args i Fin.elim0)))
    | .rel r, args => truthValue (M.rel r (fun i => object (Classical.choice M.nonempty) (args i Fin.elim0)))
    | .eq, args => truthValue (args (0 : Fin 2) Fin.elim0 = args (1 : Fin 2) Fin.elim0)
    | .tt, _ => .inr true
    | .not, args => truthValue (¬ classifiesTrue (args (0 : Fin 1) Fin.elim0))
    | .and, args => truthValue
        (classifiesTrue (args (0 : Fin 2) Fin.elim0) ∧ classifiesTrue (args (1 : Fin 2) Fin.elim0))
    | .all, args => truthValue (∀ x : M.carrier, classifiesTrue (args 0 (fun _ => .inl x)))

/-- Every UFOL structure yields an abstraction model. The logical order is the classical
proposition lattice with Boolean representatives, and schematic valuations are unrestricted. -/
noncomputable def model (M : UFOL.Structure S) : Model (signature S) where
  algebra := algebra M
  truth :=
    { Truth := Prop
      lattice := inferInstance
      includeValue := truthValue
      classify := classifiesTrue
      classify_include := fun p => by
        simpa only [classifiesTrue, truthValue, Sum.inr.injEq] using
          (@decide_eq_true_eq p (Classical.propDecidable p)) }
  space := ValuationSpace.full (algebra M)

/-- Equality arrows of canonical models induce equality transports of UFOL structures. -/
def toUFOLModels (S : UFOL.Signature) : Disc (UFOL.Structure S) ⥤ UFOL.Structure S where
  obj M := M
  map h := eqToHom h.down
  map_id _ := rfl
  map_comp f g := (eqToHom_trans (C := UFOL.Structure S) f.down g.down).symm

end Silmaril.Logic.Abstraction.FirstOrder
