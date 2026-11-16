module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation

@[expose] public section

/-!
# A concrete target algebra for original raw realizability

Values are the actual full scoped syntax modulo the separately named LinearJ
conversion. Original raw conversion embeds one way into this target. No
conversion conservativity or original/checked reification is asserted.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

abbrev Value (n : ℕ) := Quotient (Relation.EqvGen.setoid (@LinearJ.Parallel n))

def ofTerm {n : ℕ} (t : Term n) : Value n := Quotient.mk _ t

noncomputable def rep {n : ℕ} (q : Value n) : Term n := Quotient.out q

noncomputable def pi {n : ℕ} (A : Value n) (B : Value (n + 1)) : Value n :=
  ofTerm (.pi (rep A) (rep B))

noncomputable def sigma {n : ℕ} (A : Value n) (B : Value (n + 1)) : Value n :=
  ofTerm (.sigma (rep A) (rep B))

noncomputable def id {n : ℕ} (A a b : Value n) : Value n :=
  ofTerm (.id (rep A) (rep a) (rep b))

noncomputable def app {n : ℕ} (f a : Value n) : Value n := ofTerm (.app (rep f) (rep a))
noncomputable def pair {n : ℕ} (a b : Value n) : Value n := ofTerm (.pair (rep a) (rep b))
noncomputable def refl {n : ℕ} (a : Value n) : Value n := ofTerm (.refl (rep a))
noncomputable def instantiate {n : ℕ} (B : Value (n + 1)) (a : Value n) : Value n :=
  ofTerm ((rep B).instantiate (rep a))

def univ (i : ℕ) : Value 0 := ofTerm (.univ i)
def nat : Value 0 := ofTerm .nat
def empty : Value 0 := ofTerm .empty
def unit : Value 0 := ofTerm .unit

def numeral : ℕ → Term 0
  | 0 => .zero
  | k + 1 => .succ (numeral k)

def Naturals : Set (Value 0) := {q | ∃ k, q = ofTerm (numeral k)}
def Units : Set (Value 0) := {ofTerm .star}

/-- A quotient class has a persistent head in one (hence any persistent) representative. -/
def HasHead {n : ℕ} (q : Value n) (k : RigidHead) : Prop :=
  ∃ t, ofTerm t = q ∧ t.rigidHead = some k

noncomputable def head {n : ℕ} (q : Value n) : Option RigidHead := by
  classical
  exact if h : ∃ k, HasHead q k then some (Classical.choose h) else none


end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
