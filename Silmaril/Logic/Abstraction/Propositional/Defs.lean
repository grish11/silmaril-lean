module

public import Silmaril.Logic.Abstraction.FirstOrder.Defs
public import Silmaril.Logic.Institution.Examples.Propositional

@[expose] public section

namespace Silmaril.Logic.Abstraction.Propositional

open CategoryTheory Silmaril.Logic.Institution.Examples

/-- The UFOL signature of propositional variables has no operations and only nullary predicates. -/
def signature (P : Type) : UFOL.Signature where
  Op _ := PEmpty
  Rel n := PLift (n = 0) × P

/-- Rename the nullary predicates along a map of propositional variables. -/
def signatureFunctor : Type ⥤ UFOL.Signature where
  obj := signature
  map f := ⟨fun o => o, fun r => (r.1, f r.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Encode propositional variables as nullary atoms and use the classical UFOL connectives. -/
def toUFOL {P : Type} : PL.Formula P → UFOL.Sentence (signature P)
  | .var p => .rel (n := 0) (⟨rfl⟩, p) Fin.elim0
  | .bot => .not .tt
  | .imp φ ψ => .not (.and (toUFOL φ) (.not (toUFOL ψ)))
  | .and φ ψ => .and (toUFOL φ) (toUFOL ψ)
  | .or φ ψ => .not (.and (.not (toUFOL φ)) (.not (toUFOL ψ)))

/-- Read a valuation from the interpretation of nullary predicates. -/
def valuation {P : Type} (M : UFOL.Structure (signature P)) : P → Prop :=
  fun p => M.rel (n := 0) (⟨rfl⟩, p) Fin.elim0

/-- Every propositional valuation is represented by a singleton UFOL object carrier. -/
def structureOf {P : Type} (v : P → Prop) : UFOL.Structure (signature P) where
  carrier := Unit
  nonempty := ⟨()⟩
  op o := o.elim
  rel r _ := v r.2

/-- The induced abstraction signature. -/
def abstractionSignature (P : Type) : Abstraction.Signature := FirstOrder.signature (signature P)

/-- Propositional formulas as premise-free abstraction rules. -/
def sentence {P : Type} (φ : PL.Formula P) : Sentence (abstractionSignature P) :=
  FirstOrder.sentence (toUFOL φ)

/-- The canonical abstraction model of a valuation, with one object and two truth values. -/
noncomputable def model {P : Type} (v : P → Prop) : Model (abstractionSignature P) :=
  FirstOrder.model (structureOf v)

end Silmaril.Logic.Abstraction.Propositional
