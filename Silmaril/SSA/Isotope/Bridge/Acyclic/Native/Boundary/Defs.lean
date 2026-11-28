module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs

/-! # Inhabited boundaries of native SSA equational replay -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary

open Region.Paper
open UnaryReturn.Beta.Constructors (pairSequence)
open UnaryReturn.Beta.Constructors.Example (source)
open RetainedLet (returnOnce)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

scoped instance : LetCase.Structural.Finite.Signature Empty := ⟨Empty.elim, Empty.elim⟩

local notation "U" => (Ty.unit : Ty Empty)
local notation "X" => source
local notation "P" => (Ty.product X X)
local notation "a" => (Tm.let₁ (Tm.var 0) (Tm.var 0) : Tm Empty)
local notation "b" => (Tm.var 0 : Tm Empty)

/-- Return the unit constructor at a packed unit input. -/
def unitReturn : Endpoint Empty (.snoc .nil U) U :=
  ⟨.br 0 .unit, .br rfl .unit, .br .unit⟩

/-- Forward the original packed unit input. -/
def unitForward : Endpoint Empty (.snoc .nil U) U :=
  ⟨.br 0 (.var 0), .br rfl (.var rfl), .br (.var 0)⟩

/-- Evaluate both components as a pair operand, then return it. -/
def paired : Endpoint Empty (.snoc .nil X) P :=
  ⟨returnOnce (.pair a b), .let₁ (.pair (.let₁ (.var rfl) (.var rfl)) (.var rfl)) (.br rfl (.var rfl)),
    .let₁ _ (.br _)⟩

/-- Evaluate the same components in order in native region binders.
The second component reads the original packed input. -/
def sequenced : Endpoint Empty (.snoc .nil X) P :=
  ⟨pairSequence a b, .let₁ (.let₁ (.var rfl) (.var rfl))
    (.let₁ (.var (i := 1) rfl) (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))),
    .let₁ _ (.let₁ _ (.br _))⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary
