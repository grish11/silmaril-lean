module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Defs

/-! # Replay with the combined constructor-sequencing relation -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open LetCase.Structural.Finite (Context Types)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- Variable, unit, product and injection assembly with unary value lets.
The predicate is on the written operand and has no normalization witness. -/
def ConstructorOnly {Φ : Type*} : Tm Φ → Prop
  | .var _ | .unit => True
  | .let₁ a b | .pair a b => ConstructorOnly a ∧ ConstructorOnly b
  | .inl a | .inr a => ConstructorOnly a
  | .op .. | .let₂ .. | .case .. | .abort .. => False

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

abbrev Endpoint.ConstructorEqv (p q : Endpoint Φ β A) : Prop :=
  WithConstructorSequencing.Joined.Eqv false β.toList p.region q.region [A]

/-- The unrestricted replay question at the exact guarded reifier. -/
def ConstructorReplay (a b : Operand Φ β A) : Prop :=
  LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ β a.1 b.1 A →
    WithConstructorSequencing.Joined.Eqv false β.toList
      ((Code.ofLetCase a.2).guardedSSA 0) ((Code.ofLetCase b.2).guardedSSA 0) [A]

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
