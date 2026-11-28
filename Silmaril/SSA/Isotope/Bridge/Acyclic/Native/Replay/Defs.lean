module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs

/-! # Native replay at the original single-exit interface -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open LetCase.Structural.Finite (Types Context)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

/-- Paper's contextual closure with projection returns, unit η, unary
forwarding and pure case returns. These are the existing opt-in seeds. -/
abbrev Endpoint.JoinedEqv (p q : Endpoint Φ β A) : Prop :=
  Extension.Eqv (WithCaseAndUnaryReturns.JoinedStep false) β.toList p.region q.region [A]

/-- The outstanding syntactic implication at the reified typed endpoints.
A proof must replay the LetCase derivation in the specified SSA relation. -/
def ReificationReplay (a b : Operand Φ β A) : Prop :=
  LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ β a.1 b.1 A →
    Extension.Eqv (WithCaseAndUnaryReturns.JoinedStep false) β.toList
      ((Code.ofLetCase a.2).guardedSSA 0) ((Code.ofLetCase b.2).guardedSSA 0) [A]

/-- Replay for the exact derivations selected by compilation. -/
abbrev Endpoint.ReificationReplay (p q : Endpoint Φ β A) : Prop :=
  Native.ReificationReplay p.compile q.compile

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
