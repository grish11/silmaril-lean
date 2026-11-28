module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Thms

/-! # Written composition with a common ambient context and ordered input -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition

open Region (packedExitType)
open Reverse (CheckedTable)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe u v

section Written

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d : Nat} {β : BoundCtx τ d} {I J K : LCtx τ}

/-- The receiver sees the intermediate packet and older ambient captures.
The producer's original input is an unused slot in between them. -/
def weaken (I : LCtx τ) (q : CheckedTable Φ (β.snoc (packedExitType J)) K) :
    CheckedTable Φ ((β.snoc (packedExitType I)).snoc (packedExitType J)) K :=
  let r := (BoundCtx.Renaming.succ β (packedExitType I)).up (packedExitType J)
  ⟨q.size, Link.Open.renameTable r q.table, (Link.Open.rename_check r q.table).trans q.checked,
    ⟨_, q.entry.2.rename r⟩⟩

/-- Sequence two written checked graphs at the intermediate ordered
interface, keeping the original input and final ordered exits. -/
def seq (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K) :
    CheckedTable Φ (β.snoc (packedExitType I)) K :=
  Link.Open.checked p (weaken I q)

/-- The independently written decoder reads the original input slot. -/
def identity (h : I ≠ []) : CheckedTable Φ (β.snoc (packedExitType I)) I :=
  ⟨_, Link.identityTable h, Link.identity_check h, ⟨.bv 0, .bv⟩⟩

end Written

/-- The relation compares literal packed LambdaSSA regions by native replay. -/
abbrev Hom (Φ : Type) [LetCase.Structural.Finite.Signature Φ] {d : Nat}
    (β : BoundCtx (Ty Empty) d) (I J : LCtx (Ty Empty)) :=
  Quotient (Reverse.checkedSetoid Φ (β.snoc (packedExitType I)) J)

/-- Nonempty ordered interfaces at a fixed primitive signature and
structural ambient context. The nonempty list supplies a decoder target. -/
structure Interface (Φ : Type) {d : Nat} (β : LetCase.Structural.Finite.Context d)
    (input : LetCase.Structural.Finite.StructuralContext β) where
  exits : LCtx (Ty Empty)
  nonempty : exits ≠ []

namespace Case

open LetCase.LocallyNameless (Equiv)

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
  {β : LetCase.Structural.Finite.Context d} {I J K : LCtx (Ty Empty)}

/-- The existing native LetCase equation classes at the literal packed types. -/
abbrev Hom (Φ : Type) [LetCase.Structural.Finite.Signature Φ] {d : Nat}
    (β : LetCase.Structural.Finite.Context d) (I J : LCtx (Ty Empty)) :=
  Quotient (Reverse.operandSetoid Φ (β.snoc (packedExitType I)) J)

/-- Native sequencing keeps the older captures under the input binder. -/
def seq (p : Operand Φ (β.snoc (packedExitType I)) (packedExitType J))
    (q : Operand Φ (β.snoc (packedExitType J)) (packedExitType K)) :
    Operand Φ (β.snoc (packedExitType I)) (packedExitType K) :=
  ⟨.let₁ p.1 q.1.underBinder, .let₁ p.2 q.2.underBinder⟩

/-- The native identity is the newest input variable. -/
def identity : Hom Φ β I I :=
  Quotient.mk _ ⟨.bv 0, .bv⟩

/-- Native let congruence descends to the existing LetCase quotient. -/
def seqClass : Hom Φ β I J → Hom Φ β J K → Hom Φ β I K :=
  Quotient.map₂ seq (fun {_ _} hp {_ _} hq => Equiv.let₁ hp hq.underBinder)

end Case

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition
