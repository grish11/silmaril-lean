module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Thms

/-! # Directed relations on captured operands at the free interpretation

Two relations are defined on the operands themselves, in every older
environment, without packing and without a reply policy. The tree relation
keeps every finite observation of the free tree, including pending
requests. The outcome relation keeps only the ordered complete outcomes of
the existing ordered trace semantics.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open Silmaril.Elgot.ITree
open Isotope.Semantics (BoundEnv)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (run)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- A tree with no silent divergence on any path. -/
inductive Total {E : Type → Type} {X : Type 1} : Tree E X → Prop
  | ret (x : X) : Total (ret x)
  | vis {R : Type} (e : E R) (k : R → Tree E X) (below : ∀ reply, Total (k reply)) : Total (vis e k)

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-- The completed exchanges of a finite observation, in order. The way
the observation ends is forgotten. -/
def exchanges {X : Type 1} : Trace (Events Φ) X → Log Empty Φ
  | .exchange (.call f argument) reply tail => FreeMonoid.of ⟨f, argument, reply⟩ * exchanges tail
  | _ => 1

variable {d : Nat} {β : Context d} {A B : Ty Empty}

/-- Every finite observation of the first free tree is an observation of
the second, in every older environment. Pending requests are observed. -/
def TreeRefines (a b : Operand Φ (β.snoc A) B) : Prop :=
  ∀ ρ : BoundEnv Val (β.snoc A),
    TraceLE (a.2.denote Val (model Φ) (fun x => x.elim) ρ) (b.2.denote Val (model Φ) (fun x => x.elim) ρ)

/-- Every ordered complete outcome of the first operand is an outcome of
the second, in every older environment of the ordered trace semantics.
An outcome is a return with the whole ordered log of exchanges. -/
def OutcomeRefines (a b : Operand Φ (β.snoc A) B) : Prop :=
  ∀ ρ : BoundEnv LetCase.Structural.Finite.Value (β.snoc A), (run a.2 ρ).outcomes ⊆ (run b.2 ρ).outcomes

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free
