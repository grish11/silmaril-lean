module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Thms

/-! # The free request and reply interpretation, histories and policies

Every primitive of the finite structural signature is effectful. The free
interpretation turns each primitive into one visible request that carries
the generator and its typed argument, and continues with the typed reply.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open Silmaril.Elgot.ITree
open Isotope.Semantics (BoundEnv InstructionModel)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Event Structured.Lifted
  Structured.instructions Structured.PureMaps Structured.toSmall)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe s

/-- Atom carriers of the structural value model. There are no atoms. -/
abbrev Atoms : Empty → Type := fun _ => Nat

/-- Requests name a primitive with its argument, and are answered at its
declared result type. -/
abbrev Events (Φ : Type) [LetCase.Structural.Finite.Signature Φ] : Type → Type :=
  Structured.Event (Φ := Φ) Atoms

/-- Values of the tree semantics, one universe above the event values. -/
abbrev Val : Ty Empty → Type 1 := Ty.denote (Structured.Lifted Atoms)

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-- No primitive is declared pure, so no pure map is needed. -/
def noPure : Structured.PureMaps (Φ := Φ) (ε := Bool) Atoms :=
  fun _ pure => Bool.noConfusion pure

variable (Φ) in
/-- The free interpretation: each primitive is one request and its reply. -/
noncomputable def model : InstructionModel Val Φ (Tree (Events Φ)) :=
  Structured.instructions Atoms noPure

/-- The complete finite observation with the logged exchanges in order,
ending at the given return. -/
def history {X : Type 1} (log : Log Empty Φ) (result : X) : Trace (Events Φ) X :=
  (FreeMonoid.toList log).foldr
    (fun exchange tail => .exchange (.call exchange.generator exchange.argument) exchange.reply tail)
    (.result result)

variable (Φ) in
/-- The policy with one state that admits every typed reply. -/
def permissive : Handler PUnit (Events Φ) := fun _ _ _ _ => True

variable (Φ) in
/-- The policy whose state is the list of exchanges still expected. It
admits an exchange exactly when it is the next one expected. -/
def scripted : Handler (Log Empty Φ) (Events Φ)
  | ⟨_, .call f argument⟩, expected, reply, rest => expected = FreeMonoid.of ⟨f, argument, reply⟩ * rest

/-- Each complete history can be replayed from some state. -/
def Exposes {State : Type s} (policy : Handler State (Events Φ)) : Prop :=
  ∀ {X : Type 1} (log : Log Empty Φ) (result : X), ∃ state, Replay policy state (history log result)

/-- Lower every slot of a tree environment to the event universe. -/
def lower {n : Nat} {β : LetCase.Structural.Finite.Context n} (ρ : BoundEnv Val β) :
    BoundEnv LetCase.Structural.Finite.Value β :=
  fun i => Structured.toSmall Atoms (β.get i) (ρ i)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free
