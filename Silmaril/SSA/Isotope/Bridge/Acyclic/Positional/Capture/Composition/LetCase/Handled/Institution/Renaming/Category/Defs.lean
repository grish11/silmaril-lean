module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Thms

/-! # Finite structural signatures and their injective renamings

A renaming is an injective relabelling of the existing instruction
signatures, between two finite structural signatures. It keeps the argument
and reply type of every primitive. Types are not translated.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)
open Silmaril.Isotope.Institution (InstrSig)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Event)
open Free (Events)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- A finite structural signature with its instruction type. -/
structure StructuralSig where
  Instr : Type
  [signature : LetCase.Structural.Finite.Signature Instr]

attribute [instance] StructuralSig.signature

namespace StructuralSig

/-- An injective relabelling that keeps each argument and reply type. -/
@[ext] structure Hom (X Y : StructuralSig) where
  hom : sig X.Instr ⟶ sig Y.Instr
  injective : Function.Injective hom.instr

instance : Category StructuralSig where
  Hom := Hom
  id X := ⟨𝟙 (sig X.Instr), Function.injective_id⟩
  comp f g := ⟨f.hom ≫ g.hom, g.injective.comp f.injective⟩

end StructuralSig

variable {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Φ] [LetCase.Structural.Finite.Signature Ψ]

local notation "Value" => LetCase.Structural.Finite.Value

/-- A relabelling on requests. The argument is carried along the equation
of argument types. -/
def eventsRequest (f : sig Φ ⟶ sig Ψ) : Request (Events Φ) → Request (Events Ψ)
  | ⟨_, .call x argument⟩ =>
    ⟨_, .call (f.instr x) (cast (congrArg (fun A => Value A) (f.source x).symm) argument)⟩

/-- A relabelling as a map of request signatures. The reply is carried
back along the equation of reply types. -/
def eventsHom (f : sig Φ ⟶ sig Ψ) : (events Φ).toSignature ⟶ (events Ψ).toSignature where
  request := eventsRequest f
  reply := fun ⟨_, .call x _⟩ reply => cast (congrArg (fun A => Value A) (f.target x)) reply

/-- Reduct of handled-trace models along a relabelling. -/
def reductFunctor (f : sig Φ ⟶ sig Ψ) : Discrete (HandledModel Ψ) ⥤ Discrete (HandledModel Φ) :=
  Discrete.functor fun N => Discrete.mk (N.reduct (eventsHom f))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
