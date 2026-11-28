module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms

/-! # Exact weak-tree transport from guarded native rows to named RTL -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded

open Silmaril.Elgot (iter mapReturn liftPure)
open Silmaril.Elgot.ITree (Tree)
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head Table)

variable {Φ : Type} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R : List Syntax.Ty} {E : Type → Type} {B : Type 1}

/-- Shared primitive execution supplies the whole typed reply, including its
tag. Local effects and primitive divergence stay in the query tree. -/
abbrev Query {Φ : Type} [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) (E : Type → Type) :=
  (f : Φ) → Syntax.Payload (instrSrc f) → Tree E (ULift.{1} (Packet (S.replies f)))

/-- An exit is pending for one lookup, as in the named cyclic runner. -/
abbrev Cursor (R : List Syntax.Ty) := ULift.{1} (TwoRequest.Tag ⊕ Packet R)

def atBlock (p : Packet R) : Cursor R := ⟨.inr p⟩

def atExit (i : TwoRequest.Tag) : Cursor R := ⟨.inl i⟩

/-- Interpret a guarded head in the shared query model. The ordinary exit
keeps its tag. Selected UB is interpreted by the separate shaped semantics. -/
def headStep (query : Query S E) : Head S R → Tree E (B ⊕ Cursor R)
  | .exit i _ => pure (.inr (atExit i))
  | .diverge => Silmaril.Elgot.ITree.diverge
  | .request f arg next => query f arg >>= fun r =>
      pure (.inr (atBlock (next r.down.1 r.down.2)))

def step (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (query : Query S E) (result : TwoRequest.Tag → B) (c : Cursor R) : Tree E (B ⊕ Cursor R) :=
  match c.down with
  | .inl i => pure (.inl (result i))
  | .inr p => headStep query (g.head caller p)

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} [HasTy P.Instr Syntax.Ty]
  {I : Interface κ V K} {fields : K → List (V × Ty κ)} {source : CFG V K P.Instr}
  {N : RequestSignature P.Instr}

/-- The old unit exit payload and the empty selected-register record have
exactly this packed representation at the two ordered exit positions. -/
def unitExit (i : TwoRequest.Tag) : Transfer α :=
  FiniteCFG.packedTreeOutput (i.val, .pair .unit .unit)

/-- The actual compiled entry and local steps realize the guarded heads.
The encoder tracks the named label and its versioner's argument-plus-unit
packet. The step equation uses the ordered exit codec of the original
interface and compares full query trees, including the typed replies. -/
structure Corresponds (a : Admission P I fields source)
    (g : Table N R) (caller : Syntax.Payload (R.get g.entry)) (query : Query N E)
    (instr : Primitive E P.Instr α) (input : V × Nat → Value α)
    (result : TwoRequest.Tag → Transfer α := unitExit) where
  encode : Cursor R → K × Value α
  entry : a.versioned.source.entry.evalJump (treeModel instr) input =
    pure (encode (atBlock ⟨g.entry, caller⟩))
  localStep : ∀ c,
    (step g caller query result c >>= (liftPure (Sum.map id encode))) =
      mapReturn (CFG.Cyclic.stepSSA (treeModel instr) a.versioned.source.blocks input)
        (liftPure fun p => FiniteCFG.packedTreeOutput (treeExitNumber I.exits p)) (encode c)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
