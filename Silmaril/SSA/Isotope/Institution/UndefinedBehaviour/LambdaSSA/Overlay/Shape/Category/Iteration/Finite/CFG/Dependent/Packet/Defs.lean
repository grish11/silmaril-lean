module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs

/-! # Dependent positional packets and native sum tags -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Syntax
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)

/-- Label position and payload are stored together. Equal types at distinct
positions still define distinct alternatives. -/
abbrev Packet (L : List Syntax.Ty) := Σ i : Fin L.length, Payload (L.get i)

abbrev Packed (L : List Syntax.Ty) := Payload (packedExitType L)

def pack : {L : List Syntax.Ty} → Packet L → Packed L
  | [], ⟨i, _⟩ => i.elim0
  | A :: L, ⟨i, a⟩ =>
    Fin.cases (motive := fun j => Payload ((A :: L).get j) → Packed (A :: L))
      (fun b => ⟨.inl b.val, .inl b.property⟩)
      (fun j b => let p := pack (L := L) ⟨j, b⟩; ⟨.inr p.val, .inr p.property⟩) i a

def unpack : {L : List Syntax.Ty} → Packed L → Packet L
  | [], a => (noEmptyPayload a).elim
  | _ :: L, a =>
    match splitPayload a with
    | .inl b => ⟨0, b⟩
    | .inr tail =>
      let p := unpack (L := L) tail
      ⟨p.1.succ, p.2⟩

/-- Drop the typing proof and retain the ordered label. -/
def Packet.raw {L : List Syntax.Ty} (p : Packet L) : Fin L.length × Value Unit :=
  (p.1, p.2.val)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
