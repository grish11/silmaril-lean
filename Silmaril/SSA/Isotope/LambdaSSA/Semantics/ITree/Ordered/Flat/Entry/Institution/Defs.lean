module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Entry.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Packed.Institution.Thms

/-! # Ordered flat comparisons at a shared external entry context -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.EntryInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room)

universe u v

variable {κ : Type (u + 1)} {P Q : FlatInstitution.Signature.{u, v} κ}
  {n exits : Nat} {β : BoundCtx (Ty κ) n} {D : Fin exits → Ty κ}

local notation "A" => Region.packedInputType β.toList

/-- A table may access the exact shared entry context from the entry and
from any block. Each block also has its own payload type. -/
structure Table (P : FlatInstitution.Signature.{u, v} κ) (β : BoundCtx (Ty κ) n)
    (D : Fin exits → Ty κ) where
  blocks : Nat
  internal : Fin blocks → Ty κ
  code : FiniteCFG P.Instr blocks exits n
  typed : code.HasType β internal D

def Table.ofTyped {blocks : Nat} {R : Fin blocks → Ty κ} {a : FiniteCFG P.Instr blocks exits n}
    (ha : a.HasType β R D) : Table P β D :=
  ⟨blocks, R, a, ha⟩

def Table.map (a : Table P β D) (g : P ⟶ Q) : Table Q β D :=
  .ofTyped (a.typed.mapInstr (flatProfiles g.toSignatureMap g.types))

/-- A directed comparison at a common entry context and ordered exit profile. -/
structure Sentence (P : FlatInstitution.Signature.{u, v} κ) (β : BoundCtx (Ty κ) n) where
  exits : Nat
  external : Fin exits → Ty κ
  left : Table P β external
  right : Table P β external

def Sentence.map (s : Sentence P β) (g : P ⟶ Q) : Sentence Q β :=
  ⟨s.exits, s.external, s.left.map g, s.right.map g⟩

/-- The packed input type is the product of the context slots. Both sides
pack the actual written flat table. -/
def packSentence (s : Sentence P β) : PackedInstitution.Sentence P A :=
  ⟨s.exits, s.external, Program.ofCFGEntry s.left.typed, Program.ofCFGEntry s.right.typed⟩

variable [AtomValues κ] (Events : Type u → Type u)

/-- Compare the programs pointwise on the typed entry records. -/
def Satisfies (M : Model (κ := κ) Events P.Instr) (s : Sentence P β) : Prop :=
  M.Satisfies (Program.ofCFGEntry s.left.typed) (Program.ofCFGEntry s.right.typed)

def room (β : BoundCtx (Ty κ) n) (P : FlatInstitution.Signature.{u, v} κ) :
    Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  Sen := Sentence P β
  Mod := (FlatInstitution.room Events P).Mod
  Sat M s := Satisfies Events M.as s

def corridor (β : BoundCtx (Ty κ) n) (g : P ⟶ Q) : room Events β P ⟶ room Events β Q where
  sen s := s.map g
  mod := FlatInstitution.reductFunctor Events g
  sat M s := satisfies_ofCFGEntry_map_iff M.as g.toSignatureMap g.types g.bottom
    s.left.typed s.right.typed

def packingCorridor (β : BoundCtx (Ty κ) n) (P : FlatInstitution.Signature.{u, v} κ) :
    room Events β P ⟶ PackedInstitution.room Events P (Region.packedInputType β.toList) where
  sen := packSentence
  mod := 𝟭 _
  sat _ _ := Iff.rfl

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.EntryInstitution
