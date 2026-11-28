module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.InstructionMap.Thms

/-! # Sentences with a common live-out interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut

open CategoryTheory
open Silmaril.Logic.Institution (Room)
open Silmaril.SSA.LambdaRTL
open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P Q : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {source : CFG V K P.Instr}

/-- Transport the admitted named table at its supplied block profiles.
The original source and its attached exits commute with relabelling. -/
def Admission.map (a : Admission P I fields source) (g : P ⟶ Q) :
    Admission Q I fields (source.mapOp g.toSignatureMap.instr) :=
  ⟨a.rtl.map g, (congrArg (CFG.mapOp g.toSignatureMap.instr) a.attached).trans
    (CFG.Cyclic.LiveOut.attach_mapOp g.toSignatureMap.instr (fun k => (fields k).map Prod.fst) source).symm⟩

/-- Keep the original named graph with its admission certificate. -/
structure Admitted (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) where
  source : CFG V K P.Instr
  certificate : Admission P I fields source

def Admitted.map (a : Admitted P I fields) (g : P ⟶ Q) : Admitted Q I fields :=
  ⟨a.source.mapOp g.toSignatureMap.instr, a.certificate.map g⟩

/-- The interface fixes the input record, exits, and ordered field lists
for both sides of a comparison. -/
abbrev Sentence (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) :=
  Admitted P I fields × Admitted P I fields

def Sentence.map (s : Sentence P I fields) (g : P ⟶ Q) : Sentence Q I fields :=
  (s.1.map g, s.2.map g)

def toRTL (s : Sentence P I fields) : RTLSentence P (exitInterface I fields) :=
  (s.1.certificate.rtl, s.2.certificate.rtl)

/-- Both written representatives come from the existing open flat packer. -/
def toPacked (s : Sentence P I fields) : PackedInstitution.Sentence P
    (Region.packedInputType I.context.toList) :=
  ⟨I.exits.length, (exitInterface I fields).external, s.1.certificate.program,
    s.2.certificate.program⟩

variable [AtomValues κ] {Events : Type u → Type u}

def Satisfies (M : Model (κ := κ) Events P.Instr) (s : Sentence P I fields) : Prop :=
  ∀ x, TraceLE (observe M I fields s.1.source x) (observe M I fields s.2.source x)

variable (I fields Events) in
/-- The live-out room uses the same models as the named typed-entry room. -/
def room (P : FlatInstitution.Signature.{u, v} κ) :
    Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  Sen := Sentence P I fields
  Mod := (rtlRoom (exitInterface I fields) Events P).Mod
  Sat M s := Satisfies M.as s

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut
