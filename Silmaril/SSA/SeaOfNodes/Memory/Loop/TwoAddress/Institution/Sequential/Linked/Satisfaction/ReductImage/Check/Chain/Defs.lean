module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs

/-! Checked lifting along finite chains of typed capture maps. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution renaming Signature → EntrySignature

/-- The target signature of each capture map is the source of the next. -/
inductive CaptureChain : EntrySignature → EntrySignature → Type where
  | nil (P : EntrySignature) : CaptureChain P P
  | cons {P Q R : EntrySignature} (head : P ⟶ Q) (tail : CaptureChain Q R) : CaptureChain P R

namespace CaptureChain

variable {P Q R : EntrySignature} {cells : Nat}

def append : {P Q R : EntrySignature} → CaptureChain P Q → CaptureChain Q R → CaptureChain P R
  | _, _, _, .nil _, right => right
  | _, _, _, .cons head tail, right => .cons head (tail.append right)

def composite : {P Q : EntrySignature} → CaptureChain P Q → (P ⟶ Q)
  | _, _, .nil P => 𝟙 P
  | _, _, .cons head tail => head ≫ tail.composite

/-- Entries at every stage, including the initial and final signatures. -/
inductive Stages (cells : Nat) : {P Q : EntrySignature} → CaptureChain P Q → Type where
  | nil {P : EntrySignature} (entry : Entry P.args cells) : Stages cells (.nil P)
  | cons {P Q R : EntrySignature} {chain : CaptureChain Q R} {head : P ⟶ Q}
      (entry : Entry P.args cells) (tail : Stages cells chain) : Stages cells (.cons head chain)

def Stages.first : {P Q : EntrySignature} → {chain : CaptureChain P Q} → Stages cells chain → Entry P.args cells
  | _, _, _, .nil entry | _, _, _, .cons entry _ => entry

def Stages.last : {P Q : EntrySignature} → {chain : CaptureChain P Q} → Stages cells chain → Entry Q.args cells
  | _, _, _, .nil entry => entry
  | _, _, _, .cons _ tail => tail.last

def Stages.Compatible : {P Q : EntrySignature} → {chain : CaptureChain P Q} → Stages cells chain → Prop
  | _, _, _, .nil _ => True
  | _, _, .cons head _, .cons entry tail => tail.first.reduct head = entry ∧ tail.Compatible

/-- Recover each stage by the reduct of its successor, beginning at the final entry. -/
def pullStages : {P Q : EntrySignature} → (chain : CaptureChain P Q) → Entry Q.args cells → Stages cells chain
  | _, _, .nil _, target => .nil target
  | _, _, .cons head tail, target =>
    let stages := tail.pullStages target
    .cons (stages.first.reduct head) stages

/-- Run the checked lift once on the composite, then pull back from that final entry. -/
def lift? (chain : CaptureChain P Q) (source : Entry P.args cells) : Option (Stages cells chain) :=
  (liftInput? chain.composite source.input).map fun input => chain.pullStages ⟨input, source.heap⟩

def checkCoverage (chain : CaptureChain P Q) (cells : Nat) : Bool :=
  ReductImage.checkCoverage chain.composite cells

def diagnose? (chain : CaptureChain P Q) (cells : Nat) : Option (CoverageDiagnostic P Q cells) :=
  diagnoseCoverage? chain.composite cells

end CaptureChain
end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
