module

public import Silmaril.Courses.Cambridge.AstCodec.JsonBytes
public import Silmaril.Courses.Cambridge.StepSpecification.Institution

/-! The canonical constructor-tree and JSON value formats for step
specifications. Parsing checks names against the declared context. The
catalogue of full configurations is supplied when interpreting a sentence. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.StepSpecification

open Silmaril.Formats
open Silmaril.Formats.Dasl.Encode (TotalCodec)
open Silmaril.Courses.Cambridge.AstCodec

def Language.tag : Language → String
  | .l1 => "L1"
  | .l2 => "L2"
  | .l3 => "L3"

def readSlot (slots : Nat) (text : String) : Option (Fin slots) := do
  let index ← readNat text
  if h : index < slots then some ⟨index, h⟩ else none

@[simp] theorem readSlot_repr {slots : Nat} (index : Fin slots) :
    readSlot slots index.val.repr = some index := by
  simp [readSlot, index.isLt]

def stepTree (context : Context) (edge : context.shape.Edge) : Tree :=
  node "step" [.atom edge.1.val.repr, .atom edge.2.2.val.repr]

def readStep (context : Context) (tree : Tree) : Option context.shape.Edge := do
  let some [.atom "step", .atom source, .atom target] := tree.children? | none
  return (← readSlot context.slots source, (), ← readSlot context.slots target)

@[simp] theorem readStep_stepTree (context : Context) (edge : context.shape.Edge) :
    readStep context (stepTree context edge) = some edge := by
  rcases edge with ⟨source, ⟨⟩, target⟩
  simp [readStep, stepTree, node]

def sentenceTree (context : Context) (sentence : Sentence context) : Tree :=
  node "cambridge-step-spec-v1" [.atom context.language.tag, .atom context.slots.repr,
    node "all" (sentence.map (stepTree context))]

def readSentence (context : Context) (tree : Tree) : Option (Sentence context) := do
  let some [.atom "cambridge-step-spec-v1", .atom language, .atom slots, body] :=
    tree.children? | none
  if language ≠ context.language.tag ∨ slots ≠ context.slots.repr then none else
    let some (.atom "all" :: clauses) := body.children? | none
    clauses.mapM (readStep context)

private theorem readSteps (context : Context) (sentence : Sentence context) :
    sentence.mapM (readStep context ∘ stepTree context) = some sentence := by
  rw [show readStep context ∘ stepTree context = some from funext (readStep_stepTree context)]
  induction sentence <;> simp [*]

theorem readSentence_sentenceTree (context : Context) (sentence : Sentence context) :
    readSentence context (sentenceTree context sentence) = some sentence := by
  simp [readSentence, sentenceTree, node, readSteps]

def treeCodec (context : Context) : AstCodec.Codec (Sentence context) :=
  ⟨sentenceTree context, readSentence context, readSentence_sentenceTree context⟩

def json (context : Context) : TotalCodec (Sentence context) Lean.Json :=
  asJson (treeCodec context)

/-- Malformed documents have no proposition. A decoded document has the
proposition that its course model satisfies the translated specification. -/
def meaning (context : Context) (catalogue : Catalogue context) (document : Lean.Json) :
    Option Prop :=
  ((json context).decode? document).map (Holds context catalogue)

theorem meaning_encode (context : Context) (catalogue : Catalogue context)
    (sentence : Sentence context) :
    meaning context catalogue ((json context).encode sentence) =
      some (Holds context catalogue sentence) := by
  unfold meaning
  rw [(json context).recovers]
  rfl

/-- The same structured schema read and written as canonical UTF-8 JSON. -/
def jsonBytes (context : Context) : TotalCodec (Sentence context) Bytes :=
  AstCodec.JsonBytes.codec (treeCodec context)

def meaningBytes (context : Context) (catalogue : Catalogue context) (document : Bytes) :
    Option Prop :=
  ((jsonBytes context).decode? document).map (Holds context catalogue)

theorem meaningBytes_encode (context : Context) (catalogue : Catalogue context)
    (sentence : Sentence context) :
    meaningBytes context catalogue ((jsonBytes context).encode sentence) =
      some (Holds context catalogue sentence) := by
  unfold meaningBytes
  rw [(jsonBytes context).recovers]
  rfl

end Silmaril.Courses.Cambridge.StepSpecification
