module

public import Silmaril.Courses.Cambridge.StepSpecification.Format
public import Silmaril.Courses.Cambridge.ReturnSpecification.Institution

/-! The canonical JSON and proper S-expression value formats for Cambridge
may-return specifications. Translations validate documents against the same
typed context before changing their representation. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.ReturnSpecification

open Silmaril.Formats
open Silmaril.Formats.Dasl.Encode (TotalCodec)
open AstCodec
open StepSpecification (Context Catalogue readSlot readSlot_repr)

def claimTree {slots : Nat} : Claim (Fin slots) → Tree
  | .mayReturn source => node "may-return" [.atom source.val.repr]
  | .mayReturnTo source target => node "may-return-to" [.atom source.val.repr, .atom target.val.repr]

def readClaim (slots : Nat) (tree : Tree) : Option (Claim (Fin slots)) :=
  match tree.children? with
  | some [.atom "may-return", .atom source] => (readSlot slots source).map .mayReturn
  | some [.atom "may-return-to", .atom source, .atom target] => do
    return .mayReturnTo (← readSlot slots source) (← readSlot slots target)
  | _ => none

@[simp] theorem readClaim_claimTree {slots : Nat} (claim : Claim (Fin slots)) :
    readClaim slots (claimTree claim) = some claim := by
  cases claim <;> simp [readClaim, claimTree, node]

def sentenceTree (context : Context) (sentence : Sentence context) : Tree :=
  node "cambridge-may-return-spec-v1" [.atom context.language.tag, .atom context.slots.repr,
    node "all" (sentence.map claimTree)]

def readSentence (context : Context) (tree : Tree) : Option (Sentence context) := do
  let some [.atom "cambridge-may-return-spec-v1", .atom language, .atom slots, body] :=
    tree.children? | none
  if language ≠ context.language.tag ∨ slots ≠ context.slots.repr then none else
    let some (.atom "all" :: claims) := body.children? | none
    claims.mapM (readClaim context.slots)

private theorem readClaims (context : Context) (sentence : Sentence context) :
    sentence.mapM (readClaim context.slots ∘ claimTree) = some sentence := by
  rw [show readClaim context.slots ∘ claimTree = some from funext readClaim_claimTree]
  induction sentence <;> simp [*]

theorem readSentence_sentenceTree (context : Context) (sentence : Sentence context) :
    readSentence context (sentenceTree context sentence) = some sentence := by
  simp [readSentence, sentenceTree, node, readClaims]

/-- The source of this codec is the typed sentence language. Its target is
a proper S-expression value, with literal string atoms. -/
def sexp (context : Context) : AstCodec.Codec (Sentence context) :=
  ⟨sentenceTree context, readSentence context, readSentence_sentenceTree context⟩

def json (context : Context) : TotalCodec (Sentence context) Lean.Json :=
  asJson (sexp context)

def jsonBytes (context : Context) : TotalCodec (Sentence context) Bytes :=
  AstCodec.JsonBytes.codec (sexp context)

def meaningSExp (context : Context) (catalogue : Catalogue context) (document : Tree) : Option Prop :=
  ((sexp context).decode? document).map (Holds context catalogue)

def meaningJson (context : Context) (catalogue : Catalogue context) (document : Lean.Json) :
    Option Prop :=
  ((json context).decode? document).map (Holds context catalogue)

def meaningBytes (context : Context) (catalogue : Catalogue context) (document : Bytes) :
    Option Prop :=
  ((jsonBytes context).decode? document).map (Holds context catalogue)

def jsonToSExp (context : Context) (document : Lean.Json) : Option Tree :=
  ((json context).decode? document).map (sexp context).encode

def sexpToJson (context : Context) (document : Tree) : Option Lean.Json :=
  ((sexp context).decode? document).map (json context).encode

/-- Translation preserves both the proposition and the absence of a
proposition on malformed input. -/
theorem jsonToSExp_meaning (context : Context) (catalogue : Catalogue context) (document : Lean.Json) :
    (jsonToSExp context document).bind (meaningSExp context catalogue) =
      meaningJson context catalogue document := by
  cases decoded : (json context).decode? document <;>
    simp [jsonToSExp, meaningSExp, meaningJson, decoded, (sexp context).recovers]

theorem sexpToJson_meaning (context : Context) (catalogue : Catalogue context) (document : Tree) :
    (sexpToJson context document).bind (meaningJson context catalogue) =
      meaningSExp context catalogue document := by
  cases decoded : (sexp context).decode? document <;>
    simp [sexpToJson, meaningSExp, meaningJson, decoded, (json context).recovers]

end Silmaril.Courses.Cambridge.ReturnSpecification
