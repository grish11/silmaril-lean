module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Set.Image

@[expose] public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory Silmaril.Logic.TypeTheory.ExtensionalMLTT

variable {Name : Type}

/-- A resolved symbol declaration or transparent definition. Its expressions use
the slots of the preceding declarations. -/
structure NamedDecl (Name : Type) where
  name : Name
  type : ETm 0
  value : Option (ETm 0)

/-- An ordered signature of resolved declaration events. Typing is a separate
obligation. The wire adapter checks freshness and resolution before forming it. -/
structure Signature (Name : Type) where
  declarations : List (NamedDecl Name)

namespace Signature

/-- The slot used for a named constant in the MLTT context. -/
def symbolSlot (i : Nat) : String := "symbol:" ++ toString i

/-- A distinct context slot for the equation attached to a definition. -/
def equationSlot (i : Nat) : String := "equation:" ++ toString i

/-- Find the slot of exactly the given name in the declaration prefix. -/
def resolve? [DecidableEq Name] (S : Signature Name) (name : Name) :
    Option (Fin S.declarations.length) :=
  S.declarations.findFinIdx? (fun d => decide (d.name = name))

/-- A symbol contributes a context variable. A definition also contributes a
witness of its identity equation. The existing MLTT equality reflection rule
can use this equation, and distinct definitions retain distinct slots. -/
def context (S : Signature Name) : ECtx :=
  S.declarations.zipIdx.foldl (init := .nil) fun Γ (d, i) =>
    let Γ' := Γ.cons (symbolSlot i) d.type
    match d.value with
    | none => Γ'
    | some v => Γ'.cons (equationSlot i) (.id d.type (.fv (symbolSlot i)) v)

/-- The entire declaration context forms in extensional MLTT. In particular
each definition equation must form in context. -/
def WellTyped (S : Signature Name) : Prop := S.context.JEq .unit .star .star

/-- Signatures extend by appending events, retaining names, payloads and slots. -/
instance : Category.{0} (Signature Name) where
  Hom S T := PLift (S.declarations <+: T.declarations)
  id _ := ⟨⟨[], List.append_nil _⟩⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Turn a prefix inclusion into a signature morphism. -/
def ofPrefix {S T : Signature Name} (h : S.declarations <+: T.declarations) : S ⟶ T := ⟨h⟩

end Signature

/-- An additional named event asking that a value have a declared type. -/
structure SentenceEvent (Name : Type) where
  name : Name
  type : ETm 0
  value : ETm 0

/-- An event carries the declaration prefix in which its references were
resolved. Under extension the event continues to ask the judgment in that
prefix, so unrelated new declarations do not change its context. -/
structure Sentence (S : Signature Name) where
  scope : Signature Name
  included : scope ⟶ S
  event : SentenceEvent Name

namespace Sentence

variable {S T : Signature Name}

/-- A new event using the entire current signature. -/
def atSignature (S : Signature Name) (event : SentenceEvent Name) : Sentence S :=
  ⟨S, 𝟙 S, event⟩

/-- Transport an event along signature extension. -/
def weaken (f : S ⟶ T) (s : Sentence S) : Sentence T :=
  ⟨s.scope, s.included ≫ f, s.event⟩

/-- The extensional MLTT judgment for a resolved event. -/
def judgment (s : Sentence S) : EJdg :=
  ⟨s.scope.context, s.event.type, s.event.value, s.event.value⟩

@[simp] theorem judgment_weaken (f : S ⟶ T) (s : Sentence S) :
    (s.weaken f).judgment = s.judgment := rfl

@[simp] theorem weaken_id (s : Sentence S) : s.weaken (𝟙 S) = s := by
  cases s
  rfl

@[simp] theorem weaken_comp {U : Signature Name} (f : S ⟶ T) (g : T ⟶ U) (s : Sentence S) :
    s.weaken (f ≫ g) = (s.weaken f).weaken g := rfl

end Sentence

/-- Syntactic entailment is MLTT derivability from the translated judgment
hypotheses, in each event's own declaration context. -/
def Derives {S : Signature Name} (H : Set (Sentence S)) (s : Sentence S) : Prop :=
  s.judgment.Γ.JEqH (Sentence.judgment '' H) s.judgment.A s.judgment.a s.judgment.b

/-- Syntactic validity is typing without additional event hypotheses. -/
def Sentence.Valid {S : Signature Name} (s : Sentence S) : Prop := Derives ∅ s

end Silmaril.ProofFormats.LeanNDJSON.MLTT
