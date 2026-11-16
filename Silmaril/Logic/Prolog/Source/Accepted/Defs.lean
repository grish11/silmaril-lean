module

public import Silmaril.Logic.Prolog.Source.Parser.Defs
public import Silmaril.Logic.Prolog.Source.Denotation.Thms

@[expose] public section
namespace Silmaril.Logic.Prolog.Source
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Exact text accepted as one complete sentence and resolved in the stated
finite vocabulary. Parser and resolver evidence remain attached to the text. -/
structure AcceptedSentence (V : Vocabulary) where
  source : String
  parsed : NamedSentence
  parse_eq : Parser.parseSentence? source = some parsed
  resolved : Sentence V
  resolve_eq : resolveSentence? V parsed = some resolved

/-- Acceptance executes both readers; it does not assume success of resolution. -/
def acceptSentence? (V : Vocabulary) (source : String) : Option (AcceptedSentence V) :=
  match hp : Parser.parseSentence? source with
  | none => none
  | some parsed =>
    match hr : resolveSentence? V parsed with
    | none => none
    | some resolved => some ⟨source, parsed, hp, resolved, hr⟩

/-- Satisfaction is direct named-tree semantics of the parsed source. -/
def AcceptedSentence.Holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (s : AcceptedSentence V) : Prop := s.parsed.Holds M

theorem AcceptedSentence.resolved_holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (s : AcceptedSentence V) : s.resolved.Holds M ↔ s.Holds M :=
  resolveSentence_holds M s.parsed s.resolved s.resolve_eq

theorem AcceptedSentence.encode_holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (s : AcceptedSentence V) : s.resolved.encode.Holds M ↔ s.Holds M :=
  (s.resolved.encode_holds M).trans (s.resolved_holds M)

def sourceRoom (V : Vocabulary) : Room.{0,0,1} :=
  ⟨AcceptedSentence V, Cat.of (FOL.Structure V.signature), fun M s => s.Holds M⟩

/-- Forget the acceptance receipt while retaining the whole public model category. -/
def sourceToNative (V : Vocabulary) : sourceRoom V ⟶ nativeRoom V :=
  ⟨AcceptedSentence.resolved, 𝟭 _, fun M s => s.resolved_holds M⟩

/-- The text receipt and independent interpretation agree with the existing
public definite first-order semantics on every structure. -/
def sourceToDefinite (V : Vocabulary) : sourceRoom V ⟶ Definite.room V.signature :=
  ⟨fun s => s.resolved.encode, 𝟭 _, fun M s => s.encode_holds M⟩

theorem sourceToDefinite_modelExpansive (V : Vocabulary) :
    (sourceToDefinite V).ModelExpansive := fun M => ⟨M, rfl⟩

end Silmaril.Logic.Prolog.Source
