module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Writer.Thms
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Presentation.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Uflia.SExpr
variable {E F : Environment}

abbrev Accepted := Uflia.Quantified.SExpr.Renaming.Presentation.Representative
abbrev Sentence := Uflia.Quantified.SExpr.Renaming.Presentation.Sentence

/-- Run the source transformer and writer on an actual accepted byte representative.
The full-grammar transport theorem supplies success, rather than assuming it. -/
def renameAccepted (f : NameMap E F) (a : Accepted E) : Accepted F :=
  ByteAccepted.rename a f (renameSentence_success f a.expression a.sentence a.decoded)

/-- Reuse the existing equality-of-decoded-sentences quotient. Representatives
retain the transformed quantifier/let tree and freshly rendered target bytes. -/
def mapSentence (f : NameMap E F) : Sentence E → Sentence F :=
  Quotient.map (renameAccepted f) (by
    intro a b h
    exact congrArg (Hom.quantifiedSentence f.abstract) h)

@[simp] theorem decode_map (f : NameMap E F) (s : Sentence E) :
    (mapSentence f s).decode = Hom.quantifiedSentence f.abstract s.decode := by
  refine Quotient.inductionOn s ?_
  intro a
  rfl

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
