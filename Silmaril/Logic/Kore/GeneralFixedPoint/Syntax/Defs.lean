module

public import Silmaril.Logic.Kore.FixedPoint.Syntax.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint
inductive RawPattern where
  | evar (name sort : String)
  | svar (name sort : String)
  | domainValue (sort text : String)
  | app (name : String) (arguments : List RawPattern)
  | top (sort : String)
  | bottom (sort : String)
  | conj (sort : String) (left right : RawPattern)
  | disj (sort : String) (left right : RawPattern)
  | ex (sort name bound : String) (body : RawPattern)
  | all (sort name bound : String) (body : RawPattern)
  | mu (name sort : String) (body : RawPattern)
  | nu (name sort : String) (body : RawPattern)
  | neg (sort : String) (body : RawPattern)
  deriving Repr

namespace Syntax
open Operational.Text
abbrev ordinary := FixedPoint.Syntax.ordinary
def makeNode (name : String) (sorts : List String) (args : List RawPattern) :
    Option RawPattern :=
  match name, sorts, args with
  | "\\not", [s], [p] => some (.neg s p)
  | "\\implies", [s], [p, q] => some (.disj s (.neg s p) q)
  | "\\iff", [s], [p, q] =>
      some (.conj s (.disj s (.neg s p) q) (.disj s (.neg s q) p))
  | "\\top", [s], [] => some (.top s)
  | "\\bottom", [s], [] => some (.bottom s)
  | "\\and", [s], [p, q] => some (.conj s p q)
  | "\\or", [s], [p, q] => some (.disj s p q)
  | "\\exists", [s], [.evar n b, p] => some (.ex s n b p)
  | "\\forall", [s], [.evar n b, p] => some (.all s n b p)
  | "\\mu", [], [.svar n s, p] => some (.mu n s p)
  | "\\nu", [], [.svar n s, p] => some (.nu n s p)
  | _, [], args => if ordinary name then some (.app name args) else none
  | _, _, _ => none


abbrev pattern := FixedPoint.Syntax.patternWith (fun isSet name s =>
  if isSet then RawPattern.svar name s else RawPattern.evar name s) makeNode

def parse (text : String) : Option RawPattern := do
  let ts ← FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (p, rest) ← pattern (ts.length + 1) ts
  if rest.isEmpty then some p else none
end Syntax
end Silmaril.Logic.Kore.GeneralFixedPoint
