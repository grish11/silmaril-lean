module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Core.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Legality.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Normalization.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open Uflia.SExpr Silmaril.Logic.Smt.SExpr.Writer
variable {E F : Environment}

/-- Coherent target lookup makes the actual renamed global name lexer-safe. -/
theorem NameMap.globalName_legal (f : NameMap E F) (name : String)
    (hname : LegalAtom name) : LegalAtom (Uflia.SExpr.Renaming.globalName E f.rename name) := by
  unfold Uflia.SExpr.Renaming.globalName
  cases hi : lookup? E name with
  | none => exact hname
  | some i =>
      exact Uflia.SExpr.Renaming.simpleSymbol_legalAtom _
        (Uflia.SExpr.Renaming.lookup_lexical (f.lookup name i hi)).1

/-- The existing executable normalizer needs no sort-specific writer proof. -/
theorem normalize_legal (f : NameMap E F) (e output : Expr) (he : LegalExpr e)
    (h : Uflia.SExpr.Renaming.normalize? E f.rename e = some output) : LegalExpr output :=
  Uflia.SExpr.Renaming.normalizeFuel_legal_of_names f.rename f.globalName_legal
    (expressionFuel e) [] e output he (by simp) h

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
