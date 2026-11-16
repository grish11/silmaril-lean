module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Syntax.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Thms

/-! Coherent source names for actual varying-sort signature maps. Decoder
commutation is a theorem obligation, never a field of this structure. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
open Uflia.SExpr

/-- The actual typed signature selected by a declaration environment. -/
abbrev environmentSignature (E : Environment) : SortMaps.Signature := ⟨String, E.signature⟩

/-- Names select exactly the declarations supplied by the typed signature map.
User sorts may be identified or instantiated by Bool or Int. -/
structure NameMap (E F : Environment) where
  rename : String → String
  abstract : environmentSignature E ⟶ environmentSignature F
  lookup : ∀ (name : String) (i : Fin E.declarations.length),
    lookup? E name = some i →
    lookup? F (rename name) = some
      (Uflia.SExpr.Renaming.symbolIndex (abstract.operations (.declared i)))
  targetName : ∀ (name : String) (i : Fin E.declarations.length),
    lookup? E name = some i →
    (F.declarations.get
      (Uflia.SExpr.Renaming.symbolIndex (abstract.operations (.declared i)))).name = rename name

/-- Remove the transported empty-context cast while retaining the mapped sort. -/
def closedTerm {E F : Environment}
    (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (t : Uflia.Term E.signature s) :
    Uflia.Term F.signature (f.sorts s) :=
  cast (congrArg (fun Γ => ManySorted.Term F.signature.expanded Γ (f.sorts s))
    (Hom.sorts_empty f)) (Hom.term f t)

/-- Packed transport changes the computed sort as well as the typed term. -/
def mapPacked {E F : Environment}
    (f : environmentSignature E ⟶ environmentSignature F) (t : PackedTerm E) : PackedTerm F :=
  ⟨f.sorts t.sort, closedTerm f t.term⟩

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
