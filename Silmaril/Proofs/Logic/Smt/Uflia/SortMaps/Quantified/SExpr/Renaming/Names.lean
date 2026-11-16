module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Core.Thms
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Thms

/-! Reuse the original lexical records and freshness invariant. Only the target
values change: they live in the actual mapped context and computed sorts. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Uflia.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}

export Uflia.Quantified.SExpr.Renaming
  (Local sourceLocals localScope selected? selected_source selected_name selected_mem ValidScope weakenLocal valid_weaken valid_fresh_cons freshName_length freshName_injective freshName_simple freshName_not_reserved freshName_legal declaration_lt_firstFresh localScope_weaken sourceLocals_weaken pushBinder sourceLocals_pushBinder pushBinder_valid binderScope)

namespace Local
export Uflia.Quantified.SExpr.Renaming.Local (source target value)
end Local

def targetLocals (f : environmentSignature E ⟶ environmentSignature F)
    (locals : List (Local E Γ)) : Uflia.Quantified.SExpr.Locals F (f.sorts ∘ Γ) :=
  locals.map (fun entry => (entry.target, mapPacked f entry.value))

theorem target_lookup_of_mem (f : environmentSignature E ⟶ environmentSignature F)
    {locals : List (Local E Γ)} (distinct : (locals.map Local.target).Nodup)
    {entry : Local E Γ} (member : entry ∈ locals) :
    Uflia.Quantified.SExpr.local? (targetLocals f locals) entry.target = some (mapPacked f entry.value) := by
  induction locals with
  | nil => cases member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with same | member
    · subst entry
      simp [targetLocals, Uflia.Quantified.SExpr.local?]
    · have different : first.target ≠ entry.target := by
        intro same
        apply distinct.1
        exact List.mem_map.mpr ⟨entry, member, same.symm⟩
      simp only [targetLocals, List.map_cons, Uflia.Quantified.SExpr.local?, different, ↓reduceIte]
      exact ih distinct.2 member

theorem lookup_commute (f : environmentSignature E ⟶ environmentSignature F)
    (locals : List (Local E Γ)) (distinct : (locals.map Local.target).Nodup) (name : String) :
    (localName? (localScope locals) name).bind (Uflia.Quantified.SExpr.local? (targetLocals f locals)) =
      (Uflia.Quantified.SExpr.local? (sourceLocals locals) name).map (mapPacked f) := by
  change (Uflia.Quantified.SExpr.Renaming.localName? (localScope locals) name).bind _ = _
  rw [selected_name, selected_source]
  cases selected : selected? locals name with
  | none => rfl
  | some entry => exact target_lookup_of_mem f distinct (selected_mem selected)

theorem target_lookup_none (f : environmentSignature E ⟶ environmentSignature F)
    (locals : List (Local E Γ)) (name : String)
    (absent : ∀ entry ∈ locals, entry.target ≠ name) :
    Uflia.Quantified.SExpr.local? (targetLocals f locals) name = none := by
  induction locals with
  | nil => rfl
  | cons entry rest ih =>
    simp only [targetLocals, List.map_cons, Uflia.Quantified.SExpr.local?, absent entry (by simp), ↓reduceIte]
    apply ih
    intro other member
    exact absent other (List.mem_cons_of_mem _ member)

theorem global_unshadowed (f : NameMap E F) {next : Nat} (locals : List (Local E Γ))
    (valid : ValidScope F next locals) (name : String) (i : Fin E.declarations.length)
    (lookup : lookup? E name = some i) :
    Uflia.Quantified.SExpr.local? (targetLocals f.abstract locals) (f.rename name) = none := by
  have targetName := f.targetName name i lookup
  have declaration_mem : F.declarations.get
      (Uflia.SExpr.Renaming.symbolIndex (f.abstract.operations (.declared i))) ∈ F.declarations :=
    List.get_mem _ _
  have absent : ∀ entry ∈ locals, entry.target ≠ f.rename name := by
    intro entry member
    rw [← targetName]
    exact valid.2.2.1 entry member _ declaration_mem
  exact target_lookup_none f.abstract locals (f.rename name) absent

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
