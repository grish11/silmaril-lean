module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Names.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Applications.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Operators.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory
open Uflia.SExpr (Environment Expr reserved numeral? lookup?)
open Uflia.Quantified.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}

export Uflia.Quantified.SExpr.Renaming (reserved_local_lookup_control
  reserved_local_decode_control simpleSymbol_not_numeral decodeAtomLocal
  decodeAtomGlobal decodeApplicationGlobal decodeAtom_eq)

/-- The target lexer reaches the actual mapped local value. -/
theorem selected_target_decode (f : NameMap E F) (fuel next : Nat)
    (locals : List (Local E Γ)) (valid : ValidScope F next locals)
    (name : String) (entry : Local E Γ) (selected : selected? locals name = some entry) :
    decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) (.atom entry.target) =
      some (mapPacked f.abstract entry.value) := by
  have member := selected_mem selected
  exact decodeAtomLocal fuel _ entry.target (valid.2.2.2 entry member).2 _
    (target_lookup_of_mem f.abstract valid.1 member)

theorem renameAtom_eq (f : NameMap E F) (fuel : Nat) (scope : Scope) (next : Nat) (name : String)
    (notTrue : name ≠ "true") (notFalse : name ≠ "false") :
    renameScopedFuel? f (fuel + 1) scope next (.atom name) =
      match localName? scope name with
      | some target => some (.atom target)
      | none => match numeral? (.atom name) with
        | some _ => some (.atom name)
        | none => (lookup? E name).bind (fun _ => some (.atom (f.rename name))) := by
  unfold renameScopedFuel?
  split <;> simp_all
  rfl

/-- Atom transport uses lexical selection before numerals and coherent globals. -/
theorem renameAtom_success (f : NameMap E F) (fuel next : Nat)
    (locals : List (Local E Γ)) (valid : ValidScope F next locals)
    (name : String) (value : PackedTerm E Γ)
    (decoded : decodeScopedFuel? E (fuel + 1) (sourceLocals locals) (.atom name) = some value) :
    ∃ output, renameScopedFuel? f (fuel + 1) (localScope locals) next (.atom name) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output =
        some (mapPacked f.abstract value) := by
  by_cases notTrue : name = "true"
  · subst name
    change some ⟨.bool, Uflia.Quantified.Term.boolean true⟩ = some value at decoded
    cases decoded
    refine ⟨.atom "true", rfl, ?_⟩
    simp only [decodeScopedFuel?, mapPacked_bool, boolTerm_boolean]
  by_cases notFalse : name = "false"
  · subst name
    change some ⟨.bool, Uflia.Quantified.Term.boolean false⟩ = some value at decoded
    cases decoded
    refine ⟨.atom "false", rfl, ?_⟩
    simp only [decodeScopedFuel?, mapPacked_bool, boolTerm_boolean]
  rw [decodeAtom_eq fuel _ name notTrue notFalse, selected_source] at decoded
  rw [renameAtom_eq f fuel _ next name notTrue notFalse]
  simp only [localName?]
  rw [selected_name]
  cases selected : selected? locals name with
  | some entry =>
    simp only [selected, Option.map_some] at decoded ⊢
    cases decoded
    exact ⟨.atom entry.target, rfl, selected_target_decode f fuel next locals valid name entry selected⟩
  | none =>
    simp only [selected, Option.map_none] at decoded ⊢
    cases numeral : numeral? (.atom name) with
    | some number =>
      simp only [numeral] at decoded ⊢
      cases decoded
      have unshadowed : Uflia.Quantified.SExpr.local? (targetLocals f.abstract locals) name = none := by
        apply target_lookup_none
        intro entry member same
        have nonliteral := simpleSymbol_not_numeral entry.target (valid.2.2.2 entry member).1
        rw [same, numeral] at nonliteral
        contradiction
      refine ⟨.atom name, rfl, ?_⟩
      rw [decodeAtom_eq fuel _ name notTrue notFalse, unshadowed, numeral]
      simp only [mapPacked_int, intTerm_integer]
    | none =>
      simp only [numeral] at decoded ⊢
      cases lookup : lookup? E name with
      | none => simp [applyUF?, lookup] at decoded
      | some index =>
        have targetLookup := f.lookup name index lookup
        have lexical := Uflia.SExpr.Renaming.lookup_lexical targetLookup
        refine ⟨.atom (f.rename name), rfl, ?_⟩
        rw [decodeAtomGlobal fuel _ _ lexical.2
          (Uflia.SExpr.Renaming.lookup_not_numeral targetLookup)
          (global_unshadowed f locals valid name index lookup)]
        exact uf_syntax f (.nil) name value decoded

/-- Actual global application syntax retains all argument positions, including
Boolean arguments with arbitrary quantified subexpressions. -/
theorem renameUFApplication_success (f : NameMap E F) (fuel next : Nat)
    (locals : List (Local E Γ)) (valid : ValidScope F next locals)
    (children : ∀ e value,
      decodeScopedFuel? E fuel (sourceLocals locals) e = some value → ∃ output,
        renameScopedFuel? f fuel (localScope locals) next e = some output ∧
          decodeScopedFuel? F fuel (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    (name : String) (es : List Expr) (nonempty : es ≠ [])
    (nonreserved : reserved.contains name = false)
    (unshadowed : Uflia.Quantified.SExpr.local? (sourceLocals locals) name = none)
    (value : PackedTerm E Γ)
    (decoded : applyUF? E (decodeScopedFuel? E fuel (sourceLocals locals)) name es = some value) :
    ∃ output, renameScopedFuel? f (fuel + 1) (localScope locals) next (.list (.atom name :: es)) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output = some (mapPacked f.abstract value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f.abstract _ _ _ children es
    (Uflia.Quantified.SExpr.Renaming.uf_source_exists _ name es value decoded)
  have outputsNonempty : outputs ≠ [] := by
    intro empty
    have lengths := Uflia.SExpr.Renaming.forall₂_length related
    rw [empty, List.length_nil] at lengths
    exact nonempty (List.length_eq_zero_iff.mp lengths)
  have scopeNone : localName? (localScope locals) name = none := by
    rw [selected_source] at unshadowed
    change Uflia.Quantified.SExpr.Renaming.localName? (localScope locals) name = none
    rw [selected_name]
    cases selected : selected? locals name <;> simp_all
  cases lookup : lookup? E name with
  | none => simp [applyUF?, lookup] at decoded
  | some index =>
    have targetLookup := f.lookup name index lookup
    have lexical := Uflia.SExpr.Renaming.lookup_lexical targetLookup
    refine ⟨.list (.atom (f.rename name) :: outputs), ?_, ?_⟩
    · unfold renameScopedFuel?
      split <;> simp_all [reserved]
    · rw [decodeApplicationGlobal fuel _ _ lexical.2 outputs outputsNonempty
        (global_unshadowed f locals valid name index lookup)]
      exact uf_syntax f related name value decoded

/-- The source application's lexical guard is preserved before global lookup. -/
theorem renameUFApplication_guard_success (f : NameMap E F) (fuel next : Nat)
    (locals : List (Local E Γ)) (valid : ValidScope F next locals)
    (children : ∀ e value,
      decodeScopedFuel? E fuel (sourceLocals locals) e = some value → ∃ output,
        renameScopedFuel? f fuel (localScope locals) next e = some output ∧
          decodeScopedFuel? F fuel (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    (name : String) (es : List Expr) (value : PackedTerm E Γ)
    (decoded : (if es.isEmpty || reserved.contains name || (Uflia.Quantified.SExpr.local? (sourceLocals locals) name).isSome
      then none else applyUF? E (decodeScopedFuel? E fuel (sourceLocals locals)) name es) = some value) :
    ∃ output, renameScopedFuel? f (fuel + 1) (localScope locals) next (.list (.atom name :: es)) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output = some (mapPacked f.abstract value) := by
  split at decoded
  · contradiction
  · rename_i guard
    have nonempty : es ≠ [] := by
      intro empty
      subst es
      simp at guard
    have nonreserved : reserved.contains name = false := by
      cases reserved : reserved.contains name <;> simp_all
    have unshadowed : Uflia.Quantified.SExpr.local? (sourceLocals locals) name = none := by
      cases found : Uflia.Quantified.SExpr.local? (sourceLocals locals) name <;> simp_all
    exact renameUFApplication_success f fuel next locals valid children name es nonempty
      nonreserved unshadowed value decoded

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
