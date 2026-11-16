module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Applications
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Normalization.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}

/-- Open scopes containing reserved target names are not admissible invariants:
the Boolean literal dispatch wins even when a differently sorted local exists. -/
theorem reserved_local_lookup_control :
    SExpr.local? [("true", (⟨.int, Term.integer 0⟩ : PackedTerm E Γ))] "true" =
      some ⟨.int, Term.integer 0⟩ := by rfl

theorem reserved_local_decode_control (fuel : Nat) :
    decodeScopedFuel? E (fuel + 1)
      [("true", (⟨.int, Term.integer 0⟩ : PackedTerm E Γ))] (.atom "true") =
      some ⟨.bool, Term.boolean true⟩ := by rfl

/-- Lexically admitted local names cannot be decimal literals. -/
theorem simpleSymbol_not_numeral (name : String) (simple : simpleSymbol name = true) :
    numeral? (.atom name) = none := by
  cases numeral : naturalNumeral? name with
  | none => simp only [numeral?, numeral, Option.map_none]
  | some value =>
    have invalid := Uflia.SExpr.Renaming.naturalNumeral_not_simpleSymbol numeral
    rw [simple] at invalid
    contradiction

/-- A selected local reaches lookup before any numeral or global fallback. -/
theorem decodeAtomLocal (fuel : Nat) (locals : SExpr.Locals E Γ) (name : String)
    (nonreserved : reserved.contains name = false) (value : PackedTerm E Γ)
    (lookup : SExpr.local? locals name = some value) :
    decodeScopedFuel? E (fuel + 1) locals (.atom name) = some value := by
  unfold decodeScopedFuel?
  split <;> simp_all [reserved]

/-- Legal nonliteral global spellings reach the actual UF decoder in any scope. -/
theorem decodeAtomGlobal (fuel : Nat) (locals : SExpr.Locals E Γ) (name : String)
    (nonreserved : reserved.contains name = false)
    (nonliteral : numeral? (.atom name) = none)
    (unshadowed : SExpr.local? locals name = none) :
    decodeScopedFuel? E (fuel + 1) locals (.atom name) =
      applyUF? E (decodeScopedFuel? E fuel locals) name [] := by
  unfold decodeScopedFuel?
  split <;> simp_all [reserved]

/-- Nonreserved global application heads reach UF decoding in arbitrary scopes. -/
theorem decodeApplicationGlobal (fuel : Nat) (locals : SExpr.Locals E Γ) (name : String)
    (nonreserved : reserved.contains name = false) (es : List Expr) (nonempty : es ≠ [])
    (unshadowed : SExpr.local? locals name = none) :
    decodeScopedFuel? E (fuel + 1) locals (.list (.atom name :: es)) =
      applyUF? E (decodeScopedFuel? E fuel locals) name es := by
  unfold decodeScopedFuel?
  split <;> simp_all [reserved]

/-- The target lexer cannot reinterpret a mapped local as a Boolean literal. -/
theorem selected_target_decode (f : NameMap E F) (fuel next : Nat)
    (locals : List (Local E Γ)) (valid : ValidScope F next locals)
    (name : String) (entry : Local E Γ) (selected : selected? locals name = some entry) :
    decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) (.atom entry.target) =
      some (mapPacked f.abstract entry.value) := by
  have member := selected_mem selected
  exact decodeAtomLocal fuel _ entry.target (valid.2.2.2 entry member).2 _
    (target_lookup_of_mem f.abstract valid.1 member)

@[simp] theorem map_boolean (f : E.signature ⟶ F.signature) (value : Bool) :
    (Term.boolean (A := E.signature) (Γ := Γ) value).map f = Term.boolean value := by
  simp only [Term.boolean, Term.map, Operation.map]
  congr 1
  funext i
  exact i.elim0

theorem decodeAtom_eq (fuel : Nat) (locals : SExpr.Locals E Γ) (name : String)
    (notTrue : name ≠ "true") (notFalse : name ≠ "false") :
    decodeScopedFuel? E (fuel + 1) locals (.atom name) =
      match SExpr.local? locals name with
      | some value => some value
      | none => match numeral? (.atom name) with
        | some n => some ⟨.int, Term.integer n⟩
        | none => applyUF? E (decodeScopedFuel? E fuel locals) name [] := by
  unfold decodeScopedFuel?
  split <;> simp_all
  rfl

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
    change some ⟨.bool, Term.boolean true⟩ = some value at decoded
    cases decoded
    refine ⟨.atom "true", rfl, ?_⟩
    simp only [decodeScopedFuel?, mapPacked, map_boolean]
  by_cases notFalse : name = "false"
  · subst name
    change some ⟨.bool, Term.boolean false⟩ = some value at decoded
    cases decoded
    refine ⟨.atom "false", rfl, ?_⟩
    simp only [decodeScopedFuel?, mapPacked, map_boolean]
  rw [decodeAtom_eq fuel _ name notTrue notFalse, selected_source] at decoded
  rw [renameAtom_eq f fuel _ next name notTrue notFalse, selected_name]
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
      have unshadowed : SExpr.local? (targetLocals f.abstract locals) name = none := by
        apply target_lookup_none
        intro entry member same
        have nonliteral := simpleSymbol_not_numeral entry.target (valid.2.2.2 entry member).1
        rw [same, numeral] at nonliteral
        contradiction
      refine ⟨.atom name, rfl, ?_⟩
      rw [decodeAtom_eq fuel _ name notTrue notFalse, unshadowed, numeral]
      simp only [mapPacked, map_integer]
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
    (unshadowed : SExpr.local? (sourceLocals locals) name = none)
    (value : PackedTerm E Γ)
    (decoded : applyUF? E (decodeScopedFuel? E fuel (sourceLocals locals)) name es = some value) :
    ∃ output, renameScopedFuel? f (fuel + 1) (localScope locals) next (.list (.atom name :: es)) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output = some (mapPacked f.abstract value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f.abstract _ _ _ children es
    (uf_source_exists _ name es value decoded)
  have outputsNonempty : outputs ≠ [] := by
    intro empty
    have lengths := Uflia.SExpr.Renaming.forall₂_length related
    rw [empty, List.length_nil] at lengths
    exact nonempty (List.length_eq_zero_iff.mp lengths)
  have scopeNone : localName? (localScope locals) name = none := by
    rw [selected_source] at unshadowed
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
    (decoded : (if es.isEmpty || reserved.contains name || (SExpr.local? (sourceLocals locals) name).isSome
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
    have unshadowed : SExpr.local? (sourceLocals locals) name = none := by
      cases found : SExpr.local? (sourceLocals locals) name <;> simp_all
    exact renameUFApplication_success f fuel next locals valid children name es nonempty
      nonreserved unshadowed value decoded

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
