module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Operators

/-! Actual child syntax and mapped constructor results at the caller's fixed
recursive decoder, in arbitrary typed open contexts. -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment} (f : E.signature ⟶ F.signature)
variable {k : Nat} {Γ : Fin k → SortCode String}

/-- A successful constructor returns its actual renamed children and mapped value. -/
theorem renameUnary_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (a : Expr) (value : PackedTerm E Γ)
    (decoded : unary? source op a = some value) :
    ∃ a', [a].mapM rename = some [a'] ∧
      unary? target (Operation.map f op) a' = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    [a] (unary_source_exists source op a value decoded)
  cases related with
  | cons ha related =>
      cases related
      refine ⟨_, renamed, ?_⟩
      exact unary_syntax f op a _ ha value decoded

/-- A successful constructor returns its actual renamed children and mapped value. -/
theorem renameImplication_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (a b : Expr) (value : PackedTerm E Γ)
    (decoded : implication? source a b = some value) :
    ∃ a' b', [a, b].mapM rename = some [a', b'] ∧
      implication? target a' b' = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    [a, b] (implication_source_exists source a b value decoded)
  cases related with
  | cons ha related =>
      cases related with
      | cons hb related =>
          cases related
          refine ⟨_, _, renamed, ?_⟩
          exact implication_syntax f a _ b _ ha hb value decoded

/-- A successful constructor returns its actual renamed children and mapped value. -/
theorem renameXor_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (a b : Expr) (value : PackedTerm E Γ)
    (decoded : xor? source a b = some value) :
    ∃ a' b', [a, b].mapM rename = some [a', b'] ∧
      xor? target a' b' = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    [a, b] (xor_source_exists source a b value decoded)
  cases related with
  | cons ha related =>
      cases related with
      | cons hb related =>
          cases related
          refine ⟨_, _, renamed, ?_⟩
          exact xor_syntax f a _ b _ ha hb value decoded

/-- A successful constructor returns its actual renamed children and mapped value. -/
theorem renameIte_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (c a b : Expr) (value : PackedTerm E Γ)
    (decoded : ite? source c a b = some value) :
    ∃ c' a' b', [c, a, b].mapM rename = some [c', a', b'] ∧
      ite? target c' a' b' = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    [c, a, b] (ite_source_exists source c a b value decoded)
  cases related with
  | cons hc related =>
      cases related with
      | cons ha related =>
          cases related with
          | cons hb related =>
              cases related
              refine ⟨_, _, _, renamed, ?_⟩
              exact ite_syntax f c _ a _ b _ hc ha hb value decoded

/-- Successful list elaboration retains ordered transformed syntax and the mapped value. -/
theorem renameFold_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (value : PackedTerm E Γ)
    (decoded : fold? source op es = some value) :
    ∃ outputs, es.mapM rename = some outputs ∧
      fold? target (Operation.map f op) outputs = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    es (fold_source_exists source op es value decoded)
  exact ⟨outputs, renamed, fold_syntax f op related value decoded⟩

/-- Successful list elaboration retains ordered transformed syntax and the mapped value. -/
theorem renameCompare_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (es : List Expr) (value : PackedTerm E Γ)
    (decoded : compare? source op reverse es = some value) :
    ∃ outputs, es.mapM rename = some outputs ∧
      compare? target (Operation.map f op) reverse outputs = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    es (compare_source_exists source op reverse es value decoded)
  exact ⟨outputs, renamed, compare_syntax f op reverse related value decoded⟩

/-- Successful list elaboration retains ordered transformed syntax and the mapped value. -/
theorem renameEqualities_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (distinct : Bool)
    (es : List Expr) (value : PackedTerm E Γ)
    (decoded : equalities? source distinct es = some value) :
    ∃ outputs, es.mapM rename = some outputs ∧
      equalities? target distinct outputs = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    es (equalities_source_exists source distinct es value decoded)
  exact ⟨outputs, renamed, equalities_syntax f distinct related value decoded⟩

/-- Successful list elaboration retains ordered transformed syntax and the mapped value. -/
theorem renameMultiply_result
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (es : List Expr) (value : PackedTerm E Γ)
    (decoded : multiply? source es = some value) :
    ∃ outputs, es.mapM rename = some outputs ∧
      multiply? target outputs = some (mapPacked f value) := by
  obtain ⟨outputs, renamed, related⟩ := renameChildren_success f source target rename children
    es (multiply_source_exists source es value decoded)
  exact ⟨outputs, renamed, multiply_syntax f related value decoded⟩

/-- Ordinary builtin applications retain their operator spelling and the actual
renamed child list; binder forms are handled separately. -/
theorem renameBuiltin_success (f : NameMap E F) (fuel : Nat) (scope : Scope)
    (next : Nat) (name : String) (builtin : reserved.contains name = true)
    (notForall : name ≠ "forall") (notExists : name ≠ "exists") (notLet : name ≠ "let")
    (es outputs : List Expr)
    (renamed : es.mapM (renameScopedFuel? f fuel scope next) = some outputs) :
    renameScopedFuel? f (fuel + 1) scope next (.list (.atom name :: es)) =
      some (.list (.atom name :: outputs)) := by
  unfold renameScopedFuel?
  split <;> simp_all

/-- Successful folded elaboration requires at least two raw operands. -/
theorem fold_length (source : Expr → Option (PackedTerm E Γ))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (value : PackedTerm E Γ) (decoded : fold? source op es = some value) :
    2 ≤ es.length := by
  cases es with
  | nil => simp [fold?] at decoded
  | cons a es =>
      cases es with
      | nil => simp [fold?] at decoded
      | cons b rest => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))

/-- Binary-or-longer subtraction selects the fold branch in any typed context. -/
theorem decodeSubtract_fold (fuel : Nat) (locals : Locals E Γ) (es : List Expr)
    (hlength : 2 ≤ es.length) :
    decodeScopedFuel? E (fuel + 1) locals (.list (.atom "-" :: es)) =
      fold? (decodeScopedFuel? E fuel locals) .sub es := by
  cases es with
  | nil => contradiction
  | cons a es =>
      cases es with
      | nil => contradiction
      | cons b rest => rfl

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
