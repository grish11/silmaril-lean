module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Atoms.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Lets.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.BinderSemantics.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Results.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory
open Uflia.SExpr (Environment Expr)
open Uflia.Quantified.SExpr
variable {E F : Environment}

/-- Successful source decoding commutes with the actual capture-safe traversal,
at the same recursion budget and in every valid typed lexical scope. -/
theorem renameScoped_success (f : NameMap E F) (fuel : Nat) :
    ∀ {k : Nat} {Γ : Fin k → SortCode String} (locals : List (Local E Γ)) (next : Nat),
      ValidScope F next locals → firstFresh F ≤ next → ∀ expression value,
      decodeScopedFuel? E fuel (sourceLocals locals) expression = some value →
      ∃ output, renameScopedFuel? f fuel (localScope locals) next expression = some output ∧
        decodeScopedFuel? F fuel (targetLocals f.abstract locals) output = some (mapPacked f.abstract value) := by
  induction fuel with
  | zero =>
    intro k Γ locals next valid bound expression value decoded
    cases decoded
  | succ fuel ih =>
    intro k Γ locals next valid bound expression value decoded
    cases expression with
    | atom name => exact renameAtom_success f fuel next locals valid name value decoded
    | list es =>
      unfold decodeScopedFuel? at decoded
      split at decoded <;> simp_all only [Silmaril.Logic.Smt.SE.list.injEq, reduceCtorEq]
      all_goals subst es
      · change (binders? E (_ :: _)).bind _ = some value at decoded
        obtain ⟨parsed, parsedBinders, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        exact renameQuantifier_success f fuel ih locals next valid bound true _ _ parsed parsedBinders _ value decoded
      · change (binders? E (_ :: _)).bind _ = some value at decoded
        obtain ⟨parsed, parsedBinders, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        exact renameQuantifier_success f fuel ih locals next valid bound false _ _ parsed parsedBinders _ value decoded
      · change (letBindings? (decodeScopedFuel? E fuel (sourceLocals locals)) (_ :: _)).bind _ = some value at decoded
        obtain ⟨values, parsedBindings, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        exact renameLet_success f fuel (fun locals next => ih locals next) locals next valid bound _ _ values parsedBindings _ value decoded
      · obtain ⟨a', renamed, mapped⟩ := renameUnary_at_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) f.abstract.bool f.abstract.bool .not .not (operation_not_heq f.abstract) _ value decoded
        refine ⟨.list [.atom "not", a'], renameBuiltin_success f fuel (localScope locals) next
          "not" (by decide) (by decide) (by decide) (by decide) [_] [a'] renamed, ?_⟩
        exact mapped
      · obtain ⟨a', renamed, mapped⟩ := renameUnary_at_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) f.abstract.int f.abstract.int (.scale (-1)) (.scale (-1)) (operation_scale_heq f.abstract (-1)) _ value decoded
        refine ⟨.list [.atom "-", a'], renameBuiltin_success f fuel (localScope locals) next
          "-" (by decide) (by decide) (by decide) (by decide) [_] [a'] renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameFold_at_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) f.abstract.bool .and .and (operation_and_heq f.abstract) _ value decoded
        refine ⟨.list (.atom "and" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "and" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameFold_at_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) f.abstract.bool .or .or (operation_or_heq f.abstract) _ value decoded
        refine ⟨.list (.atom "or" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "or" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨a', b', renamed, mapped⟩ := renameImplication_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound)  _ _ value decoded
        refine ⟨.list [.atom "=>", a', b'], renameBuiltin_success f fuel (localScope locals) next
          "=>" (by decide) (by decide) (by decide) (by decide) [_, _] [a', b'] renamed, ?_⟩
        exact mapped
      · obtain ⟨a', b', renamed, mapped⟩ := renameXor_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound)  _ _ value decoded
        refine ⟨.list [.atom "xor", a', b'], renameBuiltin_success f fuel (localScope locals) next
          "xor" (by decide) (by decide) (by decide) (by decide) [_, _] [a', b'] renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameFold_at_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) f.abstract.int .add .add (operation_add_heq f.abstract) _ value decoded
        refine ⟨.list (.atom "+" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "+" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameFold_at_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) f.abstract.int .sub .sub (operation_sub_heq f.abstract) _ value decoded
        refine ⟨.list (.atom "-" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "-" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        have sourceLength := fold_length _ .sub _ value decoded
        have lengths := Uflia.SExpr.Renaming.forall₂_length (List.mapM_eq_some_iff_forall₂.mp renamed)
        rw [decodeSubtract_fold fuel _ outputs (by omega)]
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameCompare_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) .le .le (operation_le_heq f.abstract) false _ value decoded
        refine ⟨.list (.atom "<=" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "<=" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameCompare_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) .lt .lt (operation_lt_heq f.abstract) false _ value decoded
        refine ⟨.list (.atom "<" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "<" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameCompare_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) .le .le (operation_le_heq f.abstract) true _ value decoded
        refine ⟨.list (.atom ">=" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          ">=" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameCompare_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) .lt .lt (operation_lt_heq f.abstract) true _ value decoded
        refine ⟨.list (.atom ">" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          ">" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameEqualities_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) false _ value decoded
        refine ⟨.list (.atom "=" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "=" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameEqualities_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound) true _ value decoded
        refine ⟨.list (.atom "distinct" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "distinct" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · obtain ⟨c', a', b', renamed, mapped⟩ := renameIte_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound)  _ _ _ value decoded
        refine ⟨.list [.atom "ite", c', a', b'], renameBuiltin_success f fuel (localScope locals) next
          "ite" (by decide) (by decide) (by decide) (by decide) [_, _, _] [c', a', b'] renamed, ?_⟩
        exact mapped
      · obtain ⟨outputs, renamed, mapped⟩ := renameMultiply_result f.abstract (decodeScopedFuel? E fuel (sourceLocals locals))
          (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
          (renameScopedFuel? f fuel (localScope locals) next) (ih locals next valid bound)  _ value decoded
        refine ⟨.list (.atom "*" :: outputs), renameBuiltin_success f fuel (localScope locals) next
          "*" (by decide) (by decide) (by decide) (by decide) _ outputs renamed, ?_⟩
        exact mapped
      · exact renameUFApplication_guard_success f fuel next locals valid
          (ih locals next valid bound) _ _ value decoded

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
