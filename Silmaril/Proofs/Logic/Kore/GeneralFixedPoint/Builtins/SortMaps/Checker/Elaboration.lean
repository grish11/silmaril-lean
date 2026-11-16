module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Collections.Thms

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open Kore.Modules.Checking
open Silmaril.Proofs.Logic.Kore.FixedPoint (collect_some collect_pure)

/-- Every successfully elaborated raw constructor is transported at the same
fuel and module index. Literal profiles are independently validated finite data;
no target checker-success or semantic equation is assumed. -/
theorem Step.elaborate_forward {A B : Package} (f : Step A B)
    (profiles : literalProfiles A = true) : ∀ fuel, FuelTransport f fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro mi sets objects s rawp typed accepted
      cases accepted
  | succ n ih =>
      intro mi sets objects s rawp typed accepted
      cases rawp with
      | domainValue actual text =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have sameActual : actual = s := by simpa using valid
            subst actual
            obtain ⟨l, parsed, rest⟩ := Option.bind_eq_some_iff.mp accepted
            split at rest
            · rename_i same
              obtain ⟨op, found, result⟩ := Option.bind_eq_some_iff.mp rest
              cases Option.some.inj result
              obtain ⟨op', targetFound, binding⟩ := f.literalOperation_forward profiles found
              have targetParsed := literal_parse_forward f.semantic s text l parsed
              have same' : @Literal.sort B.base.bindings l = f.semantic.native.sorts s :=
                (literal_sort_map f.semantic l).trans (congrArg f.semantic.native.sorts same)
              simp [elaboratePackage, raw, Checking.elaborate, targetParsed,
                same', targetFound, Bind.bind, Option.bind, reindexPattern_literal f op op' binding same same']
            · contradiction
      | evar name actual =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope s = true := by
              simpa using valid
            obtain ⟨sameActual, named⟩ := good
            subst actual
            have targetNamed := f.namedSort_forward s named
            cases found : lookup objects name with
            | none => simp [found] at accepted
            | some i =>
                simp only [found, Bind.bind, Option.bind] at accepted
                split at accepted
                · rename_i same
                  cases Option.some.inj accepted
                  change FixedPoint.lookup objects name = some i at found
                  have targetLookup := lookup_mapNames f.semantic.native.sorts objects name
                  rw [found, Option.map_some] at targetLookup
                  have targetSame := (context_mapNames f.semantic.native.sorts objects i).trans
                    (congrArg f.semantic.native.sorts same)
                  simp [elaboratePackage, raw, Checking.elaborate, targetNamed, targetLookup,
                    targetSame, reindexPattern_var f i same]
                · contradiction
      | svar name actual =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope s = true := by
              simpa using valid
            obtain ⟨sameActual, named⟩ := good
            subst actual
            have targetNamed := f.namedSort_forward s named
            cases found : lookup sets name with
            | none => simp [found] at accepted
            | some i =>
                simp only [found, Bind.bind, Option.bind] at accepted
                split at accepted
                · rename_i same
                  cases Option.some.inj accepted
                  change FixedPoint.lookup sets name = some i at found
                  have targetLookup := lookup_mapNames f.semantic.native.sorts sets name
                  rw [found, Option.map_some] at targetLookup
                  have targetSame := (context_mapNames f.semantic.native.sorts sets i).trans
                    (congrArg f.semantic.native.sorts same)
                  simp [elaboratePackage, raw, Checking.elaborate, targetNamed, targetLookup,
                    targetSame, reindexPattern_setvar f i same]
                · contradiction
      | top actual =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · rename_i valid
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope s = true := by
              simpa using valid
            obtain ⟨sameActual, named⟩ := good
            subst actual
            cases Option.some.inj accepted
            have targetNamed := f.namedSort_forward s named
            simp [elaboratePackage, raw, Checking.elaborate, targetNamed, reindexPattern_top]
          · contradiction
      | bottom actual =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · rename_i valid
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope s = true := by
              simpa using valid
            obtain ⟨sameActual, named⟩ := good
            subst actual
            cases Option.some.inj accepted
            have targetNamed := f.namedSort_forward s named
            simp [elaboratePackage, raw, Checking.elaborate, targetNamed, reindexPattern_bottom]
          · contradiction
      | neg actual body =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have sameActual : actual = s := by simpa using valid
            subst actual
            obtain ⟨p, checked, result⟩ := Option.bind_eq_some_iff.mp accepted
            cases Option.some.inj result
            simp [elaboratePackage, raw, Checking.elaborate,
              ih mi sets objects s body p checked, reindexPattern_neg]
      | conj actual left right =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have sameActual : actual = s := by simpa using valid
            subst actual
            obtain ⟨p, leftChecked, rest⟩ := Option.bind_eq_some_iff.mp accepted
            obtain ⟨q, rightChecked, result⟩ := Option.bind_eq_some_iff.mp rest
            cases Option.some.inj result
            simp [elaboratePackage, raw, Checking.elaborate,
              ih mi sets objects s left p leftChecked, ih mi sets objects s right q rightChecked,
              reindexPattern_conj]
      | disj actual left right =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have sameActual : actual = s := by simpa using valid
            subst actual
            obtain ⟨p, leftChecked, rest⟩ := Option.bind_eq_some_iff.mp accepted
            obtain ⟨q, rightChecked, result⟩ := Option.bind_eq_some_iff.mp rest
            cases Option.some.inj result
            simp [elaboratePackage, raw, Checking.elaborate,
              ih mi sets objects s left p leftChecked, ih mi sets objects s right q rightChecked,
              reindexPattern_disj]
      | ex actual name bound body =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope bound = true := by
              simpa using valid
            obtain ⟨sameActual, named⟩ := good
            subst actual
            have targetNamed := f.namedSort_forward bound named
            obtain ⟨p, checked, result⟩ := Option.bind_eq_some_iff.mp accepted
            cases Option.some.inj result
            have targetBody := ih mi sets ((name, bound) :: objects) s body p checked
            simp only [elaboratePackage, mapNames_cons] at targetBody
            simp [elaboratePackage, raw, Checking.elaborate, targetNamed,
              targetBody, reindexPattern_ex f name]
      | all actual name bound body =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          split at accepted
          · contradiction
          · rename_i valid
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope bound = true := by
              simpa using valid
            obtain ⟨sameActual, named⟩ := good
            subst actual
            have targetNamed := f.namedSort_forward bound named
            obtain ⟨p, checked, result⟩ := Option.bind_eq_some_iff.mp accepted
            cases Option.some.inj result
            have targetBody := ih mi sets ((name, bound) :: objects) s body p checked
            simp only [elaboratePackage, mapNames_cons] at targetBody
            simp [elaboratePackage, raw, Checking.elaborate, targetNamed,
              targetBody, reindexPattern_all f name]
      | mu name actual body =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          by_cases rejected : (decide (actual ≠ s) || !Kore.Modules.Checking.namedSort A.base.scope s) = true
          · rw [ite_eq_left rejected] at accepted
            contradiction
          · rw [ite_eq_right rejected] at accepted
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope s = true := by
              simpa using rejected
            obtain ⟨sameActual, named⟩ := good
            subst actual
            have targetNamed := f.namedSort_forward s named
            obtain ⟨p, checked, result⟩ := Option.bind_eq_some_iff.mp accepted
            cases Option.some.inj result
            have targetBody := ih mi ((name, s) :: sets) objects s body p checked
            simp only [elaboratePackage, mapNames_cons] at targetBody
            simp [elaboratePackage, raw, Checking.elaborate, targetNamed,
              targetBody, reindexPattern_mu f name]
      | nu name actual body =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          by_cases rejected : (decide (actual ≠ s) || !Kore.Modules.Checking.namedSort A.base.scope s) = true
          · rw [ite_eq_left rejected] at accepted
            contradiction
          · rw [ite_eq_right rejected] at accepted
            have good : actual = s ∧ Kore.Modules.Checking.namedSort A.base.scope s = true := by
              simpa using rejected
            obtain ⟨sameActual, named⟩ := good
            subst actual
            have targetNamed := f.namedSort_forward s named
            obtain ⟨p, checked, result⟩ := Option.bind_eq_some_iff.mp accepted
            cases Option.some.inj result
            have targetBody := ih mi ((name, s) :: sets) objects s body p checked
            simp only [elaboratePackage, mapNames_cons] at targetBody
            simp [elaboratePackage, raw, Checking.elaborate, targetNamed,
              targetBody, reindexPattern_nu f name]
      | app name args =>
          simp only [elaboratePackage, Checking.elaborate] at accepted
          cases symbolsFound : A.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
          | some d =>
              simp only [symbolsFound] at accepted
              split at accepted
              · rename_i resultSort
                split at accepted
                · rename_i arity
                  obtain ⟨ps, argumentsChecked, result⟩ := Option.bind_eq_some_iff.mp accepted
                  cases Option.some.inj result
                  obtain ⟨d', targetFound, selected⟩ := f.symbol_attached_some name d symbolsFound
                  rcases d' with ⟨targetSymbol, targetMember⟩
                  cases selected
                  have targetResult : (symbol f.semantic.native.sorts f.names d.val).declaration.result =
                      f.semantic.native.sorts s := congrArg f.semantic.native.sorts resultSort
                  have targetArity : (args.map (raw f.semantic.native.sorts f.names)).length =
                      (symbol f.semantic.native.sorts f.names d.val).declaration.arguments.length := by
                    simpa only [symbol, declaration, List.length_map] using arity
                  have targetArguments := symbol_arguments_forward f ih mi sets objects
                    d.val.declaration.arguments args arity ps argumentsChecked
                  let sourceOp : A.base.scope.signature.operations d.val.declaration.arguments.length
                      d.val.declaration.arguments.get s := ⟨d.val, d.property, by simp, resultSort⟩
                  let targetOp : B.base.scope.signature.operations
                      (d.val.declaration.arguments.map f.semantic.native.sorts).length
                      (d.val.declaration.arguments.map f.semantic.native.sorts).get (f.semantic.native.sorts s) :=
                    ⟨symbol f.semantic.native.sorts f.names d.val, targetMember, by simp [symbol, declaration], targetResult⟩
                  simp only [elaboratePackage, raw, raw_arguments, Checking.elaborate, targetFound]
                  simp only [symbol, declaration] at targetResult targetArity ⊢
                  rw [dite_eq_left targetResult, dite_eq_left targetArity, targetArguments]
                  simp only [Bind.bind, Option.bind]
                  exact congrArg some (reindexPattern_app f sourceOp targetOp rfl ps).symm
                · contradiction
              · contradiction
          | none =>
              simp only [symbolsFound] at accepted
              obtain ⟨d, aliasFound, accepted⟩ := Option.bind_eq_some_iff.mp accepted
              split at accepted
              · rename_i valid
                have good : d.valid A.base.scope = true ∧ d.symbol.result = s ∧ args.length = d.parameters.length := by
                  simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using valid
                obtain ⟨validAlias, resultSort, arity⟩ := good
                obtain ⟨body, bodyChecked, rest⟩ := Option.bind_eq_some_iff.mp accepted
                obtain ⟨σ, objectsChecked, rest⟩ := Option.bind_eq_some_iff.mp rest
                obtain ⟨τ, setsChecked, result⟩ := Option.bind_eq_some_iff.mp rest
                cases Option.some.inj result
                have targetSymbols := f.symbol_attached_none name symbolsFound
                have targetAlias := f.alias_find name
                rw [aliasFound, Option.map_some] at targetAlias
                have targetValid := f.alias_valid d validAlias
                have targetGood :
                    ((renameAlias f.semantic.native.sorts f.names d).valid B.base.scope &&
                      (renameAlias f.semantic.native.sorts f.names d).symbol.result == f.semantic.native.sorts s &&
                      (args.map (raw f.semantic.native.sorts f.names)).length ==
                        (renameAlias f.semantic.native.sorts f.names d).parameters.length) = true := by
                  simp only [Bool.and_eq_true, beq_iff_eq]
                  refine ⟨⟨targetValid, ?_⟩, ?_⟩
                  · simpa only [renameAlias, declaration] using congrArg f.semantic.native.sorts resultSort
                  · simpa only [renameAlias, List.length_map] using arity
                have targetBody := ih d.moduleIndex (d.names true) (d.names false) s d.body body bodyChecked
                have targetObjects := alias_arguments_forward f ih mi sets objects d args false σ objectsChecked
                have targetSets := alias_arguments_forward f ih mi sets objects d args true τ setsChecked
                simp only [elaboratePackage] at targetBody targetObjects targetSets
                simp only [elaboratePackage, raw, raw_arguments, Checking.elaborate, targetSymbols,
                  targetAlias, Bind.bind, Option.bind, ite_eq_left targetGood]
                generalize setsNamed : (renameAlias f.semantic.native.sorts f.names d).names true = targetSetNames
                have setsSame : targetSetNames = mapNames f.semantic.native.sorts (d.names true) :=
                  setsNamed.symm.trans (alias_names f.semantic.native.sorts f.names d true)
                clear setsNamed
                subst targetSetNames
                generalize objectsNamed : (renameAlias f.semantic.native.sorts f.names d).names false = targetObjectNames
                have objectsSame : targetObjectNames = mapNames f.semantic.native.sorts (d.names false) :=
                  objectsNamed.symm.trans (alias_names f.semantic.native.sorts f.names d false)
                clear objectsNamed
                subst targetObjectNames
                dsimp only [renameAlias, Bind.bind, Option.bind] at targetObjects targetSets ⊢
                rw [targetBody, targetObjects, targetSets]
                exact congrArg some (reindexPattern_substitute f body τ σ).symm
              · contradiction

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
