module

public import Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt.SourceBase
public import Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawHooks

set_option linter.concreteInstances false
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Kore.GeneralFixedPoint (RawPattern)
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Kore.Modules.Checking (namedSort)
variable [sorts : SortBindings]

/-- Every successful raw check agrees with the independent original interpreter.
The source model and its carrier equivalences are arbitrary. Free object values
remain sets; legality requires only the actual finite binding at its exact sort. -/
theorem rawAdequacy_task : Task.rawAdequacy := by
  intro scope hooks literalPrefix literals M objects fuel
  induction fuel with
  | zero =>
      intro s raw p accepted _
      simp [check] at accepted
  | succ fuel ih =>
      intro s raw p accepted legal
      cases declared : namedSort scope s.name with
      | false => simp [check, declared] at accepted
      | true =>
          cases raw with
          | evar name actual =>
              by_cases same : actual = s.name
              · subst actual
                have equal : Pattern.variable s name = p := by
                  simpa [check, declared] using accepted
                subst p
                exact source_variable M.carriers objects s name fuel declared
                  (legal (s, name) (by simp [Pattern.variables]))
              · simp [check, declared, same] at accepted
          | top actual =>
              by_cases same : actual = s.name
              · subst actual
                have equal : Pattern.top s = p := by
                  simpa [check, declared] using accepted
                subst p
                exact source_top M.carriers objects s fuel declared
              · simp [check, declared, same] at accepted
          | bottom actual =>
              by_cases same : actual = s.name
              · subst actual
                have equal : Pattern.bottom s = p := by
                  simpa [check, declared] using accepted
                subst p
                exact source_bottom M.carriers objects s fuel declared
              · simp [check, declared, same] at accepted
          | domainValue actual text =>
              by_cases same : actual = s.name
              · subst actual
                cases parsed : Literal.parse s.name text with
                | none => simp [check, declared, parsed] at accepted
                | some literal =>
                    cases s with
                    | integer =>
                        cases literal with
                        | integer n =>
                            have equal : Pattern.integer n = p := by
                              simpa [check, declared, parsed, literalPattern] using accepted
                            subst p
                            simpa only [Pattern.denote, sourceEquiv, ValueSort.name,
                              Set.mem_singleton_iff]
                              using source_integer M.carriers objects text n fuel parsed
                        | boolean b =>
                            simp [check, declared, parsed, literalPattern] at accepted
                    | boolean =>
                        cases literal with
                        | integer n =>
                            simp [check, declared, parsed, literalPattern] at accepted
                        | boolean b =>
                            have equal : Pattern.boolean b = p := by
                              simpa [check, declared, parsed, literalPattern] using accepted
                            subst p
                            simpa only [Pattern.denote, sourceEquiv, ValueSort.name,
                              Set.mem_singleton_iff]
                              using source_boolean M.carriers objects text b fuel parsed
              · simp [check, declared, same] at accepted
          | neg actual raw =>
              by_cases same : actual = s.name
              · subst actual
                cases child : check scope hooks fuel s raw with
                | none => simp [check, declared, child] at accepted
                | some q =>
                    have equal : Pattern.neg q = p := by
                      simpa [check, declared, child] using accepted
                    subst p
                    exact source_neg M.carriers objects s fuel raw q
                      (ih s raw q child legal)
              · simp [check, declared, same] at accepted
          | conj actual raw other =>
              by_cases same : actual = s.name
              · subst actual
                cases left : check scope hooks fuel s raw with
                | none => simp [check, declared, left] at accepted
                | some q =>
                    cases right : check scope hooks fuel s other with
                    | none => simp [check, declared, left, right] at accepted
                    | some r =>
                        have equal : Pattern.conj q r = p := by
                          simpa [check, declared, left, right] using accepted
                        subst p
                        exact source_conj M.carriers objects s fuel raw other q r
                          (ih s raw q left (fun b hb => legal b (List.mem_append_left _ hb)))
                          (ih s other r right (fun b hb => legal b (List.mem_append_right _ hb)))
              · simp [check, declared, same] at accepted
          | disj actual raw other =>
              by_cases same : actual = s.name
              · subst actual
                cases left : check scope hooks fuel s raw with
                | none => simp [check, declared, left] at accepted
                | some q =>
                    cases right : check scope hooks fuel s other with
                    | none => simp [check, declared, left, right] at accepted
                    | some r =>
                        have equal : Pattern.disj q r = p := by
                          simpa [check, declared, left, right] using accepted
                        subst p
                        exact source_disj M.carriers objects s fuel raw other q r
                          (ih s raw q left (fun b hb => legal b (List.mem_append_left _ hb)))
                          (ih s other r right (fun b hb => legal b (List.mem_append_right _ hb)))
              · simp [check, declared, same] at accepted
          | app name args =>
              cases chosen : hook? scope hooks name with
              | none => simp [check, declared, chosen] at accepted
              | some h =>
                  obtain ⟨d, binding, found, member, symbol, hook, valid⟩ :=
                    hook_selected hooks name h chosen
                  cases s with
                  | integer => simp [check, declared, chosen, hookPattern] at accepted
                  | boolean =>
                      cases h with
                      | intEq =>
                          have profile :
                              d.val.declaration.arguments = [sorts.intSort, sorts.intSort] ∧
                                d.val.declaration.result = sorts.boolSort := by
                            simpa [Hook.valid, Hook.arguments, Hook.result] using valid
                          cases args with
                          | nil => simp [check, declared, chosen, hookPattern] at accepted
                          | cons raw rest =>
                              cases rest with
                              | nil => simp [check, declared, chosen, hookPattern] at accepted
                              | cons other tail =>
                                  cases tail with
                                  | cons extra tail =>
                                      simp [check, declared, chosen, hookPattern] at accepted
                                  | nil =>
                                      cases left : check scope hooks fuel .integer raw with
                                      | none => simp [check, declared, chosen, hookPattern, left] at accepted
                                      | some q =>
                                          cases right : check scope hooks fuel .integer other with
                                          | none => simp [check, declared, chosen, hookPattern, left, right] at accepted
                                          | some r =>
                                              have equal : Pattern.intEq q r = p := by
                                                simpa [check, declared, chosen, hookPattern, left, right] using accepted
                                              subst p
                                              exact source_intEq M objects fuel name d binding found
                                                member symbol hook profile.1 profile.2 raw other q r
                                                (ih .integer raw q left
                                                  (fun b hb => legal b (List.mem_append_left _ hb)))
                                                (ih .integer other r right
                                                  (fun b hb => legal b (List.mem_append_right _ hb)))
                      | boolNot =>
                          have profile : d.val.declaration.arguments = [sorts.boolSort] ∧
                              d.val.declaration.result = sorts.boolSort := by
                            simpa [Hook.valid, Hook.arguments, Hook.result] using valid
                          cases args with
                          | nil => simp [check, declared, chosen, hookPattern] at accepted
                          | cons raw rest =>
                              cases rest with
                              | cons extra rest => simp [check, declared, chosen, hookPattern] at accepted
                              | nil =>
                                  cases child : check scope hooks fuel .boolean raw with
                                  | none => simp [check, declared, chosen, hookPattern, child] at accepted
                                  | some q =>
                                      have equal : Pattern.boolNot q = p := by
                                        simpa [check, declared, chosen, hookPattern, child] using accepted
                                      subst p
                                      exact source_boolNot M objects fuel name d binding found
                                        member symbol hook profile.1 profile.2 raw q
                                        (ih .boolean raw q child legal)
          | svar name actual => simp [check, declared] at accepted
          | ex actual name bound body => simp [check, declared] at accepted
          | all actual name bound body => simp [check, declared] at accepted
          | mu name actual body => simp [check, declared] at accepted
          | nu name actual body => simp [check, declared] at accepted

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
