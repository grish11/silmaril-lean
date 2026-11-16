module

public import Silmaril.Logic.Egg.Source.Named.Examples.Aliases.Defs
public import Silmaril.Logic.Egg.Source.Named.Representation.Inferred.Thms
public import Silmaril.Logic.Egg.Source.Named.Supplied.Theory.Defs
import Lean

@[expose] public section

/-! This check traverses proof dependencies of the general correspondence,
representation and theory APIs, as well as the concrete semantic controls.
It is a foundational-axiom ceiling, not a full repository CI claim. -/

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations : Array Lean.Name := #[
    ``Silmaril.Logic.Egg.Source.Named.denotes_unique,
    ``Silmaril.Logic.Egg.Source.Named.resolveTerm_denotes_iff,
    ``Silmaril.Logic.Egg.Source.Named.resolveRule_holds_iff,
    ``Silmaril.Logic.Egg.Source.Named.resolveProgram_holds_iff,
    ``Silmaril.Logic.Egg.Source.Named.eraseTerm_resolve,
    ``Silmaril.Logic.Egg.Source.Named.Parser.read_write_program,
    ``Silmaril.Logic.Egg.Source.Named.AcceptedProgram.resolved_holds,
    ``Silmaril.Logic.Egg.Source.Named.ProgramEntry.resolve_eq,
    ``Silmaril.Logic.Egg.Source.Named.DeclarationHom.resolveRule_map,
    ``Silmaril.Logic.Egg.Source.Named.DeclarationHom.resolveProgram_map,
    ``Silmaril.Logic.Egg.Source.Named.inferDeclarations_exists,
    ``Silmaril.Logic.Egg.Source.Named.inferTerm_resolve,
    ``Silmaril.Logic.Egg.Source.Named.inferredAdmissionComplete_task,
    ``Silmaril.Logic.Egg.Source.Named.finiteProgramRepresentation_task,
    ``Silmaril.Logic.Egg.Source.Named.localProgramByteRepresentation,
    ``Silmaril.Logic.Egg.Source.Named.FiniteSupport.finiteSuppliedProgramRepresentation,
    ``Silmaril.Logic.Egg.Source.Named.Families.toCore,
    ``Silmaril.Logic.Egg.Source.Named.Families.toCore_modelExpansive,
    ``Silmaril.Logic.Egg.Source.Named.FamilySentence.decode_holds,
    ``Silmaril.Logic.Egg.Source.Named.FamilySentence.decode_map,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.toCore,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.toCore_modelExpansive,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.decode_map,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.holds_map,
    ``Silmaril.Logic.Egg.Source.Named.theoryHolds_iff,
    ``Silmaril.Logic.Egg.Source.Named.satisfiable_iff,
    ``Silmaril.Logic.Egg.Source.Named.unsatisfiable_iff,
    ``Silmaril.Logic.Egg.Source.Named.entails_iff,
    ``Silmaril.Logic.Egg.Source.Named.every_theory_satisfiable,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.theoryHolds_iff,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.satisfiable_iff,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.unsatisfiable_iff,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.entails_iff,
    ``Silmaril.Logic.Egg.Source.Named.Supplied.Direct.every_theory_satisfiable,
    ``Silmaril.Logic.Egg.Source.Named.Examples.original_context_changes_truth,
    ``Silmaril.Logic.Egg.Source.Named.Examples.collapse_not_injective,
    ``Silmaril.Logic.Egg.Source.Named.Examples.complete_source_admitted,
    ``Silmaril.Logic.Egg.Source.Named.Examples.complete_source_two_rules,
    ``Silmaril.Logic.Egg.Source.Named.Examples.alias_local_names,
    ``Silmaril.Logic.Egg.Source.Named.Examples.distinct_bytes_same_ambient,
    ``Silmaril.Logic.Egg.Source.Named.Examples.aliases_share_populated_model,
    ``Silmaril.Logic.Egg.Source.Named.Examples.aliases_one_theory_model,
    ``Silmaril.Logic.Egg.Source.Named.Examples.supplied_transport_keeps_bytes,
    ``Silmaril.Logic.Egg.Source.Named.Examples.dropping_last_rule_changes_truth]
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    Lean.logInfo m!"AXIOMS {declaration}: {axioms}"
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected foundational axiom in {declaration}: {axiomName}"
  Lean.logInfo m!"Named Egg source: {declarations.size} transitive axiom ceilings passed"
