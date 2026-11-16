module

public import Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source

/-- The actual source declaration and rewrite checker both succeeded. -/
theorem Package.parser_and_checker {cfg fuel text} (p : Package cfg fuel text) :
    Syntax.parse text = some p.source ∧
      checkDefinition cfg fuel p.source = some p.definition :=
  ⟨p.parsed, p.accepted⟩

export Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
  (checkPayload_source checkDefinition_source localRules_source checkModule_source
   checkModule_local_axiom_source checkModule_local_claim_source
   CheckedHistory checkDefinition_history ImportPath InstalledSource
   package_installed_source package_installed_is_axiom
   OriginatingScope InstalledSourceWithScope package_installed_source_with_scope)

/-- Every projected module record uses exactly its axiom list. This theorem
alone does not establish accepted-source provenance; Package acceptance and
the source-membership theorems supply that separate boundary. -/
theorem CheckedModule.induced_raw_iff_lowered {ambient cfg}
    (m : CheckedModule ambient cfg)
    (M : Matching.GeneralFixedPoint.Model ambient.signature) (w v : M.carrier cfg) :
    RawStep m.system M w v ↔ Reachability.RuleSystem.Induced (lowerSchemes m.system M) w v :=
  CheckedRewrites.induced_raw_iff_lowered m.system M w v

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
