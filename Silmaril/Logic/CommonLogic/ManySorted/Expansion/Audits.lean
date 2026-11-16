module

public import Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples
import Lean

/-! Named-declaration axiom ceiling for expansion.
Checks every user-authored public top-level definition/type/theorem in this slice
and its examples, including public implementation bridge theorems where present.
Private helpers are checked transitively through these declarations.
The scope is exactly the 50 names printed and listed below; this is not a
whole-library or structural-assumption audit. No exact observed axiom sets are presumed. -/

#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Discourse
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.junk
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.tag
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.tag_injective
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.encode
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.encode_injective
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.applyOperation
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.function
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.relation
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.raw
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.function_encode
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.function_off_profile
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.relation_encode
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.raw_wellTyped
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.expand
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.pack
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.unpack
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.unpack_spec
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.unpack_pack
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.pack_unpack
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.carrierEquiv
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.decodeExpandIso
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.decoded_coverage
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.expanded_satisfaction
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.typedRoom
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.comparison
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.source_isoInvariant
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.isoExpansive
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.elemExpansive
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.entails_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.satisfiable_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.unsatisfiable_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.satisfiable_raw_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.emptySignature
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.emptySource
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.no_sorts_only_junk
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.decoded_empty_carrier
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.empty_source_recovered
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.numericSignature
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.numericSource
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.nullary_value
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.tagged_function
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.tagged_relation
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.off_profile_function
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.junk_not_sorted
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.off_profile_relation
#print axioms Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.unpack_op
#print axioms Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.unpack_rel
#print axioms Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.decodeExpandIso
#print axioms Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.sentence_holds_iso

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Discourse,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.junk,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.tag,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.tag_injective,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.encode,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.encode_injective,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.applyOperation,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.function,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.relation,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.raw,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.function_encode,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.function_off_profile,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.relation_encode,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.raw_wellTyped,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.expand,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.pack,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.unpack,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.unpack_spec,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.unpack_pack,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.pack_unpack,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.carrierEquiv,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.decodeExpandIso,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.decoded_coverage,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.expanded_satisfaction,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.typedRoom,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.comparison,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.source_isoInvariant,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.isoExpansive,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.elemExpansive,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.entails_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.satisfiable_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.unsatisfiable_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.satisfiable_raw_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.emptySignature,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.emptySource,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.no_sorts_only_junk,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.decoded_empty_carrier,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.empty_source_recovered,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.numericSignature,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.numericSource,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.nullary_value,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.tagged_function,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.tagged_relation,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.off_profile_function,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.junk_not_sorted,
    ``Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples.off_profile_relation,
    ``Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.unpack_op,
    ``Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.unpack_rel,
    ``Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.decodeExpandIso,
    ``Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.sentence_holds_iso]
  for name in checked do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"expansion: checked {checked.length} named declarations against the standard three-axiom ceiling"
