import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Thms

open Silmaril.ProofFormats.DaslSyntax.Database
open Silmaril.Semantics.Naming (Binding graph_binding)
open Silmaril.Semantics.Naming.Lift (mem_where_iff)

section HOL

open Silmaril.Logic.HOLLight
open Examples.HOL

def members : List TermName := [.premise, .alias, .premise]

theorem resolved : HOL.listAssumptions terms members {premise} := by
  refine ⟨[premise, premise, premise], .cons rfl (.cons rfl (.cons rfl .nil)), ?_⟩
  simp

theorem listRow : HOL.derivesList terms initialSignature [] members .consequence :=
  namedSystem_iff.mpr ⟨_, consequence, resolved, rfl, consequenceProof⟩

theorem finiteRow : HOL.derivesFinite terms initialSignature [] members.toFinset .consequence :=
  (HOL.derivesList_iff_finite (graph_binding _) (fun _ => List.mem_toFinset.symm) resolved).mp listRow

example : HOL.typing contexts terms types initialSignature () .bound () :=
  typingTable_iff.mpr ⟨[.bool], .bvar 0, .bool, rfl, rfl, rfl, .bvar rfl trivial⟩

example : ¬ HOL.typingAt terms types initialSignature [] .bound () := by
  rintro ⟨⟨_, _, _⟩, ⟨termHit, typeHit, _⟩, checked⟩
  cases termHit
  cases typeHit
  cases checked with
  | bvar lookup _ => cases lookup

example : ¬ HOL.derives hypotheses terms initialSignature [] false .consequence :=
  namedSystem_no_context (by rintro ⟨_, hit⟩; cases hit)

example : () ∈ HOL.validTypes types initialSignature := mem_where_iff.mpr ⟨.bool, rfl, trivial⟩

example : TermName.closed ∈ HOL.propositions terms initialSignature :=
  HOL.closedTheorems_subset_propositions closedRow

example : ¬ TermName.premise ∈ HOL.closedTheorems terms initialSignature [] := by
  rintro ⟨⟨_, _⟩, ⟨hit, _⟩, _, free, _⟩
  cases hit
  cases free

end HOL

section MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Examples.MLTT

example : true ∈ MLTT.wellTyped terms .nil sigma := mem_where_iff.mpr ⟨pair, rfl, .nil_ok, pairTyping⟩

example : ¬ MLTT.typing contexts terms types () false () := by
  rintro ⟨⟨_, _, _, _⟩, ⟨_, hit, _, _⟩, _⟩
  cases hit

example : MLTT.inhabitance contexts types () () := inhabitanceRow

end MLTT

#print axioms valueSystem_names
#print axioms namesWhere_eq_recognized
#print axioms HOL.derivesList_iff_finite
#print axioms HOL.derives_le_entails
#print axioms Examples.HOL.closedRow
#print axioms Examples.HOL.contextRow
#print axioms finiteRow
#print axioms Examples.MLTT.formationRow
#print axioms Examples.MLTT.inhabitanceRow
#print axioms Examples.MLTT.typingRow
#print axioms Examples.MLTT.firstProjection
#print axioms Examples.MLTT.secondProjection
