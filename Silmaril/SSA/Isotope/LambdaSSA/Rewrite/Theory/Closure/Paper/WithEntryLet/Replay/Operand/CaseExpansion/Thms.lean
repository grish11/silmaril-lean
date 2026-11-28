module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.CaseExpansion.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetCaseExpansion

/-! # Case duplication and the limits of target repair

The interchange problems in the standard Paper presentation arise at
different kinds of rule.

* Value substitution, label renaming, and congruence retain region structure.
  Constructor let beta removes a binder and substitutes into the body.
  Product beta contracts a binary binder, while product eta contracts the
  unpack-and-forward form. Case-to-CFG moves case arms into local blocks.
* Case-value expansion can make two copies of a region. Selection of an
  injected case arm drops the other arm. CFG zero removes an enclosure,
  while outward CFG elimination and an outward entry branch drop local
  blocks. A local entry branch copies a block into the entry. CFG eta and
  continuation substitution can insert copies at several jumps or at none.
  Feedback collapse identifies two loop interfaces, and the native
  uniformity generator uses a commuting square. Neither supplies an
  address map in its premises. Native initiality relates arbitrary
  regions given an empty constructor value in scope.
* Reversing EntryLet belongs to symmetry in the extension. Recovering a
  table before that move requires undoing weakening in the local blocks,
  including exclusion of the newly bound capture. It is a separate
  problem from commuting a forward move across a native step.

Here native case-value expansion duplicates a computation after the state
map has discarded a tag. A forward EntryLet move in just one copy makes the
two tags distinguishable by the standard Paper diagnostic.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.CaseExpansion

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction
open OperandExample (Bit D X Seed forget target)
open Paper.TypeCategory (ofRegion sumIso)
open Extension.Singleton (projection projectStep iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "J" => projection Seed

/-- Expand a case on the discarded input by the native case-value rule. -/
theorem native_expansion :
    Paper.Eqv [Bit] (flatRecurringRequest.substVars discardInput) duplicatedRequest [Bit] :=
  EntryLetCaseExpansion.native_expansion

/-- Select just one of the two copies for the next EntryLet move. -/
theorem move_one_copy : (Site.leftArm .here).move duplicatedRequest = some oneMovedRequest :=
  EntryLetCaseExpansion.move_one_copy

theorem oneMovedRequest_typed : ValueBranches [Bit] oneMovedRequest [Bit] :=
  EntryLetCaseExpansion.oneMovedRequest_typed

theorem source_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion oneMovedRequest_typed ≫ (sumIso U U).hom :=
  EntryLetCaseExpansion.source_composite

/-- The actual cyclic square commutes in the EntryLet extension. -/
theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target :=
  EntryLetCaseExpansion.corrected_square

/-- With the source and state map fixed, no target in standard Paper
can make the square commute. -/
theorem no_target_repair (g : X ⟶ X ⨿ X) :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ g :=
  EntryLetCaseExpansion.no_target_repair g

/-- Changing the source representative to use the same request
placement at both tags recovers a native square with the written target. -/
theorem source_repaired :
    ∃ f : D ⟶ X ⨿ D, projectStep Seed f = projectStep Seed source ∧
      f ≫ coprod.map (𝟙 X) forget = forget ≫ target :=
  EntryLetCaseExpansion.source_repaired

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  EntryLetCaseExpansion.corrected_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.CaseExpansion
