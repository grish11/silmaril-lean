module

public import Silmaril.Logic.HybridPolyadic.Matching.Thms
public import Silmaril.Logic.HybridPolyadic.Examples

/-! # Actual matching targets for names, @, down, n-ary actions and aliasing

Every displayed target uses native fixed-point/first-order matching denotation.
The final quantified pattern distinguishes a generated submodel from its target,
so hybrid truth invariance is not overstated as invariance of all FO/μ patterns.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Logic.HybridPolyadic.Matching.Examples
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Matching
open HybridPolyadic.Examples

abbrev target := expand cfg

theorem two_edges_target : Sat target (translateFixedPoint twoEdges) :=
  (expanded_satisfaction cfg twoEdges).mpr entry_two_edges_exit

theorem no_direct_target : ¬ Sat target
    (translateFixedPoint (.atNom Name.entry ((Formula.nominal Name.exit).unaryDia Action.step))) :=
  fun h => no_direct_step ((expanded_satisfaction cfg _).mp h)

theorem nary_target : Sat target
    (translateFixedPoint (.dia Action.fork ![Formula.top, .nominal Name.exit])) :=
  (expanded_satisfaction cfg _).mpr genuine_polyadic

theorem nary_swapped_target_false : ¬ Sat target
    (translateFixedPoint (.dia Action.fork ![.nominal Name.exit, Formula.top])) :=
  fun h => swapped_coordinate_rejected ((expanded_satisfaction cfg _).mp h)

/-- δ makes @ independent of the current world, including unreachable world 3. -/
theorem at_exit_every_world (w : Fin 4) :
    w ∈ target.base.denote (fun i => i.elim0) (translate (.atNom Name.exit (.nominal Name.exit))) :=
  (translate_denote target _ _ w).mpr rfl

theorem shadow_target : Sat target
    (translateFixedPoint (.down ((Formula.down (.state 0)).unaryDia Action.step))) :=
  (expanded_satisfaction cfg _).mpr binder_shadow

theorem outer_distinct_target_false : ¬ Sat target
    (translateFixedPoint (.down ((Formula.down (.state 1)).unaryDia Action.step))) :=
  fun h => binder_outer_distinct ((expanded_satisfaction cfg _).mp h)

theorem saved_entry_at_target : Sat target
    (translateFixedPoint (.down ((Formula.down (.atState 1 (.nominal Name.entry))).unaryDia Action.step))) :=
  (expanded_satisfaction cfg _).mpr saved_entry_at

theorem nominal_alias_target : Sat (reduct aliasNames target)
    (translateFixedPoint (.atNom Name.entry (.nominal Name.exit))) :=
  (translate_satisfaction _ _).mpr names_alias_reduct

theorem action_alias_target_false : ¬ Sat (reduct aliasActions target)
    (translateFixedPoint ((Formula.nominal Name.exit).unaryDia Action.jump)) :=
  fun h => action_alias_reduct ((translate_satisfaction _ _).mp h)

theorem capture_avoiding_target :
    (0 : Fin 4) ∈ target.base.denote ![2, 0]
      (translate ((Formula.down (.state 1) : Formula signature 1).rename
        (fun _ : Fin 1 => (1 : Fin 2)))) :=
  (translate_denote target _ _ _).mpr renamed_outer_state

/-- Nonempty nominal interpretations are a real restriction on raw matching models. -/
theorem reject_empty_nominal (a : Name) :
    ¬ ∃ choose : Name → Bool, (∅ : Set Bool) = {choose a} := by
  rintro ⟨choose, he⟩
  have hm : choose a ∈ (∅ : Set Bool) := by rw [he]; rfl
  exact hm

/-- Multiple names may denote the same state, but a single nominal cannot denote two states. -/
theorem reject_plural_nominal : ¬ ∃ w : Bool, (Set.univ : Set Bool) = {w} := by
  rintro ⟨w, he⟩
  have hf : false = w := by
    have hm : false ∈ ({w} : Set Bool) := by rw [← he]; trivial
    exact hm
  have ht : true = w := by
    have hm : true ∈ ({w} : Set Bool) := by rw [← he]; trivial
    exact hm
  exact Bool.false_ne_true (hf.trans ht.symm)

/-- An empty δ value cannot satisfy the explicitly declared full-carrier graph law. -/
theorem reject_empty_definedness : (∅ : Set Bool) ≠ Set.univ := by
  intro h
  have hm : false ∈ (∅ : Set Bool) := by rw [h]; trivial
  exact hm

/-- These are genuine unrestricted raw matching interpretations. -/
def markedRaw (names defined : Set Bool) : FirstOrder.Model (matchingSignature signature) where
  carrier _ := Bool
  nonempty _ := ⟨false⟩
  operation op := match op with
    | .atom _ => fun _ => ∅
    | .nominal _ => fun _ => names
    | .action _ => fun _ => ∅
    | .defined => fun _ => defined

theorem empty_nominal_raw_not_admitted :
    ¬ ∃ M : Model signature, M.base = markedRaw ∅ Set.univ := by
  rintro ⟨M, hb⟩
  apply nominal_not_empty M Name.entry
  rw [hb]
  rfl

theorem plural_nominal_raw_not_admitted :
    ¬ ∃ M : Model signature, M.base = markedRaw Set.univ Set.univ := by
  rintro ⟨M, hb⟩
  have small : ∀ x y : (markedRaw Set.univ Set.univ).carrier (),
      x ∈ (markedRaw Set.univ Set.univ).operation (.nominal Name.entry) (fun i => i.elim0) →
      y ∈ (markedRaw Set.univ Set.univ).operation (.nominal Name.entry) (fun i => i.elim0) → x = y := by
    rw [← hb]
    exact nominal_members_equal M Name.entry
  exact Bool.false_ne_true (small false true trivial trivial)

theorem empty_definedness_raw_not_admitted :
    ¬ ∃ M : Model signature, M.base = markedRaw {false} ∅ := by
  rintro ⟨M, hb⟩
  have law : ∀ args, (markedRaw {false} ∅).operation .defined args = Set.univ := by
    rw [← hb]
    exact M.definedness
  exact reject_empty_definedness (law (fun _ => false))

abbrev bareSignature : Signature := ⟨Empty, Empty, fun _ => Empty⟩

abbrev oneWorld : HybridPolyadic.Model bareSignature where
  World := Unit
  relation _ a := a.elim
  valuation a := a.elim
  name a := a.elim
  point := ()

abbrev twoWorlds : HybridPolyadic.Model bareSignature where
  World := Bool
  relation _ a := a.elim
  valuation a := a.elim
  name a := a.elim
  point := false

/-- This is an admitted target arrow and a genuine raw matching graph homomorphism. -/
def inclusion : expand oneWorld ⟶ expand twoWorlds where
  map _ := false
  injective := fun _ _ _ => Subsingleton.elim _ _
  point := rfl
  atoms a := a.elim
  names a := a.elim
  forth _ a := a.elim
  back _ a := a.elim

def rawInclusion : FirstOrder.Model.Hom (expand oneWorld).base (expand twoWorlds).base :=
  forgetHom inclusion

/-- A full target pattern can quantify over a world outside the arrow image. -/
def extraWorld : Sentence bareSignature := .base (.ex () (.neg (.var 0)))

theorem full_pattern_target_true : Sat (expand twoWorlds) extraWorld := by
  refine ⟨true, ?_⟩
  intro h
  cases h

theorem full_pattern_source_false : ¬ Sat (expand oneWorld) extraWorld := by
  rintro ⟨w, hw⟩
  exact hw (Subsingleton.elim _ _)

theorem two_edges_satisfiable : ∃ M : Model signature, Sat M (translateFixedPoint twoEdges) :=
  ⟨target, two_edges_target⟩

theorem bottom_unsat_target : ¬ ∃ M : Model signature, Sat M (translateFixedPoint .bot) :=
  (hybrid_unsat_iff (.bot : Formula signature 0)).mp (by rintro ⟨_, h⟩; exact h)

end Silmaril.Logic.HybridPolyadic.Matching.Examples

/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.translate_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.translate_denote
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.definedPattern_denote' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.definedPattern_denote
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.forgetHom' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.forgetHom
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.hybridNatural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.hybridNatural
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.hybridToConstrainedMatching_modelExpansive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.hybridToConstrainedMatching_modelExpansive
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.hybrid_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.hybrid_sat_iff
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.hybrid_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.hybrid_unsat_iff
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.hybrid_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.hybrid_entails_iff
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.Examples.at_exit_every_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.Examples.at_exit_every_world
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.Examples.capture_avoiding_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.Examples.capture_avoiding_target
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.Examples.empty_nominal_raw_not_admitted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.Examples.empty_nominal_raw_not_admitted
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.Examples.empty_definedness_raw_not_admitted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.Examples.empty_definedness_raw_not_admitted
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.Examples.full_pattern_target_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.Examples.full_pattern_target_true
/-- info: 'Silmaril.Logic.HybridPolyadic.Matching.Examples.full_pattern_source_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Matching.Examples.full_pattern_source_false
