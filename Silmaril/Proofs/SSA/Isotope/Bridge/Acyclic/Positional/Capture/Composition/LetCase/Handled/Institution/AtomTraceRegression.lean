module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation grammarCase readGrammar mapRanked
  readGrammar_map grammarCase_map)
open Silmaril.Semantics.NondeterministicTrace (Finite)
open Region (packedExitType)
open Reverse (CheckedTable)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (StructuralContext equiv_iff_traceArrow_eq_snoc)
open LetCase.Structural.Reply (Γ₀ run traceArrow_eq_iff_run traceArrow_of_valid valid_of_equiv)
open Silmaril.Isotope.Institution.Acyclic (regionWitnessPullback)
open LetSeq.StraightLine.Structural (Shape Packed packedEnv Log packed_run_eq_iff_native mem_request_trace)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

/-! ## A signature with an atom

There is one atom. The primitive takes two atoms and returns one. The
bound context is one packed slot holding two captured atoms. -/

private inductive Ask | ask

local instance : LetSeq.StraightLine.Structural.Signature Unit Ask :=
  ⟨fun _ => .pair (.atom ()) (.atom ()), fun _ => .atom ()⟩

private abbrev tok : Ty Unit := .base ()
private abbrev captures : Shape Unit := .pair (.atom ()) (.atom ())
private abbrev Line := LetSeq.LocallyNameless.Tm Empty Ask 1
private abbrev Typed (t : Line) :=
  LetSeq.LocallyNameless.Derivation Ask LetSeq.StraightLine.Structural.Γ₀ (Packed captures) t tok

example : (Packed captures).get 0 = .product tok tok := rfl

/-- Return the first captured atom. -/
private def first : Typed (.let₂ (.bv 0) (.bv 1)) := .let₂ (A := tok) (B := tok) .bv .bv

/-- Return the second captured atom. -/
private def second : Typed (.let₂ (.bv 0) (.bv 0)) := .let₂ (A := tok) (B := tok) .bv .bv

/-- Ask with the two captured atoms in their order and return the reply. -/
private def asking : Typed (.let₂ (.bv 0) (.op Ask.ask (.pair (.bv 1) (.bv 0)))) :=
  .let₂ (A := tok) (B := tok) .bv (.op (.pair .bv .bv))

/-- Ask with the two captured atoms swapped. -/
private def swapped : Typed (.let₂ (.bv 0) (.op Ask.ask (.pair (.bv 0) (.bv 1)))) :=
  .let₂ (A := tok) (B := tok) .bv (.op (.pair .bv .bv))

private abbrev entry {t : Line} (line : Typed t) := entryOf (lineGraph line)

/-! ## The separating input and the runs -/

private abbrev input := packedEnv captures (captures.fresh 0)

example : captures.fresh 0 = ((0 : Nat), (1 : Nat)) := rfl

private theorem run_first : LetSeq.StraightLine.Structural.run first input = pure (0 : Nat) := by
  simp only [LetSeq.StraightLine.Structural.run, first, LetSeq.LocallyNameless.Derivation.denote]
  erw [pure_bind]
  rfl

private theorem run_second : LetSeq.StraightLine.Structural.run second input = pure (1 : Nat) := by
  simp only [LetSeq.StraightLine.Structural.run, second, LetSeq.LocallyNameless.Derivation.denote]
  erw [pure_bind]
  rfl

private theorem run_asking :
    LetSeq.StraightLine.Structural.run asking input = (LetSeq.StraightLine.Structural.model (α := Unit)).eval Ask.ask ((0 : Nat), (1 : Nat)) := by
  simp only [LetSeq.StraightLine.Structural.run, asking, LetSeq.LocallyNameless.Derivation.denote]
  erw [pure_bind, pure_bind, pure_bind, pure_bind]
  rfl

private theorem run_swapped :
    LetSeq.StraightLine.Structural.run swapped input = (LetSeq.StraightLine.Structural.model (α := Unit)).eval Ask.ask ((1 : Nat), (0 : Nat)) := by
  simp only [LetSeq.StraightLine.Structural.run, swapped, LetSeq.LocallyNameless.Derivation.denote]
  erw [pure_bind, pure_bind, pure_bind, pure_bind]
  rfl

/-! ## Captured atoms are told apart

The two captured atoms are different terms. They are not natively equal,
and the sentence between their graphs is not valid. -/

private theorem captures_differ : ¬ LetSeq.LocallyNameless.Equiv false LetSeq.StraightLine.Structural.Γ₀
    (Packed captures) (.let₂ (.bv 0) (.bv 1) : Line) (.let₂ (.bv 0) (.bv 0)) tok := by
  intro h
  have runs := (packed_run_eq_iff_native first second).mpr h
  rw [run_first, run_second] at runs
  have mem : ((0 : Nat), (1 : Log Unit Ask)) ∈ Finite.outcomes (pure (0 : Nat)) := rfl
  rw [runs] at mem
  exact absurd (congrArg Prod.fst (show ((0 : Nat), (1 : Log Unit Ask)) = (1, 1) from mem)) (by decide)

/-- The sentence between the graphs of the two captured atoms. -/
private abbrev apart : RankedEquation (atomSig Unit Ask) := sentenceOf (entry first) (entry second)

private theorem apart_invalid : ¬ RankedValid false apart := fun valid =>
  captures_differ ((rankedValid_line_iff first second).mp valid)

/-- The ordered trace model with atoms is a supported model that rejects it. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Ask))
    (atomSig Unit Ask)).Sat (atomTraceRanked Unit Ask) apart := fun holds =>
  apart_invalid ((rankedValid_straightLine_iff_atomTrace (entry first) (entry second)
    (straightLine_lineGraph first) (straightLine_lineGraph second)).mpr holds)

/-- The order of the captured atoms in a request is observed. -/
private theorem requests_differ : ¬ LetSeq.LocallyNameless.Equiv false LetSeq.StraightLine.Structural.Γ₀
    (Packed captures) (.let₂ (.bv 0) (.op Ask.ask (.pair (.bv 1) (.bv 0))) : Line)
    (.let₂ (.bv 0) (.op Ask.ask (.pair (.bv 0) (.bv 1)))) tok := by
  intro h
  have runs := (packed_run_eq_iff_native asking swapped).mpr h
  rw [run_asking, run_swapped] at runs
  have mem : ((0 : Nat), FreeMonoid.of (⟨Ask.ask, ((0 : Nat), (1 : Nat)), (0 : Nat)⟩ :
      LetSeq.StraightLine.Structural.Event (α := Unit) (Φ := Ask))) ∈
      Finite.outcomes ((LetSeq.StraightLine.Structural.model (α := Unit)).eval Ask.ask ((0 : Nat), (1 : Nat))) :=
    ⟨(0 : Nat), rfl⟩
  rw [runs] at mem
  obtain ⟨reply, same⟩ := mem
  have events := FreeMonoid.of_injective (Prod.mk.inj same).2
  exact Nat.one_ne_zero (congrArg (fun e => e.argument.1) events)

example : ¬ RankedValid false (sentenceOf (entry asking) (entry swapped)) := fun valid =>
  requests_differ ((rankedValid_line_iff asking swapped).mp valid)

/-! ## A valid sentence between two graphs

The second graph is read back from the operand emitted by the first. Its
emitted operand is natively equal to the same straight-line term. -/

private def askingGraph : CheckedTable Ask (Packed captures) [tok] := lineGraph asking

private def askingAgain : CheckedTable Ask (Packed captures) [tok] :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) askingGraph.toLetCase.2

private theorem again_line : StraightLine (emitted (P := atomSig Unit Ask) (entryOf askingAgain)) :=
  StraightLine.congr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) askingGraph.toLetCase.2)
    (straightLine_lineGraph asking)

private abbrev together : RankedEquation (atomSig Unit Ask) :=
  sentenceOf (entryOf askingGraph) (entryOf askingAgain)

private theorem together_valid : RankedValid false together :=
  (rankedValid_straightLine_iff (entryOf askingGraph) (entryOf askingAgain) (straightLine_lineGraph asking)
    again_line).mpr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) askingGraph.toLetCase.2).symm

/-- The ordered trace model with atoms satisfies it. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Ask))
    (atomSig Unit Ask)).Sat (atomTraceRanked Unit Ask) together :=
  (rankedValid_straightLine_iff_atomTrace (entryOf askingGraph) (entryOf askingAgain)
    (straightLine_lineGraph asking) again_line).mp together_valid

/-- Both sentences are in the complete class. -/
example : Complete false apart ∧ Complete false together :=
  ⟨complete_of_traceReflects apart (straightLine_traceReflects (entry first) (entry second)
      (straightLine_lineGraph first) (straightLine_lineGraph second)),
    complete_of_traceReflects together (straightLine_traceReflects (entryOf askingGraph) (entryOf askingAgain)
      (straightLine_lineGraph asking) again_line)⟩

/-! ## Two translations of the atom

Both translations keep every type former and send the primitive to a
primitive of a finite structural signature. The first sends the atom to
the unit type and the second sends it to the two-tag sum. -/

private def image (X : Ty Empty) : Ty Unit → Ty Empty
  | .base _ => X
  | .unit => .unit
  | .empty => .empty
  | .product A B => .product (image X A) (image X B)
  | .coprod A B => .coprod (image X A) (image X B)

private abbrev tagShape : LetCase.Structural.Finite.Shape := .sum .unit .unit
private abbrev Tag : Ty Empty := tagShape.ty

private inductive Flat | ask
private inductive Tagged | ask

local instance : LetCase.Structural.Finite.Signature Flat := ⟨fun _ => .pair .unit .unit, fun _ => .unit⟩
local instance : LetCase.Structural.Finite.Signature Tagged := ⟨fun _ => .pair tagShape tagShape, fun _ => tagShape⟩

/-- Send the atom to the unit type. -/
private def forget : SignatureMap (atomSig Unit Ask).Instr (sig Flat).Instr (Ty Unit) (Ty Empty) Bool Bool where
  instr _ := Flat.ask
  ty := image .unit
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

/-- Send the atom to the two-tag sum. -/
private def tags : SignatureMap (atomSig Unit Ask).Instr (sig Tagged).Instr (Ty Unit) (Ty Empty) Bool Bool where
  instr _ := Tagged.ask
  ty := image Tag
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

local instance : forget.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : forget.PreservesSums := ⟨rfl, fun _ _ => rfl⟩
local instance : tags.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : tags.PreservesSums := ⟨rfl, fun _ _ => rfl⟩

example : forget.ty tok = .unit ∧ tags.ty tok = Tag := ⟨rfl, rfl⟩

/-! ## The unit translation does not reflect

Under the unit translation the two captured atoms become two values of
the unit type. The translated operands are natively equal, so the
translated sentence is valid. The original sentence is not valid. -/

private abbrev flatCtx : BoundCtx (Ty Empty) 1 := .snoc .nil (.product .unit .unit)
private abbrev flatOut : Ty Empty := packedExitType [Ty.unit]

private def firstFlat : Operand Flat flatCtx flatOut := ⟨.inl (.let₂ (.bv 0) (.bv 1)), .inl (.let₂ .bv .bv)⟩
private def secondFlat : Operand Flat flatCtx flatOut := ⟨.inl (.let₂ (.bv 0) (.bv 0)), .inl (.let₂ .bv .bv)⟩

private theorem flat_equal : Equiv false Γ₀ flatCtx firstFlat.1 secondFlat.1 flatOut :=
  (equiv_iff_traceArrow_eq_snoc .nil firstFlat.2 secondFlat.2).mpr
    ((traceArrow_eq_iff_run firstFlat.2 secondFlat.2).mpr fun ρ => by
      simp only [firstFlat, secondFlat, run, Derivation.denote]
      erw [pure_bind, pure_bind])

private theorem forgotten_derivable : Derivable false (grammarCase (readGrammar (mapRanked forget apart))) := by
  rw [readGrammar_map, grammarCase_map, emitted_case]
  have left : Equiv false Γ₀ flatCtx _ firstFlat.1 flatOut :=
    (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand first).2).mapInstr forget
  have right : Equiv false Γ₀ flatCtx _ secondFlat.1 flatOut :=
    (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand second).2).mapInstr forget
  exact (left.trans flat_equal).trans right.symm

private theorem forgotten_valid : RankedValid false (mapRanked forget apart) :=
  rankedValid_of_derivable _ forgotten_derivable

/-- The unit translation does not reflect validity of this sentence. -/
example : ¬ ReflectsValid forget false apart := fun reflects => apart_invalid (reflects forgotten_valid)

/-- It does not reflect native equality either. Forward transport is all
that it has. -/
example : ¬ ReflectsDerivable forget false apart := fun reflects =>
  apart_invalid (rankedValid_of_derivable apart (reflects forgotten_derivable))

/-! ## The two-tag translation reflects on this sentence

Under the two-tag translation the translated operands differ at the
ordered trace model of the target: an input with two different tags
separates them. The translation therefore reflects native equality of
this sentence, and validity of the sentence is decided by the pullback of
the target's ordered trace model. -/

private abbrev tagCtx : BoundCtx (Ty Empty) 1 := .snoc .nil (.product Tag Tag)
private abbrev tagOut : Ty Empty := packedExitType [Tag]

private def firstTag : Operand Tagged tagCtx tagOut := ⟨.inl (.let₂ (.bv 0) (.bv 1)), .inl (.let₂ .bv .bv)⟩
private def secondTag : Operand Tagged tagCtx tagOut := ⟨.inl (.let₂ (.bv 0) (.bv 0)), .inl (.let₂ .bv .bv)⟩

local notation "Val" => LetCase.Structural.Finite.Value

private def tagEnv : BoundEnv Val tagCtx :=
  BoundEnv.snoc (β := .nil) (fun i => i.elim0) (.inl PUnit.unit, .inr PUnit.unit)

private theorem tags_differ : ¬ Equiv false Γ₀ tagCtx firstTag.1 secondTag.1 tagOut := by
  intro h
  have runs := (traceArrow_eq_iff_run firstTag.2 secondTag.2).mp
    (traceArrow_of_valid (valid_of_equiv firstTag.2 secondTag.2 h)) tagEnv
  have mem : ((.inl (.inl PUnit.unit) : Val tagOut), (1 : Log Empty Tagged)) ∈
      (run firstTag.2 tagEnv).outcomes := by
    simp only [firstTag, run, Derivation.denote]
    erw [pure_bind, pure_bind]
    exact rfl
  rw [runs] at mem
  simp only [secondTag, run, Derivation.denote] at mem
  erw [pure_bind, pure_bind] at mem
  have same : ((.inl (.inl PUnit.unit) : Val tagOut), (1 : Log Empty Tagged)) =
      (.inl (.inr PUnit.unit), 1) := mem
  cases same

private theorem targetSeparated :
    Separated (Φ := Tagged) (grammarCase (readGrammar (mapRanked tags apart))).1.bound := by
  rw [readGrammar_map, grammarCase_map, emitted_case]
  exact separated_snoc .nil _

private theorem tagged_not_derivable : ¬ Derivable false (grammarCase (readGrammar (mapRanked tags apart))) := by
  intro h
  rw [readGrammar_map, grammarCase_map, emitted_case] at h
  have mapped : Equiv false Γ₀ tagCtx
      ((emitted (P := atomSig Unit Ask) (entry first)).1.mapInstr tags.instr)
      ((emitted (P := atomSig Unit Ask) (entry second)).1.mapInstr tags.instr) tagOut := h
  have left : Equiv false Γ₀ tagCtx _ firstTag.1 tagOut :=
    (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand first).2).mapInstr tags
  have right : Equiv false Γ₀ tagCtx _ secondTag.1 tagOut :=
    (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand second).2).mapInstr tags
  exact tags_differ (left.symm.trans (mapped.trans right))

/-- The two-tag translation reflects native equality of this sentence. -/
private theorem tags_reflect : ReflectsDerivable tags false apart := fun h => absurd h tagged_not_derivable

/-- On a straight-line sentence that is the same as reflecting validity. -/
example : ReflectsValid tags false apart :=
  (straightLine_reflectsDerivable_iff tags rfl (entry first) (entry second) (straightLine_lineGraph first)
    (straightLine_lineGraph second) targetSeparated).mp tags_reflect

/-- The pullback of the target's ordered trace model is a supported model
over the signature with the atom. It rejects the sentence, and by the
criterion it decides validity of the sentence. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Tagged))
    (atomSig Unit Ask)).Sat (ShrinkHoms.toShrinkHoms (Discrete.mk ((traceRegionModel Tagged).pullbackOfWitness tags
      (regionWitnessPullback tags (traceRegionModel Tagged))))) apart := fun holds =>
  apart_invalid ((rankedValid_iff_pulledTrace tags rfl apart targetSeparated tags_reflect).mpr holds)

/-- The same rejection without the ordered trace model with atoms: the
translated sentence is not derivable in the complete target. -/
example : ¬ RankedValid false apart := fun valid =>
  tagged_not_derivable (complete_structural (mapRanked tags apart) targetSeparated
    (rankedValid_mapRanked_typeChange tags apart valid))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
