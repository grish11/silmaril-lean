module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.TypeChange.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel regionWitnessPullback)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation grammarCase readGrammar mapRanked
  readGrammar_map grammarCase_map)
open Silmaril.Semantics.NondeterministicTrace (Finite)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Reply (Γ₀ run traceArrow_eq_iff_run traceArrow_of_valid valid_of_equiv)
open LetSeq.StraightLine.Structural (Log Trace)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (StructuralContext)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## A source signature with an atom

The source types have one atom. The primitive takes two atoms and returns
one. The type translation sends the atom to the two-tag sum, so the source
primitive lands on the fixture's structural primitive. -/

private abbrev Atomic := Ty Unit
private abbrev atom : Atomic := .base ()

private inductive Abstract | ask

local instance : HasTy Abstract Atomic := ⟨fun _ => .product atom atom, fun _ => atom⟩
local instance : HasEff Abstract Bool := ⟨fun _ => true⟩

private abbrev source : InstrSig Atomic Bool := ⟨Abstract⟩

/-- Send the atom to the two-tag sum and keep every type former. -/
private def collapse : Atomic → Ty Empty
  | .base _ => Bit
  | .unit => .unit
  | .empty => .empty
  | .product A B => .product (collapse A) (collapse B)
  | .coprod A B => .coprod (collapse A) (collapse B)

/-- The signature map. Its type translation is not the identity: the
source and target type universes differ. -/
private def translate : SignatureMap source.Instr (sig Op).Instr Atomic (Ty Empty) Bool Bool where
  instr _ := Op.ask
  ty := collapse
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

local instance : translate.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : translate.PreservesSums := ⟨rfl, fun _ _ => rfl⟩

example : collapse atom = Bit ∧ collapse (.product atom atom) = .product Bit Bit := ⟨rfl, rfl⟩

/-! ## The pullback of a supported model is supported -/

/-- The supported ordered trace model over the structural target. -/
private noncomputable abbrev target := traceRegionModel Op

private theorem witness :
    Silmaril.Isotope.Institution.Acyclic.RegionWitnessPullback (P := source) (Q := sig Op) translate target :=
  regionWitnessPullback (P := source) (Q := sig Op) translate target

/-- Its pullback: a model over the source signature, whose atom is
interpreted by the values of the two-tag sum. -/
private noncomputable abbrev pulled : CoherentRegionModel (traceJ (α := Empty) (Φ := Op)) source :=
  target.pullbackOfWitness (P := source) (Q := sig Op) translate witness

private theorem pulled_supported : Supported false pulled :=
  supported_pullback (P := source) (Q := sig Op) (pe := false) translate target witness trace_supported

/-- The existing ranked signature map along the translation. -/
private abbrev move (e : RankedEquation source) : RankedEquation (sig Op) :=
  mapRanked (P := source) (Q := sig Op) translate e

/-- The atom is interpreted by the interpretation of the two-tag sum. -/
example : pulled.types.obj atom = target.types.obj Bit := rfl

/-! ## A captured ranked sentence over the source signature

The older capture has the atom type. The packet is a literal packed input
with its empty tail. -/

private abbrev older : BoundCtx Atomic 1 := .snoc .nil atom
private abbrev packetIn : Atomic := packedExitType [Ty.unit]
private abbrev sourceCtx : BoundCtx Atomic 2 := older.snoc packetIn
private abbrev outs : LCtx Atomic := [atom]

private theorem outs_nonempty : outs ≠ [] := List.cons_ne_nil _ _

/-- Ask with the older capture twice and return the reply. -/
private def asking : Operand Abstract sourceCtx (packedExitType outs) :=
  ⟨.inl (.op Abstract.ask (.pair (.bv 1) (.bv 1))), .inl (.op (.pair .bv .bv))⟩

private def askingGraph : CheckedTable Abstract sourceCtx outs := CheckedTable.ofLetCase outs_nonempty asking.2

/-- The graph read back from the operand emitted by the first graph. -/
private def askingAgain : CheckedTable Abstract sourceCtx outs :=
  CheckedTable.ofLetCase outs_nonempty askingGraph.toLetCase.2

example : askingGraph.table.check = true ∧ askingAgain.table.check = true := ⟨rfl, rfl⟩

private def entryOf (c : CheckedTable Abstract sourceCtx outs) : RankedEntry Abstract sourceCtx outs :=
  ⟨c.size, c.table, c.checked, 0, c.entry⟩

/-- The sentence between the two graphs. They are different graphs with
natively equal emitted operands. -/
private abbrev sentence : RankedEquation source := ⟨⟨2, sourceCtx, outs⟩, entryOf askingGraph, entryOf askingAgain⟩

private theorem derivable : Derivable false (grammarCase (readGrammar sentence)) :=
  (derivable_iff false sentence).mpr
    (CheckedTable.ofLetCase_emit false outs_nonempty askingGraph.toLetCase.2).symm

/-! ## Closure and soundness on the source side -/

/-- Soundness applies at the pulled-back model because it is supported. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) source).Sat
    (ShrinkHoms.toShrinkHoms (Discrete.mk pulled)) sentence :=
  sat_of_derivable pulled
    pulled_supported sentence derivable

/-- The satisfaction square along the type-changing map. -/
private theorem square :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk target)) (move sentence) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) source).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk pulled)) sentence :=
  sat_pullback (P := source) (Q := sig Op) translate target sentence

/-- Validity is carried to the translated sentence by the model law. -/
example : RankedValid false (move sentence) :=
  rankedValid_mapRanked_typeChange (P := source) (Q := sig Op) (pe := false) translate sentence
    (rankedValid_of_derivable sentence derivable)

/-- The translated sentence has the translated bound context: the older
capture is now the two-tag sum. -/
example : (move sentence).1.bound = (BoundCtx.snoc .nil Bit).snoc (packedExitType [Ty.unit]) := rfl

/-! ## Reflection stays on the structural side

Completeness is a statement about the ordered trace model over the
structural target signature. It applies to the translated sentence. It is
not a statement about the source signature, whose types have an atom. -/

private theorem targetInput : StructuralContext (BoundCtx.snoc .nil Bit) := .snoc .nil bitShape

example : RankedValid false (move sentence) ↔
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
      (ShrinkHoms.toShrinkHoms (Discrete.mk target)) (move sentence) :=
  rankedValid_iff_trace (move sentence) (by rw [emitted_case]; exact separated_snoc targetInput _)

/-- Satisfaction at the pulled-back model is decided on the target side. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) source).Sat
    (ShrinkHoms.toShrinkHoms (Discrete.mk pulled)) sentence ↔
      Derivable false (grammarCase (readGrammar (move sentence))) :=
  square.symm.trans ((rankedValid_iff_trace (move sentence)
    (by rw [emitted_case]; exact separated_snoc targetInput _)).symm.trans
    (rankedValid_iff (move sentence) (by rw [emitted_case]; exact separated_snoc targetInput _)))

/-! ## A sentence the pulled-back model rejects

Return the older capture without asking. The translated operands differ at
the ordered trace model: one logs a request and the other logs nothing. -/

private def returning : Operand Abstract sourceCtx (packedExitType outs) :=
  ⟨.inl (.bv 1), .inl .bv⟩

private def returningGraph : CheckedTable Abstract sourceCtx outs :=
  CheckedTable.ofLetCase outs_nonempty returning.2

private abbrev rejected : RankedEquation source :=
  ⟨⟨2, sourceCtx, outs⟩, entryOf askingGraph, entryOf returningGraph⟩

private abbrev targetCtx : BoundCtx (Ty Empty) 2 := (BoundCtx.snoc .nil Bit).snoc (packedExitType [Ty.unit])
private abbrev targetOut : Ty Empty := packedExitType [Bit]

private def askingTarget : Operand Op targetCtx targetOut :=
  ⟨.inl (.op Op.ask (.pair (.bv 1) (.bv 1))), .inl (.op (.pair .bv .bv))⟩

private def returningTarget : Operand Op targetCtx targetOut :=
  ⟨.inl (.bv 1), .inl .bv⟩

local notation "Val" => LetCase.Structural.Finite.Value

private def env : BoundEnv Val targetCtx :=
  (BoundEnv.snoc (β := .nil) (fun i => i.elim0) (.inl PUnit.unit)).snoc (.inl PUnit.unit)

set_option backward.isDefEq.respectTransparency false in
private theorem targets_differ : ¬ Equiv false Γ₀ targetCtx askingTarget.1 returningTarget.1 targetOut := by
  intro h
  have runs := (traceArrow_eq_iff_run askingTarget.2 returningTarget.2).mp
    (traceArrow_of_valid (valid_of_equiv askingTarget.2 returningTarget.2 h)) env
  have silent : ((.inl (.inl PUnit.unit) : Val targetOut), (1 : Log Empty Op)) ∈
      (run returningTarget.2 env).outcomes := by
    simp only [returningTarget, run, Derivation.denote]
    erw [pure_bind]
    exact rfl
  rw [← runs] at silent
  simp only [askingTarget, run, Derivation.denote] at silent
  erw [pure_bind, pure_bind] at silent
  obtain ⟨reply, logged, rest, asked, -, joined⟩ := Finite.mem_bind.mp silent
  obtain ⟨argument, first, second, -, evaluated, split⟩ := Finite.mem_bind.mp asked
  obtain ⟨answer, same⟩ := evaluated
  obtain ⟨-, rfl⟩ := Prod.mk.inj same
  have lists := congrArg FreeMonoid.toList joined
  rw [← split] at lists
  simp [FreeMonoid.toList_mul, FreeMonoid.toList_of, FreeMonoid.toList_one] at lists

private theorem rejected_not_derivable : ¬ Derivable false (grammarCase (readGrammar (move rejected))) := by
  intro h
  rw [readGrammar_map, grammarCase_map, emitted_case] at h
  have mapped : Equiv false Γ₀ targetCtx
      ((emitted (P := source) (entryOf askingGraph)).1.mapInstr translate.instr)
      ((emitted (P := source) (entryOf returningGraph)).1.mapInstr translate.instr) targetOut := h
  have left : Equiv false Γ₀ targetCtx _ askingTarget.1 targetOut :=
    (CheckedTable.ofLetCase_emit false outs_nonempty asking.2).mapInstr translate
  have right : Equiv false Γ₀ targetCtx _ returningTarget.1 targetOut :=
    (CheckedTable.ofLetCase_emit false outs_nonempty returning.2).mapInstr translate
  exact targets_differ (left.symm.trans (mapped.trans right))

/-- The pulled-back model is a supported model over the source signature
that rejects this sentence. The rejection is computed on the target side. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) source).Sat
    (ShrinkHoms.toShrinkHoms (Discrete.mk pulled)) rejected := fun holds =>
  rejected_not_derivable (derivable_of_trace (move rejected)
    (by rw [emitted_case]; exact separated_snoc targetInput _)
    ((sat_pullback (P := source) (Q := sig Op) translate target rejected).mpr holds))

/-! ## The restricted rooms -/

/-- The corridor of restricted rooms sends the supported target model to
the supported pullback. -/
example : (supportedTypeCorridor (P := source) (Q := sig Op) translate (traceJ (α := Empty) (Φ := Op)) false).mod.obj
      (ShrinkHoms.toShrinkHoms (Discrete.mk ⟨target, trace_supported⟩)) =
    ShrinkHoms.toShrinkHoms (Discrete.mk ⟨pulled, pulled_supported⟩) := rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
