module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.TypeChange.Marked.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (TypeSignature)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation grammarCase readGrammar mapRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## Three marked signatures

The first has an atom and effects in the natural numbers, with marker
zero. The second has the same types and Boolean effects, with marker
false. The third is the fixture's structural signature. -/

private abbrev Atomic := Ty Unit
private abbrev atom : Atomic := .base ()

private inductive Counted | ask
private inductive Abstract | ask

local instance : HasTy Counted Atomic := ⟨fun _ => .product atom atom, fun _ => atom⟩
local instance : HasEff Counted Nat := ⟨fun _ => 1⟩
local instance : HasTy Abstract Atomic := ⟨fun _ => .product atom atom, fun _ => atom⟩
local instance : HasEff Abstract Bool := ⟨fun _ => true⟩

private abbrev counted : InstrSig Atomic Nat := ⟨Counted⟩
private abbrev abstract : InstrSig Atomic Bool := ⟨Abstract⟩

private abbrev first : MarkedSignature := ⟨⟨Atomic, Nat, counted⟩, 0⟩
private abbrev second : MarkedSignature := ⟨⟨Atomic, Bool, abstract⟩, false⟩
private abbrev third : MarkedSignature := ⟨⟨Ty Empty, Bool, sig Op⟩, false⟩

/-- The effect map is not the identity: it sends a count to whether it is
positive. Types are unchanged. -/
private def positive : SignatureMap counted.Instr abstract.Instr Atomic Atomic Nat Bool where
  instr _ := Abstract.ask
  ty := id
  eff n := decide (n ≠ 0)
  source _ := rfl
  target _ := rfl
  effect _ := rfl

local instance : positive.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : positive.PreservesSums := ⟨rfl, fun _ _ => rfl⟩

private def collapse : Atomic → Ty Empty
  | .base _ => Bit
  | .unit => .unit
  | .empty => .empty
  | .product A B => .product (collapse A) (collapse B)
  | .coprod A B => .coprod (collapse A) (collapse B)

/-- The type map is not the identity: it sends the atom to the two-tag
sum. Effects are unchanged. -/
private def translate : SignatureMap abstract.Instr (sig Op).Instr Atomic (Ty Empty) Bool Bool where
  instr _ := Op.ask
  ty := collapse
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

local instance : translate.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : translate.PreservesSums := ⟨rfl, fun _ _ => rfl⟩

/-- Both maps preserve the chosen markers. -/
private def stepEffect : first ⟶ second := ⟨⟨positive⟩, rfl⟩
private def stepType : second ⟶ third := ⟨⟨translate⟩, rfl⟩

example : positive.eff 1 = true ∧ positive.eff 0 = false ∧ translate.ty atom = Bit := ⟨rfl, rfl, rfl⟩

/-! ## The functor on the composite -/

private noncomputable abbrev inst := supportedMarkedInst (traceJ (α := Empty) (Φ := Op))

example : inst.map (stepEffect ≫ stepType) = inst.map stepEffect ≫ inst.map stepType :=
  inst.map_comp stepEffect stepType

example : inst.map (𝟙 first) = 𝟙 (inst.obj first) := inst.map_id first

/-- Each step is the corridor of #5031 along its signature map. -/
example : inst.map stepType = supportedTypeCorridor translate (traceJ (α := Empty) (Φ := Op)) false :=
  supportedMarkedCorridor_mk translate false

example : inst.map stepEffect = supportedTypeCorridor positive (traceJ (α := Empty) (Φ := Op)) 0 :=
  supportedMarkedCorridor_mk positive 0

/-- The supported ordered trace model over the structural signature. -/
private noncomputable abbrev top : (inst.obj third).Mod :=
  ShrinkHoms.toShrinkHoms (Discrete.mk ⟨traceRegionModel Op, trace_supported⟩)

/-- The composite corridor sends it to the pullback along the type map
followed by the pullback along the effect map. -/
private theorem composite_model : (inst.map (stepEffect ≫ stepType)).mod.obj top =
    (inst.map stepEffect).mod.obj ((inst.map stepType).mod.obj top) :=
  congrArg (fun c => c.mod.obj top) (inst.map_comp stepEffect stepType)

/-- The model over the first signature. It is supported at marker zero. -/
private noncomputable abbrev bottom : (inst.obj first).Mod :=
  (inst.map stepEffect).mod.obj ((inst.map stepType).mod.obj top)

example : Supported 0 bottom.fromShrinkHoms.as.1 := bottom.fromShrinkHoms.as.2

/-! ## A captured sentence over the first signature -/

private abbrev older : BoundCtx Atomic 1 := .snoc .nil atom
private abbrev sourceCtx : BoundCtx Atomic 2 := older.snoc (packedExitType [Ty.unit])
private abbrev outs : LCtx Atomic := [atom]

private theorem outs_nonempty : outs ≠ [] := List.cons_ne_nil _ _

/-- Ask with the older capture twice and return the reply. -/
private def asking : Operand Counted sourceCtx (packedExitType outs) :=
  ⟨.inl (.op Counted.ask (.pair (.bv 1) (.bv 1))), .inl (.op (.pair .bv .bv))⟩

private def askingGraph : CheckedTable Counted sourceCtx outs := CheckedTable.ofLetCase outs_nonempty asking.2

private def askingAgain : CheckedTable Counted sourceCtx outs :=
  CheckedTable.ofLetCase outs_nonempty askingGraph.toLetCase.2

private def entryOf (c : CheckedTable Counted sourceCtx outs) : RankedEntry Counted sourceCtx outs :=
  ⟨c.size, c.table, c.checked, 0, c.entry⟩

private abbrev sentence : RankedEquation counted := ⟨⟨2, sourceCtx, outs⟩, entryOf askingGraph, entryOf askingAgain⟩

private theorem derivable : Derivable (0 : Nat) (grammarCase (readGrammar sentence)) :=
  (derivable_iff 0 sentence).mpr (CheckedTable.ofLetCase_emit (0 : Nat) outs_nonempty askingGraph.toLetCase.2).symm

/-- Soundness at the twice pulled-back model, which is supported. -/
private theorem holds_bottom : (inst.obj first).Sat bottom sentence :=
  sat_of_derivable bottom.fromShrinkHoms.as.1 bottom.fromShrinkHoms.as.2 sentence derivable

/-- The satisfaction condition of the composite corridor carries it to
the structural model, for the sentence translated along both maps. -/
example : (inst.obj third).Sat top ((inst.map (stepEffect ≫ stepType)).sen sentence) :=
  ((inst.map (stepEffect ≫ stepType)).sat top sentence).mpr (composite_model ▸ holds_bottom)

/-- Translating along the composite is translating along each map in turn. -/
example : (inst.map (stepEffect ≫ stepType)).sen sentence =
    (inst.map stepType).sen ((inst.map stepEffect).sen sentence) :=
  congrArg (fun c => c.sen sentence) (inst.map_comp stepEffect stepType)

/-- After both maps the older capture is the two-tag sum. -/
example : ((inst.map stepType).sen ((inst.map stepEffect).sen sentence)).1.bound =
    (BoundCtx.snoc .nil Bit).snoc (packedExitType [Ty.unit]) := rfl

/-- Validity in the supported models moves along the composite, from
marker zero to marker false. -/
example : RankedValid false (mapRanked (translate.comp positive) sentence) :=
  rankedValid_mapRanked_typeChange (pe := (0 : Nat)) (translate.comp positive) sentence
    (rankedValid_of_derivable sentence derivable)

/-! ## Comparison with the unrestricted rooms -/

private noncomputable abbrev comparison := supportedComparison (traceJ (α := Empty) (Φ := Op))

/-- Forgetting the marker and then restricting models commutes with both
steps and with their composite. -/
example : (MarkedSignature.forget ⋙ Silmaril.Isotope.Institution.Acyclic.Captured.rankedInst
      (traceJ (α := Empty) (Φ := Op))).map stepEffect ≫ comparison.app second =
    comparison.app first ≫ inst.map stepEffect :=
  comparison.naturality stepEffect

example : (MarkedSignature.forget ⋙ Silmaril.Isotope.Institution.Acyclic.Captured.rankedInst
      (traceJ (α := Empty) (Φ := Op))).map (stepEffect ≫ stepType) ≫ comparison.app third =
    comparison.app first ≫ inst.map (stepEffect ≫ stepType) :=
  comparison.naturality (stepEffect ≫ stepType)

/-- The comparison keeps sentences and sends a supported model to itself. -/
example : (comparison.app first).sen sentence = sentence := rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
