module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Semantic.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Tests

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open Morphism (SignatureMap)

private abbrev A : Ty Bool := .base false
private abbrev B : Ty Bool := .base true
private abbrev C₀ : Ty Unit := .base ()
private abbrev D₀ : Ty Nat := .base 7

private def signature {α : Type} (X Y : Ty α) : InstrSig (Ty α) Unit where
  Instr := Bool
  hasTy := ⟨fun _ => .coprod X Y, fun _ => .coprod X Y⟩
  hasEff := ⟨fun _ => ()⟩

private abbrev source := signature A B
private abbrev target := signature C₀ C₀
private abbrev wider := signature D₀ D₀

private def collapse : SignatureMap source.Instr target.Instr (Ty Bool) (Ty Unit) Unit Unit where
  instr := Bool.not
  ty := Ty.map (fun _ => ())
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

private def widen : SignatureMap target.Instr wider.Instr (Ty Unit) (Ty Nat) Unit Unit where
  instr := Bool.not
  ty := Ty.map (fun _ => 7)
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

local instance : collapse.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : collapse.PreservesSums := ⟨rfl, fun _ _ => rfl⟩
local instance : widen.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
local instance : widen.PreservesSums := ⟨rfl, fun _ _ => rfl⟩

private abbrev ambient : BoundCtx (Ty Bool) 2 := .snoc (.snoc .nil A) (.coprod A B)
private abbrev exits := [A, B]
private abbrev packets : Fin 2 → Ty Bool := ![.coprod A A, A]

/-- Both arms of block zero go to block one. It inspects the ambient sum
after the primitive, so the two original outward positions are both used. -/
private abbrev shared : Table source.Instr ambient exits 1 where
  types := packets
  block := fun i => Fin.cases (motive := fun j => Block source.Instr ambient packets exits (packets j))
    (.case ⟨.bv 0, .bv⟩ (.local 1) (.local 1))
    (fun j => Fin.cases (motive := fun j => Block source.Instr ambient packets exits (packets j.succ))
      (.case ⟨.op false (.bv 1), .op .bv⟩ (.exit (i := 0) rfl) (.exit (i := 1) rfl))
      (fun k => k.elim0) j) i

private def start : Operand source.Instr ambient (packets 0) := ⟨.inl (.bv 1), .inl .bv⟩

private theorem sharedChecked : shared.check = true := by cbv

private def pointed : RankedEntry source.Instr ambient exits :=
  ⟨1, shared, sharedChecked, 0, start⟩

private def rebuilt : RankedEntry source.Instr ambient exits :=
  ofGrammar pointed.toGrammar

example : (List.finRange 2).map pointed.table.localTargets = [[1, 1], []] := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rebuilt_size : rebuilt.size = 2 := by
  change (ofGrammar (tableProgram shared sharedChecked 0 start)).size = 2
  unfold tableProgram
  rw [tableTree.eq_def]
  change (ofGrammar ⟨packets 0, start,
    .case ⟨.bv 0, .bv⟩ (.local (tableTree shared sharedChecked 1))
      (.local (tableTree shared sharedChecked 1))⟩).size = 2
  rw [tableTree.eq_def]
  rfl

/-- The shared local successor becomes two blocks in the round trip. -/
example : rebuilt.size ≠ pointed.size := by rw [rebuilt_size]; decide

private def equation : RankedEquation source := ⟨⟨2, ambient, exits⟩, pointed, rebuilt⟩

example : (mapRanked collapse equation).1.exits = [C₀, C₀] := rfl

example : (List.finRange 2).map (pointed.mapSignature collapse).table.localTargets =
    [[1, 1], []] := by
  change (List.finRange 2).map (shared.mapSignature collapse).localTargets = _
  rw [Table.localTargets_mapSignature]
  rfl

/-- After both exit types collapse, the instruction is relabelled and the
native targets still select two different outward positions. -/
example : ((pointed.mapSignature collapse).table.block 1).toSSA =
    .case (.op true (.var 1)) (.br 2 (.var 0)) (.br 3 (.var 0)) := rfl

example : grammarCase (readGrammar (mapRanked (widen.comp collapse) equation)) =
    mapCaseSignature widen (mapCaseSignature collapse (grammarCase (readGrammar equation))) := by
  rw [mapRanked_comp, readGrammar_map, readGrammar_map, grammarCase_map, grammarCase_map]

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The nontrivial equation holds in every coherent model after collapsing the
exit types, and holds in the corresponding actual validated LetCase algebra. -/
example (M : (grammarRoom J target).Mod) :
    (grammarRoom J target).Sat M (readGrammar (mapRanked collapse equation)) :=
  (sat_readGrammar M _).mpr
    ((sat_mapRanked collapse _ equation).mpr (denoteRanked_roundTrip _ pointed).symm)

end Silmaril.Isotope.Institution.Acyclic.Captured.Tests
