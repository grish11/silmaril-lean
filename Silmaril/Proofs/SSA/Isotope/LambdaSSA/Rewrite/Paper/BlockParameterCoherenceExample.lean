module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms

/-! # Parameter-reading rows with exact native CFG witnesses -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.BlockParameterFixture

open CategoryTheory CategoryTheory.Limits
open UnusedSummand.BlockParameters
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

private inductive Op where
  | load
  | inspect

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Flag : Ty Empty := Silmaril.coprod U U
private abbrev Result : Ty Empty := Silmaril.product U Flag

instance : HasTy Op (Ty Empty) where
  src
    | .load => U
    | .inspect => Flag
  trg _ := Flag

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def liveFamily (dead : Ty Empty) : Fin 3 → Ty Empty :=
  Fin.cases Flag (Fin.cases Flag (fun _ => dead))

private def table : Program (Φ := Op) (liveFamily U) [U, Result] [Flag] where
  entry := .jump 0 (.op Op.load .unit)
  blocks := Fin.cases
    (.parameter (.jump 1 (.var 0 rfl)))
    (Fin.cases
      (.parameter (.case (.op Op.inspect (.var 0 rfl))
        (.exit 0 rfl (.var 0 rfl))
        (.exit 1 rfl (.pair (.var 0 rfl) (.var 2 rfl)))))
      (fun _ => .captured (.exit 0 rfl .unit)))

private def entry : Region Op := .br 0 (.op Op.load .unit)

private def blocks : Fin 3 → Region Op :=
  Fin.cases (.br 1 (.var 0))
    (Fin.cases (.case (.op Op.inspect (.var 0))
      (.br 3 (.var 0)) (.br 4 (.pair (.var 0) (.var 2)))) (fun _ => .br 3 .unit))

private theorem raw_region : table.region = .cfg entry 3 blocks := by
  unfold Program.region table blocks
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

private theorem reachesFirst : table.Reaches 0 := .entry rfl

private theorem reachesSecond : table.Reaches 1 := .next reachesFirst rfl

private theorem target_index {i : Fin 3} (hit : table.targets i) : i = 0 ∨ i = 1 := by
  rcases hit with hit | ⟨j, hit⟩
  · exact .inl (show (0 : Fin 3) = i from hit).symm
  · revert hit
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ h => h.elim)) j
    · exact fun h => .inr (show (1 : Fin 3) = i from h).symm
    · rintro (h | h) <;> exact h.elim

private theorem closed : table.ReachableParameters where
  targets i hit := by
    rcases target_index hit with rfl | rfl
    · exact reachesFirst
    · exact reachesSecond
  parameters i :=
    Fin.cases (fun _ => reachesFirst)
      (Fin.cases (fun _ => reachesSecond) (fun _ h => h.elim)) i

private theorem noJumpToThird : ¬ table.targets 2 := by
  intro hit
  rcases target_index hit with h | h <;> contradiction

private theorem entry_typed (D : Ty Empty) :
    entry.HasType [Flag] (List.ofFn (liveFamily D) ++ [U, Result]) :=
  .br rfl (.op .unit)

private theorem blocks_typed (D : Ty Empty) (i : Fin 3) :
    (blocks i).HasType (liveFamily D i :: [Flag]) (List.ofFn (liveFamily D) ++ [U, Result]) :=
  Fin.cases (.br rfl (.var rfl))
    (Fin.cases (.case (.op (.var rfl))
      (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))) (fun _ => .br rfl .unit)) i

private theorem families_differ : liveFamily U ≠ liveFamily .empty := by
  intro eq
  have last := congrFun eq (2 : Fin 3)
  change Ty.unit = Ty.empty at last
  cases last

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, Result])

/-- Exact witnesses exist independently at both internal families. -/
example :
    (∃ f : Arrow, CfgDenotesAt J M (liveFamily U) entry blocks f) ∧
    (∃ g : Arrow, CfgDenotesAt J M (liveFamily .empty) entry blocks g) :=
  ⟨CfgDenotesAt.exists_of_typing J M _ (entry_typed U) (blocks_typed U),
   CfgDenotesAt.exists_of_typing J M _ (entry_typed .empty) (blocks_typed .empty)⟩

/-- The entry loads a flag at label 0. The next block forwards that parameter
to label 1, where the inspect instruction consumes it. Both outward indices keep
their payload types and the unwritten slot can have either type. -/
example (roll : IterationRolling C) :
    (¬ table.targets 2) ∧ (liveFamily U ≠ liveFamily .empty) ∧
    ∀ {f g : Arrow},
      CfgDenotesAt J M (liveFamily U) entry blocks f →
      CfgDenotesAt J M (liveFamily .empty) entry blocks g → f = g := by
  refine ⟨noJumpToThird, families_differ, ?_⟩
  intro f g d e
  have assemble {S : Fin 3 → Ty Empty} {x : Arrow} (w : CfgDenotesAt J M S entry blocks x) :
      ∃ ht : table.region.HasType [Flag] [U, Result], RegionDenotes J M ht x := by
    rw [raw_region]
    obtain ⟨he, hb, _, _, _, de, db, dc, rfl⟩ := w
    exact ⟨_, .cfg he hb de db dc⟩
  obtain ⟨_, left⟩ := assemble d
  obtain ⟨_, right⟩ := assemble e
  exact table.denotes_eq J M roll closed left right

end Model

private def cycleEntry : Region Op := .br 0 (.inl .unit)

private def cycleBlocks : Fin 2 → Region Op :=
  Fin.cases (.br 1 (.var 0)) (fun _ => .br 0 (.var 0))

private def cycleFamily (D : Ty Empty) : Fin 2 → Ty Empty := fun _ => Silmaril.coprod U D

private theorem cycleEntry_typed (D : Ty Empty) :
    cycleEntry.HasType [] (List.ofFn (cycleFamily D) ++ [U]) :=
  .br rfl (.inl .unit)

private theorem cycleBlocks_typed (D : Ty Empty) (i : Fin 2) :
    (cycleBlocks i).HasType [cycleFamily D i] (List.ofFn (cycleFamily D) ++ [U]) :=
  Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl)) i

/-- The two reached blocks only forward the sum to each other. With no
synthesizing entry argument, their right summands remain undetermined
even at the fixed outward interface. -/
example : ¬ LabelsDetermined [] [U] cycleEntry cycleBlocks (cycleFamily U) := by
  intro fixed
  have eq := fixed (cycleFamily .empty) (cycleEntry_typed .empty) (cycleBlocks_typed .empty)
  have component := congrFun eq (0 : Fin 2)
  have impossible := (Ty.coprod.inj component).2
  cases impossible

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.BlockParameterFixture
