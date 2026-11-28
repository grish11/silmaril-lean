module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.SelectedTerminal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedTerminalCaseBind

/-! # Native replay of the selected read/table fixture -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.SelectedTerminal

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay
  (TerminalInput Exits terminal direct table)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local instance : HasEff signature.Instr Bool := signature.hasEff

local notation "E" => Extension.Eqv Seed
local notation "quoted" => Finite.Expr.quote 2 (fun env => env 1)

/-- The new equation binds the table's actual emitted discriminator. -/
theorem table_binds (pos : Position Exits) :
    E [TerminalInput] (terminal pos quoted).elaborate.val (boundTable pos) Exits :=
  SelectedTerminalCaseBind.table_binds pos

/-- The exact direct and table terminals agree in the ordered-pair join with
case binding. After input unpacking, both emit once and return the retained bit. -/
theorem terminal_eq (pos : Position Exits) :
    E [TerminalInput] (terminal pos (.read 1)).elaborate.val (terminal pos quoted).elaborate.val Exits :=
  SelectedTerminalCaseBind.terminal_eq pos

/-- The actual closed arrows replay in the opt-in quotient with their
two typed exit positions preserved. -/
theorem packed_eq :
    Extension.Singleton.ofRegion Seed direct.selected.elaborate.property.packExits =
      Extension.Singleton.ofRegion Seed table.selected.elaborate.property.packExits :=
  SelectedTerminalCaseBind.packed_eq

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Extension.Singleton (SeedDenotes)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M signature.Instr]
  [RegionTypingCoherent (Φ := signature.Instr) J M]

/-- The fixture's join has common denotations in the existing coherent shared-tensor models. -/
theorem seed_denotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) :
    SeedDenotes (Seed := Seed) J M :=
  WithCaseBind.joined_seedDenotes J M (WithPairReturns.joined_seedDenotes J M shared false)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.SelectedTerminal
