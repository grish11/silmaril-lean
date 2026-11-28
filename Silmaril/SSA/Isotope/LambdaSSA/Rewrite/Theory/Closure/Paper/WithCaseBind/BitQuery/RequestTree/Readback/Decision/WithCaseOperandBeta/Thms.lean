module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.WithCaseOperandBeta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Obstruction.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryCaseOperandModel
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryCaseOperandReplay

/-! # Model soundness and exact replay of the opt-in operand beta -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

theorem operand_beta : CaseOperandBetaIn Eqv :=
  BitQueryCaseOperandReplay.operand_beta

/-- Successful admission reuses #4792's staged reader and preserves the
literal packed arrow of the supplied original program in the opt-in quotient. -/
theorem read_packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : readTermCase fuel p = some t) : packed p = packedTree t :=
  BitQueryCaseOperandReplay.read_packed_eq h

theorem original_packed_eq_quote (label : Bool) : packed (original label) = packedTree (quote label) :=
  BitQueryCaseOperandReplay.original_packed_eq_quote label

/-- The literal original closed packed arrows from the default obstruction
become equal after adjoining only the focused beta step. -/
theorem closed_packed_eq (label b : Bool) :
    (Paper.Extension.Singleton.projection Step).map (Obstruction.sourcePacked label b) =
      (Paper.Extension.Singleton.projection Step).map (Obstruction.targetPacked label b) :=
  BitQueryCaseOperandReplay.closed_packed_eq label b

/-- The staged reader expands the two known input tags while forwarding the
actual request reply payload to its ordered exit. -/
theorem read_original (label : Bool) :
    readTermCase 8 (original label) =
      some (.ask label (.split (.literal false) (.literal true)) (.ret false 0) (.ret true 0)) := by
  cases label <;> rfl

universe u v x y
variable {V : Type u} {C : Type v} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (M : TypeModel (Ty Empty) V)
  [InstructionModel J M signature.Instr]

/-- The constructor-known case and the selected literal have a common term
arrow whenever the constructor payload has its named pure value witness. -/
theorem operand_denotes {Γ : List (Ty Empty)} {payload : Tm signature.Instr} (b : Bool)
    (h : Tm.BranchValue Γ payload U) (p : ctxObj M Γ ⟶ M.obj U)
    (hval : Denotes J M h.hasType (J.map p)) :
    ∃ f, Denotes J M (operand_typed b h) f ∧
      Denotes J M ((constructorBit_value (Γ := Γ) b .unit).hasType) f :=
  BitQueryCaseOperandModel.operand_denotes J M b h p hval

/-- Compose the same named operand arrow with the actual instruction and
both reply continuations. This structural witness needs no coherence. -/
theorem region_denotes {Γ L : List (Ty Empty)} {payload : Tm signature.Instr}
    (label b : Bool) (h : Tm.BranchValue Γ payload U) (p : ctxObj M Γ ⟶ M.obj U)
    (hval : Denotes J M h.hasType (J.map p)) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    ∃ f, RegionDenotes J M (source_typed label b h hl hr).hasType f ∧
      RegionDenotes J M (target_typed label b hl hr).hasType f :=
  BitQueryCaseOperandModel.region_denotes J M label b h p hval hl hr

theorem step_denotes : Paper.Extension.Singleton.SeedDenotes (Seed := Step) J M :=
  BitQueryCaseOperandModel.step_denotes J M

theorem closed_packed_denotes (label b : Bool) :
    ∃ f,
      RegionDenotes J M (Obstruction.source_typed label b).packExits.hasType f ∧
      RegionDenotes J M (Obstruction.target_typed label b).packExits.hasType f :=
  BitQueryCaseOperandModel.closed_packed_denotes J M label b

variable [RegionTypingCoherent (Φ := signature.Instr) J M]

theorem closed_singleton_eq (label b : Bool) :
    denoteSingletonRegion J M (Obstruction.source_typed label b).packExits.hasType =
      denoteSingletonRegion J M (Obstruction.target_typed label b).packExits.hasType := by
  obtain ⟨_, ds, dt⟩ := closed_packed_denotes J M label b
  unfold denoteSingletonRegion
  rw [(ds.eq_denote J M).symm.trans (dt.eq_denote J M)]

/-- A fixed pair of distinct original arrows has equal denotation in every
model of the stated class. -/
theorem closed_default_gap (label b : Bool) :
    Obstruction.sourcePacked label b ≠ Obstruction.targetPacked label b ∧
      denoteSingletonRegion J M (Obstruction.source_typed label b).packExits.hasType =
        denoteSingletonRegion J M (Obstruction.target_typed label b).packExits.hasType :=
  ⟨Obstruction.packed_ne label b, closed_singleton_eq J M label b⟩

variable [FreydCategory.CentralUnit J]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared in
/-- The existing contextual closure soundness applies to the single new rule. -/
theorem Eqv.sound {Γ L : List (Ty Empty)} {r s : Region signature.Instr}
    (h : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (step_denotes J M) h hr hs

include shared in
/-- Every stated Paper model functor identifies the same distinct default
singleton arrows. -/
theorem default_denote_not_faithful :
    ¬ (Paper.TypeCategory.denoteFunctor (Φ := signature.Instr) J M shared).Faithful := by
  intro faithful
  apply Obstruction.packed_ne false false
  apply faithful.map_injective
  change Paper.TypeCategory.denoteArrow J M (Obstruction.sourcePacked false false) =
    Paper.TypeCategory.denoteArrow J M (Obstruction.targetPacked false false)
  simpa only [Obstruction.sourcePacked, Obstruction.targetPacked, Paper.TypeCategory.denoteArrow_ofRegion J M shared]
    using closed_singleton_eq J M false false

/-- The actual singleton quotient admits the existing coherent model lift. -/
noncomputable def denoteFunctor :=
  Paper.Extension.Singleton.denoteFunctor J M shared (step_denotes J M)

include shared in
theorem read_singleton_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : readTermCase fuel p = some t) :
    denoteSingletonRegion J M p.property.packExits.hasType =
      denoteSingletonRegion J M t.guarded_typed.packExits.hasType := by
  have mapped := congrArg (fun f => (denoteFunctor J M shared).map f) (read_packed_eq h)
  simp only [packed, packedTree, denoteFunctor, Paper.Extension.Singleton.denoteFunctor_map_ofRegion] at mapped
  exact mapped

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta
