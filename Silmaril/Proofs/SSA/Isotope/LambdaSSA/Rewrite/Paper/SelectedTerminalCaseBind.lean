module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.SelectedTerminal.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Projection.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.InputPacking.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.PackedTerm.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms

/-! # Replay of the selected table discriminator -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedTerminalCaseBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (Exits TerminalInput terminal terminalSlots)
open Paper.WithCaseBind.SelectedTerminal
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CfgEta.TypeCategory (returnRegion returnRegion_typed singletonValueFamily)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open Silmaril.DeBruijn (lift)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local instance : HasEff signature.Instr Bool := signature.hasEff

local notation "E" => Paper.Extension.Eqv Seed
local notation "quoted" => Finite.Expr.quote 2 (fun env => env 1)

private theorem inclUnary {Γ L r s} (h : Paper.UnaryReturn.Step Γ r s L) : Seed Γ r s L :=
  .inl (.inl (.inr (.inl h)))

private theorem inclPair {Γ L r s} (h : Paper.WithPairReturns.Step Γ r s L) : Seed Γ r s L :=
  .inl (.inr h)

private theorem inclProjection {Γ L r s} (h : Paper.WithProjectionReturns.Step Γ r s L) : Seed Γ r s L :=
  .inl (.inl (.inl (.inl h)))

theorem table_binds (pos : Position Exits) :
    E [TerminalInput] (terminal pos quoted).elaborate.val (boundTable pos) Exits :=
  let body := applyPacked_typed_exits (tableArm pos).elaborate.property
  Paper.WithCaseBind.case_eq_let Or.inr tableDiscriminator.elaborate.property body body

private theorem table_lowers (pos : Position Exits) :
    E [TerminalInput] (terminal pos quoted).elaborate.val
      ((returnRegion tableDiscriminator.elaborate.val).lsubst (fun _ => tableContinuation pos)) Exits :=
  let body := applyPacked_typed_exits (tableArm pos).elaborate.property
  Paper.WithCaseBind.case_eq_return_post Or.inr inclUnary tableDiscriminator.elaborate.property body body

private theorem weakSingleton {A : Ty Empty} {Γ : VCtx (Ty Empty)} :
    Ren [A] (A :: Γ) id := by
  intro i D h
  cases i with
  | zero => exact h
  | succ i => simp [At] at h

private theorem emitTrue_typed {Γ : VCtx (Ty Empty)} : Tm.HasType Γ emitTrue unit :=
  .op .unit

private theorem prefixSecond (t : Term signature.Instr TerminalInput Bit) :
    E [TerminalInput] (returnRegion (emitPrefix [true] t).elaborate.val)
      (.let₁ emitTrue (.let₁ (t.elaborate.val.rename Nat.succ) (.br 0 (.var 0)))) [Bit] :=
  Paper.WithPairReturns.return_pair_second inclPair inclProjection emitTrue_typed t.elaborate.property

private theorem direct_prefix (pos : Position Exits) :
    E [TerminalInput] (terminal pos (.read 1)).elaborate.val
      (.let₁ emitTrue (.let₁ ((terminalSlots 1).elaborate.val.rename Nat.succ) (.br pos.1 (.var 0)))) Exits :=
  (prefixSecond (terminalSlots 1)).renameLabels (singletonExitRen pos.typed)

private theorem table_prefix (pos : Position Exits) :
    E [TerminalInput] (terminal pos quoted).elaborate.val
      ((.let₁ emitTrue (.let₁ ((terminalSlots 0).elaborate.val.rename Nat.succ) (.br 0 (.var 0))) :
          Region signature.Instr).lsubst (fun _ => tableContinuation pos)) Exits := by
  let body := applyPacked_typed_exits (tableArm pos).elaborate.property
  have post : LSubst.HasType [TerminalInput] [Bit] Exits (fun _ => tableContinuation pos) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact (Paper.RetainedCase.boundCase_typed body body).hasType
    | succ i => simp [At] at hi
  let hEmit := emitTrue_typed (Γ := [TerminalInput])
  let hRead := (terminalSlots 0).elaborate.property.rename (Ren.wk [TerminalInput] unit)
  exact (table_lowers pos).trans ((prefixSecond (terminalSlots 0)).lsubstPost
    (returnRegion_typed tableDiscriminator.elaborate.property)
    (.let₁ hEmit (.let₁ hRead (.br rfl (.var (i := 0) rfl)))) post)

-- These certificates only use constructor data, unary lets, and projections.
private inductive ProjectionBeta : VCtx (Ty Empty) → Tm signature.Instr → Tm signature.Instr → Ty Empty → Prop where
  | value {Γ t A} (h : Tm.BranchValue Γ t A) : ProjectionBeta Γ t t A
  | let₁ {Γ a b c d A D} (ha : ProjectionBeta Γ a c A) (hb : Tm.HasType (A :: Γ) b D)
      (next : ProjectionBeta Γ (b.subst (Tm.singleSubst c)) d D) :
      ProjectionBeta Γ (.let₁ a b) d D
  | fst {Γ a b A B} (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B) :
      ProjectionBeta Γ (.let₂ (.pair a b) (.var 1)) a A
  | snd {Γ a b A B} (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B) :
      ProjectionBeta Γ (.let₂ (.pair a b) (.var 0)) b B

private theorem ProjectionBeta.typed {Γ t c A} (h : ProjectionBeta Γ t c A) :
    Tm.HasType Γ t A ∧ Tm.BranchValue Γ c A := by
  induction h with
  | value h => exact ⟨h.hasType, h⟩
  | let₁ _ hb _ ih₁ ih₂ => exact ⟨.let₁ ih₁.1 hb, ih₂.2⟩
  | fst a b => exact ⟨.let₂ (.pair a.hasType b.hasType) (.var (i := 1) rfl), a⟩
  | snd a b => exact ⟨.let₂ (.pair a.hasType b.hasType) (.var (i := 0) rfl), b⟩

private theorem projection_substitute {Γ X D} {a : Tm signature.Instr} {r s : Region signature.Instr}
    (e : Paper.WithProjectionReturns.Step [X] r s [D]) (aTyped : Tm.BranchValue Γ a X) :
    E Γ (r.substVars (Tm.singleSubst a)) (s.substVars (Tm.singleSubst a)) [D] := by
  have eq : E [X] r s [D] := .extra e.valueBranches.1.hasType e.valueBranches.2.hasType (inclProjection e)
  apply eq.substVars
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact aTyped
  | succ i => simp [At] at hi

private theorem oncePost (a : Tm signature.Instr) (r : Region signature.Instr) :
    (returnOnce a).lsubst (fun _ => r) = .let₁ a r := by
  change Region.let₁ a (compLSubst labelId (fun _ => r) 0) = _
  rw [compLSubst_id_left]

private theorem ProjectionBeta.once {Γ t c A} (h : ProjectionBeta Γ t c A) :
    E Γ (returnOnce t) (.br 0 c) [A] := by
  induction h with
  | value ht =>
    exact .paper (.cfgEta (.native (.letValue ht (.br rfl (.var (i := 0) rfl)))))
  | @fst a b A B ha hb =>
    have projection := projection_substitute (.fst A B) (.pair ha hb)
    exact projection.trans (.paper (.productBeta (.let₂Beta ha hb (.br rfl (.var (i := 1) rfl)))))
  | @snd a b A B ha hb =>
    have projection := projection_substitute (.snd A B) (.pair ha hb)
    exact projection.trans (.paper (.productBeta (.let₂Beta ha hb (.br rfl (.var (i := 0) rfl)))))
  | @let₁ a b c d A D ha hb next ih₁ ih₂ =>
    let fuse := Paper.UnaryReturn.Step.fuse ha.typed.1 hb
    have eq : E Γ (.let₁ a (returnOnce b)) (returnOnce (.let₁ a b)) [D] :=
      .extra fuse.valueBranches.1.hasType fuse.valueBranches.2.hasType (inclUnary fuse)
    have post := ih₁.lsubstPost (returnOnce_valueBranches ha.typed.1) (.br rfl ha.typed.2)
      (fun _ _ hi => ((singletonValueFamily (returnOnce_valueBranches hb)) hi).hasType)
    rw [oncePost] at post
    exact eq.symm.trans (post.trans ih₂)

private theorem ProjectionBeta.lowered {Γ t c A} (h : ProjectionBeta Γ t c A) :
    E Γ (returnRegion t) (.br 0 c) [A] :=
  (Paper.UnaryReturn.returnRegion_eq_returnOnce inclUnary h.typed.1).trans h.once

private theorem projectionLet {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {a c : Tm signature.Instr} {A : Ty Empty} {r : Region signature.Instr}
    (h : ProjectionBeta Γ a c A) (hr : ValueBranches (A :: Γ) r L) :
    E Γ (.let₁ a r) (r.substVars (Tm.singleSubst c)) L := by
  have post : LSubst.HasType Γ [A] L (fun _ => r) := by
    intro i D hi
    cases i with
    | zero => cases Option.some.inj hi; exact hr.hasType
    | succ i => simp [At] at hi
  have e := h.once.lsubstPost (returnOnce_valueBranches h.typed.1) (.br rfl h.typed.2) post
  rw [oncePost] at e
  exact e

private abbrev Slots : VCtx (Ty Empty) := [Bit, unit, Bit, Bit]

private def packet : Tm signature.Instr := packedInputValue Slots

private theorem packetSubst : ∀ ⦃i A⦄, At [TerminalInput] i A →
    Tm.BranchValue Slots (Tm.singleSubst packet i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact packedInputValue_branchValue Slots
  | succ i => simp [At] at hi

private def unpackedSlot (i : Fin 2) : Tm signature.Instr :=
  ((terminalSlots i).elaborate.val.rename Nat.succ).subst (Tm.liftSubst (Tm.singleSubst packet))

set_option backward.isDefEq.respectTransparency false in
private theorem oldProjection : ProjectionBeta (unit :: Slots) (unpackedSlot 1) (.var 3) Bit := by
  unfold unpackedSlot
  apply ProjectionBeta.let₁
  · apply ProjectionBeta.fst
    · repeat first | apply Tm.BranchValue.pair | exact Tm.BranchValue.unit | exact Tm.BranchValue.var rfl
    · exact .var rfl
  · repeat' first | apply Tm.HasType.let₁ | apply Tm.HasType.let₂ | exact Tm.HasType.var rfl
  · apply ProjectionBeta.let₁
    · apply ProjectionBeta.fst
      · repeat first | apply Tm.BranchValue.pair | exact Tm.BranchValue.unit | exact Tm.BranchValue.var rfl
      · exact .var rfl
    · repeat' first | apply Tm.HasType.let₂ | exact Tm.HasType.var rfl
    · apply ProjectionBeta.snd
      · repeat first | apply Tm.BranchValue.pair | exact Tm.BranchValue.unit | exact Tm.BranchValue.var rfl
      · exact .var rfl

private theorem direct_unpack (pos : Position Exits) :
    E Slots ((terminal pos (.read 1)).elaborate.val.unpackInputs Slots)
      (.let₁ emitTrue (.br pos.1 (.var 3))) Exits := by
  refine ((direct_prefix pos).substVars packetSubst).trans ?_
  exact .let₁ emitTrue_typed (projectionLet oldProjection (.br pos.typed (.var (i := 0) rfl)))

private theorem newestProjection : ProjectionBeta (unit :: Slots) (unpackedSlot 0) (.var 1) Bit := by
  apply ProjectionBeta.snd
  · repeat' first | apply Tm.BranchValue.pair | exact Tm.BranchValue.unit | exact Tm.BranchValue.var rfl
  · exact .var rfl

private theorem liftValues {Γ Δ : VCtx (Ty Empty)} {θ : Nat → Tm signature.Instr}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) (B : Ty Empty) :
    ∀ ⦃i A⦄, At (B :: Γ) i A → Tm.BranchValue (B :: Δ) (Tm.liftSubst θ i) A := by
  intro i A hi
  cases i with
  | zero => exact .var hi
  | succ i =>
    change Tm.BranchValue (B :: Δ) ((θ i).rename Nat.succ) A
    rw [Tm.rename_eq_subst]
    exact (hθ hi).subst (fun _ _ h => .var (Ren.wk Δ B h))

private def unpackedTableContinuation (pos : Position Exits) : Region signature.Instr :=
  ((tableContinuation pos).renameVars (lift Nat.succ)).substVars
    (Tm.liftSubstN 2 (Tm.singleSubst packet))

private theorem tableContinuation_valueBranches (pos : Position Exits) :
    ValueBranches [Bit, TerminalInput] (tableContinuation pos) Exits :=
  let body := applyPacked_typed_exits (tableArm pos).elaborate.property
  Paper.RetainedCase.boundCase_typed body body

private theorem unpackedTableContinuation_typed (pos : Position Exits) :
    ValueBranches (Bit :: unit :: Slots) (unpackedTableContinuation pos) Exits :=
  ((tableContinuation_valueBranches pos).renameVars ((Ren.wk [TerminalInput] unit).lift Bit)).substVars
    (liftValues (liftValues packetSubst unit) Bit)

private theorem table_unpack_test (pos : Position Exits) :
    E Slots ((terminal pos quoted).elaborate.val.unpackInputs Slots)
      (.let₁ emitTrue ((unpackedTableContinuation pos).substVars (Tm.singleSubst (.var 1)))) Exits := by
  have splitPrefix :
      (Region.let₁ emitTrue (.let₁ ((terminalSlots 0).elaborate.val.rename Nat.succ)
        (.br 0 (.var 0)))).lsubst (fun _ => tableContinuation pos) =
        Region.let₁ emitTrue (.let₁ ((terminalSlots 0).elaborate.val.rename Nat.succ)
          ((tableContinuation pos).renameVars (lift Nat.succ))) := by
    change Region.let₁ emitTrue
      ((returnOnce ((terminalSlots 0).elaborate.val.rename Nat.succ)).lsubst
        (fun _ => (tableContinuation pos).renameVars (lift Nat.succ))) = _
    rw [oncePost]
  have moved := table_prefix pos
  rw [splitPrefix] at moved
  refine (moved.substVars packetSubst).trans ?_
  exact .let₁ emitTrue_typed (projectionLet newestProjection (unpackedTableContinuation_typed pos))

private def innerTest : Tm signature.Instr :=
  let a := Paper.PackedBody.applyPackedTerm (retainSlot (A := unit) (terminalSlots 1)).elaborate.val
  let b := (a.rename (lift Nat.succ)).rename (lift (lift Nat.succ))
  (b.subst (Tm.liftSubstN 3 (Tm.singleSubst packet))).subst (Tm.liftSubst (Tm.singleSubst (.var 1)))

set_option backward.isDefEq.respectTransparency false in
private theorem innerProjection : ProjectionBeta (unit :: unit :: Slots) innerTest (.var 4) Bit := by
  unfold innerTest
  repeat' first
    | apply ProjectionBeta.let₁
    | apply ProjectionBeta.fst
    | apply ProjectionBeta.snd
    | apply Tm.HasType.let₁
    | apply Tm.HasType.let₂
    | exact Tm.HasType.var rfl
    | apply Tm.BranchValue.pair
    | exact Tm.BranchValue.unit
    | exact Tm.BranchValue.var rfl

private def injectBit (right : Bool) (a : Tm signature.Instr) : Tm signature.Instr :=
  if right then .inr a else .inl a

private def literalBranch (pos : Position Exits) (right : Bool) : Region signature.Instr :=
  .let₁ .unit (.br pos.1 (injectBit right (.var 0)))

private theorem injectBit_typed {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr} (right : Bool)
    (ht : Tm.BranchValue Γ a unit) : Tm.BranchValue Γ (injectBit right a) Bit := by
  cases right
  · exact .inl ht
  · exact .inr ht

private theorem literalBranch_typed {Γ : VCtx (Ty Empty)} (pos : Position Exits) (right : Bool) :
    ValueBranches Γ (literalBranch pos right) Exits :=
  .let₁ .unit (.br pos.typed (injectBit_typed right (.var (i := 0) rfl)))

private theorem retagUnit {Γ : VCtx (Ty Empty)} (pos : Position Exits) (right : Bool) :
    E (unit :: Γ) (literalBranch pos right) (.br pos.1 (injectBit right (.var 0))) Exits := by
  have unitEq : E [unit]
      (.br 0 .unit) (.br 0 (.var 0)) [unit] :=
    .extra (.br rfl .unit) (.br rfl (.var (i := 0) rfl))
      (.inl (.inl (.inl (.inr .unit))))
  have captured : E (unit :: Γ) (.br 0 .unit) (.br 0 (.var 0)) [unit] := by
    simpa only [renameVars_id] using unitEq.renameVars (weakSingleton (A := (unit : Ty Empty)) (Γ := Γ))
  have post : LSubst.HasType (unit :: Γ) [unit] Exits (fun _ => .br pos.1 (injectBit right (.var 0))) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .br pos.typed (injectBit_typed right (.var (i := 0) rfl)).hasType
    | succ i => simp [At] at hi
  have retag := captured.lsubstPost (.br rfl .unit) (.br rfl (.var (i := 0) rfl)) post
  have beta : E (unit :: Γ) (literalBranch pos right)
      ((Region.br pos.1 (injectBit right (.var 0))).substVars (Tm.singleSubst .unit)) Exits :=
    .paper (.cfgEta (.native (.letValue .unit
      (.br pos.typed (injectBit_typed right (.var (i := 0) rfl)).hasType))))
  cases right <;> exact beta.trans retag

private theorem innerTest_returns (pos : Position Exits) :
    E (unit :: unit :: Slots) (.case innerTest (literalBranch pos false) (literalBranch pos true))
      (.br pos.1 (.var 4)) Exits := by
  let hl := literalBranch_typed (Γ := unit :: unit :: unit :: Slots) pos false
  let hr := literalBranch_typed (Γ := unit :: unit :: unit :: Slots) pos true
  have step := Paper.WithCaseBind.case_eq_return_post Or.inr inclUnary innerProjection.typed.1 hl hr
  have post : LSubst.HasType (unit :: unit :: Slots) [Bit] Exits
      (fun _ => Paper.RetainedCase.boundCase (literalBranch pos false) (literalBranch pos true)) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact (Paper.RetainedCase.boundCase_typed hl hr).hasType
    | succ i => simp [At] at hi
  refine step.trans ((innerProjection.lowered).lsubstPost
    (returnRegion_typed innerProjection.typed.1) (.br rfl innerProjection.typed.2) post) |>.trans ?_
  change E (unit :: unit :: Slots) (.case (.var 4) (literalBranch pos false) (literalBranch pos true))
    (.br pos.1 (.var 4)) Exits
  refine (Paper.Extension.Eqv.case (.var (i := 4) rfl) (retagUnit pos false) (retagUnit pos true)).trans ?_
  exact .paper (.cfgEta (.native (.caseValue (.var (i := 4) rfl) (.br pos.typed (.var (i := 0) rfl)))))

private theorem table_unpack (pos : Position Exits) :
    E Slots ((terminal pos quoted).elaborate.val.unpackInputs Slots)
      (.let₁ emitTrue (.br pos.1 (.var 3))) Exits := by
  refine (table_unpack_test pos).trans (.let₁ emitTrue_typed ?_)
  change E (unit :: Slots)
    (.case (.var 1)
      (.case innerTest (literalBranch pos false) (literalBranch pos true))
      (.case innerTest (literalBranch pos false) (literalBranch pos true))) (.br pos.1 (.var 3)) Exits
  refine (Paper.Extension.Eqv.case (.var (i := 1) rfl) (innerTest_returns pos) (innerTest_returns pos)).trans ?_
  exact .paper (.cfgEta (.native (.caseValue (.var (i := 1) rfl) (.br pos.typed (.var (i := 4) rfl)))))

private theorem includePacking {Γ L : List (Ty Empty)} {r s : Region signature.Instr}
    (h : Paper.Extension.Eqv Paper.WithProjectionReturnsAndUnitEta.Step Γ r s L) : E Γ r s L := by
  induction h with
  | paper h => exact .paper h
  | extra hr hs h => exact .extra hr hs (.inl (.inl (.inl h)))
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp _ ih => exact .lsubstCongr hp ih
  | lsubstPost _ hr hs hσ ih => exact .lsubstPost ih hr hs hσ
  | substVars _ hθ ih => exact .substVars ih hθ
  | renameLabels _ hρ ih => exact .renameLabels ih hρ

private theorem split_congr (Γ : VCtx (Ty Empty)) {Δ : VCtx (Ty Empty)} {i : Nat}
    {r s : Region signature.Instr} {L : LCtx (Ty Empty)}
    (hi : At Δ i (packedInputType Γ)) (h : E (InputDestructure.expanded Γ Δ) r s L) :
    E Δ (InputDestructure.split Γ i r) (InputDestructure.split Γ i s) L := by
  induction Γ generalizing Δ i with
  | nil => exact h
  | cons A Γ ih => exact .let₂ (.var hi) (ih (i := 1) rfl h)

theorem terminal_eq (pos : Position Exits) :
    E [TerminalInput] (terminal pos (.read 1)).elaborate.val (terminal pos quoted).elaborate.val Exits := by
  let hd := (terminal pos (.read 1)).elaborate.property
  let ht := (terminal pos quoted).elaborate.property
  have unpacked := (direct_unpack pos).trans (table_unpack pos).symm
  have packed := split_congr Slots (i := 0) rfl (unpacked.renameVars (InputDestructure.fieldRen Slots [TerminalInput]))
  exact (includePacking (Paper.WithProjectionReturnsAndUnitEta.InputPacking.repack_unpack (Γ := Slots)
    hd.hasType)).symm.trans (packed.trans
    (includePacking (Paper.WithProjectionReturnsAndUnitEta.InputPacking.repack_unpack (Γ := Slots) ht.hasType)))

theorem packed_eq :
    Paper.Extension.Singleton.ofRegion Seed
      CaseTree.ReplyAgreement.NativeReplay.direct.selected.elaborate.property.packExits =
    Paper.Extension.Singleton.ofRegion Seed
      CaseTree.ReplyAgreement.NativeReplay.table.selected.elaborate.property.packExits :=
  CaseTree.ReplyAgreement.NativeReplay.packed_of_terminal
    (terminal_eq CaseTree.ReplyAgreement.NativeReplay.first)
    (terminal_eq CaseTree.ReplyAgreement.NativeReplay.second)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedTerminalCaseBind
