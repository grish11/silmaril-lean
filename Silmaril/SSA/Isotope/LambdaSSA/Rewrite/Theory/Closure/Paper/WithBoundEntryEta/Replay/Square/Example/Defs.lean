module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Defs

/-! # Two requests in a repeating square that forgets a state tag -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.SquareReplay.Example

open CategoryTheory CategoryTheory.Limits
open WithEntryLet.OperandExample (Bit D X forget)
open Paper.EntryLetObstruction (U blocks)
open SequencingObstruction (Instruction)
open Paper.TypeCategory (ofRegion discardArrow sumCofan sumIso)
open Generators (weakenRows)

abbrev Seed := WithBoundEntryEta.Step (τ := Ty Empty) (Φ := Instruction)

def tick : Tm Instruction := .op .tick .unit

def discriminate : Tm Instruction := .let₁ tick (.inl .unit)
def leftEntry : Region Instruction := .br 0 (.var 0)
def rightEntry : Region Instruction := .br 1 (.var 0)
def entry : Region Instruction := .case discriminate leftEntry rightEntry

def work : Region Instruction := .cfg (.let₁ tick entry) 2 blocks
def movedWork : Region Instruction := .let₁ tick (.cfg entry 2 (weakenRows blocks))

def repeatExit : Region Instruction := .br 0 (.inr .unit)

def flatRows : Fin 2 → Region Instruction :=
  fun j => ((weakenRows blocks) j).lsubst (liftLSubstVars
    (liftLSubstN 2 (liftLSubstVars (liftLSubstVars (fun _ => repeatExit)))))

def writtenFlat : Region Instruction := compLSubst (fun _ => work) (fun _ => repeatExit) 0

def flat : Region Instruction := compLSubst (fun _ => movedWork) (fun _ => repeatExit) 0

def hoisted : Region Instruction :=
  .let₁ tick (.case discriminate
    (.cfg leftEntry 2 (weakenRows flatRows)) (.cfg rightEntry 2 (weakenRows flatRows)))

def site : WithEntryLet.Site := .unaryBody .here

private theorem rowsTyped {Γ : VCtx (Ty Empty)} (j : Fin 2) :
    ValueBranches (U :: Γ) (blocks j) [U, U, U] :=
  Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl)) j

private theorem discriminatorTyped {Γ : VCtx (Ty Empty)} :
    Tm.HasType Γ discriminate Bit :=
  .let₁ (.op .unit) (.inl .unit)

private theorem entryTyped {Γ : VCtx (Ty Empty)} : ValueBranches Γ entry [U, U, U] :=
  .case discriminatorTyped (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl))

theorem workTyped : ValueBranches [U] work [U] :=
  .cfg (fun _ : Fin 2 => U) (.let₁ (.op .unit) entryTyped) rowsTyped

theorem movedWorkTyped : ValueBranches [U] movedWork [U] :=
  NativeFrame.letCaseTable_guarded (fun _ : Fin 2 => U) (.op .unit) discriminatorTyped
    (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl)) rowsTyped

theorem repeatTyped : ValueBranches [U] repeatExit [Bit] := .br rfl (.inr .unit)

theorem writtenFlatTyped : ValueBranches [U] writtenFlat [Bit] :=
  CfgEta.TypeCategory.seqValueBranches workTyped repeatTyped

theorem flatTyped : ValueBranches [U] flat [Bit] :=
  CfgEta.TypeCategory.seqValueBranches movedWorkTyped repeatTyped

theorem hoistedTyped : ValueBranches [U] hoisted [Bit] :=
  (CaseReplay.hoistAt_guarded site flatTyped rfl).1

noncomputable def post : X ⟶ X ⨿ D :=
  discardArrow U ≫ (sumCofan U U).inl ≫ coprod.inr

noncomputable def source : D ⟶ X ⨿ D :=
  forget ≫ ofRegion workTyped ≫ post

noncomputable def movedSource : D ⟶ X ⨿ D :=
  forget ≫ ofRegion movedWorkTyped ≫ post

noncomputable def target : X ⟶ X ⨿ X := ofRegion hoistedTyped ≫ (sumIso U U).hom

/-- Reuse the same round while routing each input tag to the opposite tag. -/
noncomputable def alternating (round : X ⟶ X) : D ⟶ X ⨿ D :=
  NativeFrame.split forget round (sumCofan U U).inr (sumCofan U U).inl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.SquareReplay.Example
