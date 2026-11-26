module

import Silmaril.SSA.Isotope.LetParCase.Thms
import Mathlib.Control.Monad.Writer

open Silmaril Silmaril.Isotope Silmaril.Isotope.Parallel Silmaril.Isotope.Semantics

private inductive Instr where
  | emit (tag : Nat)

private instance : HasTy Instr (Ty Unit) where
  src _ := .unit
  trg _ := .base ()

private instance : HasEff Instr Bool where
  eff _ := true

private abbrev D := Ty.denote (fun _ : Unit => Nat)
private abbrev Γ : Ctx Empty (Ty Unit) := .nil
private abbrev number : Ty Unit := .base ()

private abbrev count (α : Type) := Writer Nat α
private instance : Monad count := WriterT.monad 0 Nat.add

private def countInstr : InstructionModel D Instr count where
  eval
    | .emit tag, _ => WriterT.mk (tag, tag)

/-- Combine the branch logs by addition while retaining the order of the result values. -/
private def countPar : ParOp count := fun a b =>
  WriterT.mk ((a.run.1, b.run.1), a.run.2 + b.run.2)

private abbrev closedFree : FreeEnv D Γ := fun x => nomatch x
private abbrev closedBound : BoundEnv D .nil := fun i => Fin.elim0 i

private def emit (tag : Nat) : LetPar.Tm Empty Instr 0 := .op (.emit tag) .unit

private def emitD (tag : Nat) : Derivation Instr Γ .nil (emit tag) number :=
  .op .unit

/-- Both effects occur, and the tuple preserves the left and right result positions. -/
example :
    ((Derivation.par (emitD 2) (emitD 7)).denote D countInstr countPar
      (Control.seq D count) closedFree closedBound).run = (((2 : Nat), (7 : Nat)), 9) :=
  rfl

example :
    LetPar.Equiv false Γ .nil ((Tm.par (emit 2) (emit 7)).swap) (.par (emit 7) (emit 2))
      (product number number) :=
  Equiv.parSwap ⟨emitD 2⟩ ⟨emitD 7⟩

private def choose (left : Bool) : LetParCase.Tm Empty Instr 0 :=
  .case LetParCase.hasCase
    (if left then .inl LetParCase.hasCase .unit else .inr LetParCase.hasCase .unit)
    (.op (.emit 1) (.bv 0)) (.op (.emit 2) (.bv 0))

private def chooseD (left : Bool) : Derivation Instr Γ .nil (choose left) number :=
  .case (match left with | true => .inl .unit | false => .inr .unit) (.op .bv) (.op .bv)

private def runChoice (left : Bool) : (Nat × Nat) × Nat :=
  ((Derivation.par (chooseD left) (LetParCase.ofLetParDerivation (emitD 4))).denote D
    countInstr countPar (Control.case D count) closedFree closedBound).run

/-- For either tag, the selected arm and the independent sibling contribute their effects. -/
example : runChoice true = ((1, 4), 5) ∧ runChoice false = ((2, 4), 6) :=
  ⟨rfl, rfl⟩

example :
    LetParCase.Equiv false Γ .nil (.par (choose true) (LetParCase.ofLetPar (emit 4)))
      (.case LetParCase.hasCase (.inl LetParCase.hasCase .unit)
        (.par (.op (.emit 1) (.bv 0)) (LetParCase.ofLetPar (emit 4)).lift)
        (.par (.op (.emit 2) (.bv 0)) (LetParCase.ofLetPar (emit 4)).lift))
      (product number number) :=
  LetParCase.parCaseLeft (X := Ty.unit) (Y := Ty.unit) (.inl .unit) ⟨.inl .unit⟩ ⟨.op .bv⟩ ⟨.op .bv⟩
    ⟨LetParCase.ofLetParDerivation (emitD 4)⟩

private abbrev trace (α : Type) := Writer (List Nat) α

private def traceInstr : InstructionModel D Instr trace where
  eval
    | .emit tag, _ => WriterT.mk (tag, [tag])

private def leftFirst : ParOp trace := fun a b => do
  let x ← a
  let y ← b
  pure (x, y)

private def swapped : Derivation Instr Γ .nil ((Tm.par (emit 2) (emit 7)).swap)
    (product number number) :=
  .let₂ (.par (emitD 2) (emitD 7)) (.pair .bv .bv)

private def runTrace {t : LetPar.Tm Empty Instr 0} {A : Ty Unit}
    (d : Derivation Instr Γ .nil t A) : D A × List Nat :=
  (d.denote D traceInstr leftFirst (Control.seq D trace) closedFree closedBound).run

/-- Sequential replacement of Par fails the swap equation in an ordered effect model. -/
example : runTrace swapped ≠ runTrace (.par (emitD 7) (emitD 2)) := by
  change (((7, 2), [2, 7]) : (Nat × Nat) × List Nat) ≠ ((7, 2), [7, 2])
  decide

#print axioms Silmaril.Isotope.Parallel.Tm.widen_injective
#print axioms Silmaril.Isotope.Parallel.Equiv.parMap
#print axioms Silmaril.Isotope.LetPar.embed_injective
#print axioms Silmaril.Isotope.LetPar.embed_equiv
#print axioms Silmaril.Isotope.LetPar.denote_derivation
#print axioms Silmaril.Isotope.LetParCase.embed_injective
#print axioms Silmaril.Isotope.LetParCase.embed_equiv
#print axioms Silmaril.Isotope.LetParCase.denote_derivation
#print axioms Silmaril.Isotope.LetParCase.embed_seqCase
