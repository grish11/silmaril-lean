module

import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv Tm)
open Reply (Γ₀)
open LetSeq.StraightLine.Structural (Event Log)
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Generator where
  | choose
  | emit

private abbrev bit : Shape := .sum .unit .unit
private abbrev packet : Shape := .pair bit .unit

private instance : Signature Generator where
  source
    | .choose => bit
    | .emit => .unit
  target
    | .choose => bit
    | .emit => .unit

private abbrev input : Context 1 := .snoc .nil packet.ty

private def argument : Term Generator 1 :=
  .let₂ (.bv 0) (.case (.op .choose (.bv 1)) (.op .emit .unit) .unit)

private def argumentTyping : Derivation Generator Γ₀ input argument .unit :=
  .let₂ .bv (.case (.op .bv) (.op .unit) .unit)

private def assignment : Assignment input :=
  Fin.cases (.pair (.inl .unit) .unit) (fun i => i.elim0)

-- Actual nested primitive argument, product destruction and reply case.
example : Normalizes .unit ((Tm.op .emit argument).bsubst assignment.terms) :=
  normalize (.op (f := Generator.emit) argumentTyping) assignment

-- Open reflection compares the whole native terms, with the argument's
-- effects evaluated before the outer call.
example : Equiv false Γ₀ input (.op .emit argument) (.let₁ argument (.op .emit (.bv 0))) .unit := by
  let slot : Derivation Generator Γ₀ (input.snoc .unit) (.bv 0) .unit := .bv
  apply (equiv_iff_traceArrow_eq (.snoc .nil packet) (.op (f := Generator.emit) argumentTyping)
    (.let₁ argumentTyping (.op (f := Generator.emit) slot))).mpr
  apply (Reply.traceArrow_eq_iff_run (.op (f := Generator.emit) argumentTyping) (.let₁ argumentTyping (.op (f := Generator.emit) slot))).mpr
  intro ρ
  simp only [slot, Reply.run, Derivation.denote, pure_bind]
  rfl

private def runLeft : Derivation Generator Γ₀ .nil (.op Generator.choose (.inl .unit)) bit.ty :=
  .op (.inl .unit)

private def runRight : Derivation Generator Γ₀ .nil (.op Generator.choose (.inr .unit)) bit.ty :=
  .op (.inr .unit)

-- Either call can reply with the left tag. The recorded constructor
-- argument still separates the heads of the two actual native terms.
example : ¬ Equiv false Γ₀ .nil (.op Generator.choose (.inl .unit)) (.op Generator.choose (.inr .unit)) bit.ty := by
  intro native
  let ρ : Silmaril.Isotope.Semantics.BoundEnv Value (.nil : Context 0) := fun i => i.elim0
  have eq := (Reply.traceArrow_eq_iff_run runLeft runRight).mp
    ((equiv_iff_traceArrow_eq .nil runLeft runRight).mp native) ρ
  let left : Value bit.ty := .inl ()
  let right : Value bit.ty := .inr ()
  let log : Log Empty Generator := FreeMonoid.of ⟨.choose, left, left⟩
  simp only [runLeft, runRight, Reply.run, Derivation.denote, pure_bind] at eq
  let tr := (LetSeq.StraightLine.Structural.model (α := Empty) (Φ := Generator))
  have obs : (left, log) ∈ (tr.eval .choose left).outcomes := ⟨left, rfl⟩
  change tr.eval .choose left = tr.eval .choose right at eq
  rw [eq] at obs
  obtain ⟨reply, witness⟩ := obs
  have same : Event.mk (α := Empty) Generator.choose right reply =
      Event.mk Generator.choose left left := by
    exact (List.cons.inj (congrArg FreeMonoid.toList (Prod.mk.inj witness).2)).1
  have impossible : (Sum.inr PUnit.unit : PUnit ⊕ PUnit) = Sum.inl PUnit.unit :=
    eq_of_heq (Event.mk.inj same).2.1
  cases impossible

end Silmaril.Isotope.LetCase.Structural.Finite
