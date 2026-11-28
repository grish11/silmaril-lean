module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Tests

open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv HasType Pure)
open LetCase.Structural.Finite (Context Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LambdaSSA.Semantics (Env extend)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

section EmptyTail

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {X : Types}

private def inject (β : Context n) (X : Types) : Operand Φ (β.snoc X) (.coprod X .empty) :=
  ⟨.inl (.bv 0), .inl .bv⟩

private def remove (β : Context n) (X : Types) : Operand Φ (β.snoc (.coprod X .empty)) X :=
  ⟨.case (.bv 0) (.bv 0) (.abort (.bv 0)), .case .bv .bv (.abort .bv)⟩

private theorem remove_inl :
    Equiv false (Φ := Φ) Γ₀ (β.snoc X) (.case (.inl (.bv 0)) (.bv 0) (.abort (.bv 0))) (.bv 0) X :=
  (Equiv.caseBetaL (B := Ty.empty) .bv .bv (.abort .bv)).trans (Equiv.letEta .bv)

example : Pure false (inject (Φ := Φ) β X).1 ∧ Pure false (remove (Φ := Φ) β X).1 :=
  ⟨.inl .bv, .case .bv .bv (.abort .bv)⟩

example : Equiv false Γ₀ (β.snoc X)
    (.let₁ (inject (Φ := Φ) β X).1 (remove (β.snoc X) X).1) (.bv 0) X :=
  (Equiv.letBeta (.inl .bv) (inject β X).2.toHasType (remove (β.snoc X) X).2.toHasType).trans remove_inl

example : Equiv false Γ₀ (β.snoc (.coprod X .empty))
    (.let₁ (remove (Φ := Φ) β X).1 (inject (β.snoc (.coprod X .empty)) X).1) (.bv 0) (.coprod X .empty) := by
  apply (LetCase.Structural.Finite.equiv_coprod_empty_iff
    (.let₁ (remove β X).2.toHasType (inject (β.snoc (.coprod X .empty)) X).2.toHasType) .bv).mpr
  change Equiv false Γ₀ (β.snoc X)
    (.let₁ (.case (.inl (.bv 0)) (.bv 0) (.abort (.bv 0))) (.inl (.bv 0))) (.inl (.bv 0)) (.coprod X .empty)
  have e : HasType Φ Γ₀ (β.snoc X) (.bv 0) X := .bv
  have rebuild : HasType Φ Γ₀ ((β.snoc X).snoc X) (.inl (.bv 0)) (.coprod X .empty) := .inl .bv
  exact (Equiv.let₁ remove_inl (.refl rebuild)).trans (Equiv.letBeta .bv e rebuild)

end EmptyTail

private inductive Op | observe

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev captures : Context 1 := .snoc .nil bitShape.ty
private abbrev exits : LCtx Types := [.unit, .unit]
private abbrev Packet := packedExitType exits
private abbrev Source := captures.snoc Packet

local instance : LetCase.Structural.Finite.Signature Op where
  source _ := .pair bitShape bitShape
  target _ := bitShape

private def consumer : CheckedTable Op Source exits where
  size := 0
  table :=
    { types := fun _ => .unit
      block := fun _ => .case
        ⟨.op .observe (.pair (.bv 2) (.case (.bv 1) (.inl .unit) (.inr .unit))),
          .op (.pair .bv (.case .bv (.inl .unit) (.inr .unit)))⟩
        (.exit (i := 0) rfl) (.exit (i := 1) rfl) }
  checked := rfl
  entry := ⟨.unit, .unit⟩

private theorem input : StructuralContext captures := .snoc .nil bitShape
private theorem nonempty : exits ≠ [] := List.cons_ne_nil _ _

private def linked : CheckedTable Op Source exits := seq (identity nonempty) consumer

example : ReplayEqv false Source.toList (linked.table.packedSSA 0 linked.entry)
    (consumer.table.packedSSA 0 consumer.entry) [Packet] :=
  left_identity_replay input nonempty consumer

example :
    seqClass input (⟦identity nonempty⟧ : Hom Op captures exits exits) ⟦consumer⟧ = ⟦consumer⟧ :=
  left_identity input nonempty ⟦consumer⟧

private abbrev low : Value Empty := .inl .unit
private abbrev high : Value Empty := .inr .unit
private abbrev tag₂ : Value Empty := .inr low
private def env (x : Value Empty) : Env Empty := extend (extend (fun _ => .unit) high) x

/-- The observer insists on the older high capture and returns the input tag
selected from the two identical outward payloads. -/
private def observe (_ : Op) (x : Value Empty) (s : Nat) (y : Value Empty) (s' : Nat) : Prop :=
  ((x = .pair high low ∧ y = low) ∨ (x = .pair high high ∧ y = high)) ∧ s' = s + 1

private abbrev eval := LambdaSSA.Semantics.Region.Eval observe

/-- The actual linked packed evaluator keeps each tag and calls the original
consumer exactly once with the older capture. -/
example : eval (env low) (linked.table.packedSSA 0 linked.entry) 0 0 low 1 := by
  refine .cfg (.let₁ .var (.br .var)) (.step (next := 3) (middle := .unit) (s₁ := 0) (by decide) ?_
    (.step (next := 5) (middle := .pair low .unit) (s₁ := 0) (by decide) ?_
      (.step (next := 6) (by decide) ?_ (.exit (by decide)))))
  · exact .case_inl .var (.let₁ .var (.br .var))
  · exact .let₁ (.let₁ (.inl .var) (.pair .var .unit)) (.br .var)
  · exact .case_inl (.let₂ .var (.case_inl (.op (.pair .var (.case_inl .var (.inl .unit)))
      ⟨.inl ⟨rfl, rfl⟩, rfl⟩) (.inl .var))) (.let₁ .var (.br (.inl .var)))

example : eval (env tag₂) (linked.table.packedSSA 0 linked.entry) 0 0 tag₂ 1 := by
  refine .cfg (.let₁ .var (.br .var)) (.step (next := 1) (middle := low) (s₁ := 0) (by decide) ?_
    (.step (next := 4) (middle := .unit) (s₁ := 0) (by decide) ?_
      (.step (next := 5) (middle := .pair tag₂ .unit) (s₁ := 0) (by decide) ?_
        (.step (next := 6) (by decide) ?_ (.exit (by decide))))))
  · exact .case_inr .var (.let₁ .var (.br .var))
  · exact .case_inl .var (.let₁ .var (.br .var))
  · exact .let₁ (.let₁ (.inr (.inl .var)) (.pair .var .unit)) (.br .var)
  · exact .case_inr (.let₂ .var (.case_inr (.op (.pair .var (.case_inr .var (.inr .unit)))
      ⟨.inr ⟨rfl, rfl⟩, rfl⟩) (.inr .var))) (.let₁ .var (.br (.inr (.inl .var))))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Tests
