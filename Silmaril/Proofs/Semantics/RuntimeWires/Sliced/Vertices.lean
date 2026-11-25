module

public import Silmaril.Semantics.RuntimeWires.Sliced.Defs

public section

namespace Silmaril.RuntimeWires.Proofs.Sliced

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private theorem count_pass (W : List O) {A B : List O} (r : Row S A B) :
    (Row.pass W r).boxCount = r.boxCount := by
  induction W with
  | nil => rfl
  | cons x W ih => exact ih

private theorem count_straight (W : List O) : (Row.straight (S := S) W).boxCount = 0 := by
  induction W with
  | nil => rfl
  | cons x W ih => exact ih

private theorem count_split {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (h : Row.Split S r p q) : r.boxCount = p.boxCount + q.boxCount := by
  induction h with
  | empty => rfl
  | wire _ _ ih => exact ih
  | upper _ _ ih =>
    simp only [Row.boxCount, count_pass, ih]
    omega
  | lower _ _ ih =>
    simp only [Row.boxCount, count_pass, ih, Nat.add_assoc]

private theorem count_move {A B : List O} {p q : Sheet S A B} (h : Sheet.Move S p q) :
    p.boxCount = q.boxCount := by
  induction h with
  | split h tail => simp only [Sheet.boxCount, count_split h, Nat.add_assoc]
  | straight tail => simp only [Sheet.boxCount, count_straight, Nat.zero_add]
  | under _ _ ih => simp only [Sheet.boxCount, ih]

theorem count_seam {A B : List O} {p q : Sheet S A B} (h : Sheet.SeamEquivalent p q) :
    p.boxCount = q.boxCount := by
  induction h with
  | rel _ _ h => exact count_move h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Silmaril.RuntimeWires.Proofs.Sliced
