module

public import Silmaril.Logic.SetTheory.Nat

@[expose] public section

/-!
# Set operations for extensional dependent type theory

Functions are graphs, dependent pairs are Kuratowski pairs, and identity types
are empty or singleton sets. These operations do not squash functions or pairs
as the separate GT3 interpretation does.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSem

universe u

open ZFSet

noncomputable section
open Classical

/-- The singleton set interpreting the unit type. -/
def tt : ZFSet.{u} := {∅}

/-- The set interpreting a proposition as an extensional identity type. -/
def truth (p : Prop) : ZFSet.{u} := if p then tt else ∅

/-- A dependent pair is an ordinary Kuratowski pair. -/
abbrev pair (a b : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair a b

/-- First projection, with the empty set as its value off ordered pairs. -/
def fst (p : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ a b, p = pair a b then h.choose else ∅

/-- Second projection, with the empty set as its value off ordered pairs. -/
def snd (p : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ a b, p = pair a b then h.choose_spec.choose else ∅

/-- The graph of a function restricted to the set `A`. -/
def lam (A : ZFSet.{u}) (g : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : A => pair x.1 (g x.1)

/-- Graph application, with the empty set as its value when no output exists. -/
def app (f a : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ b, pair a b ∈ f then h.choose else ∅

/-- The dependent product, represented by graphs of its sections. -/
def pi (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun s : ((x : A) → B x.1) =>
    lam A fun y => if h : y ∈ A then (s ⟨y, h⟩).1 else ∅

/-- The dependent sum, represented by ordered pairs. -/
def sigma (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun p : (Σ x : A, B x.1) => pair p.1.1 p.2.1

/-- Primitive recursion on von Neumann numerals; the value off `ω` is empty. -/
def natrec (z : ZFSet.{u}) (s : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (m : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ n : ℕ, Silmaril.Logic.SetTheory.numeral n = m then
    Nat.rec z (fun n r => s (Silmaril.Logic.SetTheory.numeral n) r) h.choose
  else ∅

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSem
