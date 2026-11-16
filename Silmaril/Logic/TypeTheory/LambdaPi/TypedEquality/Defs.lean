module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Defs

@[expose] public section

/-!
# Scoped typed equality for LF

This is an independent rule system on the shared scoped syntax. Its only
sort axiom is Type : Kind, and products quantify over Type. Signatures may declare constants at either sort; local context extensions
require a type at Type. Globals occupy the initial segment of the scoped telescope.
There are no rules for the extra MLTT constructors in the shared syntax, raw
conversion, reflection, or assumed target typings. Relating ordinary native
LF derivations to this presentation remains a separate completeness problem.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- The two LF sorts, represented at target universe levels zero and one. -/
abbrev LFSort := Fin 2

mutual

/-- Independently checked global declarations, represented as telescope parameters. -/
inductive SignatureFormed : {n : ℕ} → Context n → Prop
  | nil : SignatureFormed .nil
  | snoc {n : ℕ} {S : Context n} {A : Term n} {s : LFSort}
      (hS : SignatureFormed S) (hA : Equality S S A A (.univ s.val)) :
      SignatureFormed (S.snoc A)

/-- A signature followed by local variables, which may only range over Type. -/
inductive ContextFormed : {k : ℕ} → Context k → {n : ℕ} → Context n → Prop
  | signature {k : ℕ} {S : Context k} (hS : SignatureFormed S) : ContextFormed S S
  | snoc {k n : ℕ} {S : Context k} {Γ : Context n} {A : Term n}
      (hΓ : ContextFormed S Γ) (hA : Equality S Γ A A (.univ 0)) :
      ContextFormed S (Γ.snoc A)

/-- LF equality carrying its source formation and typing premises. -/
inductive Equality : {k : ℕ} → Context k → {n : ℕ} → Context n → Term n → Term n → Term n → Prop
  | type {k n : ℕ} {S : Context k} {Γ : Context n} (hΓ : ContextFormed S Γ) :
      Equality S Γ (.univ 0) (.univ 0) (.univ 1)
  | var {k n : ℕ} {S : Context k} {Γ : Context n} {i : Fin n} {A : Term n}
      (hΓ : ContextFormed S Γ) (hi : Lookup Γ i A) : Equality S Γ (.var i) (.var i) A
  | pi {k n : ℕ} {S : Context k} {s : LFSort} {Γ : Context n} {A A' : Term n} {B B' : Term (n + 1)}
      (hA : Equality S Γ A A' (.univ 0))
      (hB : Equality S (Γ.snoc A) B B' (.univ s.val)) :
      Equality S Γ (.pi A B) (.pi A' B') (.univ s.val)
  | lam {k n : ℕ} {S : Context k} {s : LFSort} {Γ : Context n} {A : Term n} {B b b' : Term (n + 1)}
      (hA : Equality S Γ A A (.univ 0))
      (hB : Equality S (Γ.snoc A) B B (.univ s.val))
      (hb : Equality S (Γ.snoc A) b b' B) :
      Equality S Γ (.lam A b) (.lam A b') (.pi A B)
  | app {k n : ℕ} {S : Context k} {s : LFSort} {Γ : Context n} {A f f' a a' : Term n} {B : Term (n + 1)}
      (hA : Equality S Γ A A (.univ 0))
      (hB : Equality S (Γ.snoc A) B B (.univ s.val))
      (hf : Equality S Γ f f' (.pi A B)) (ha : Equality S Γ a a' A) :
      Equality S Γ (.app f a) (.app f' a') (B.instantiate a)
  | beta {k n : ℕ} {S : Context k} {s : LFSort} {Γ : Context n} {A a : Term n} {B b : Term (n + 1)}
      (hA : Equality S Γ A A (.univ 0))
      (hB : Equality S (Γ.snoc A) B B (.univ s.val))
      (hb : Equality S (Γ.snoc A) b b B) (ha : Equality S Γ a a A) :
      Equality S Γ (.app (.lam A b) a) (b.instantiate a) (B.instantiate a)
  | eta {k n : ℕ} {S : Context k} {s : LFSort} {Γ : Context n} {A f : Term n} {B : Term (n + 1)}
      (hA : Equality S Γ A A (.univ 0))
      (hB : Equality S (Γ.snoc A) B B (.univ s.val))
      (hf : Equality S Γ f f (.pi A B)) :
      Equality S Γ (.lam A (.app f.weaken (.var 0))) f (.pi A B)
  | conv {k n : ℕ} {S : Context k} {s : LFSort} {Γ : Context n} {t u A B : Term n}
      (ht : Equality S Γ t u A) (hAB : Equality S Γ A B (.univ s.val)) : Equality S Γ t u B
  | symm {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
      (h : Equality S Γ t u A) : Equality S Γ u t A
  | trans {k n : ℕ} {S : Context k} {Γ : Context n} {t u v A : Term n}
      (h : Equality S Γ t u A) (h' : Equality S Γ u v A) : Equality S Γ t v A

end

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
