module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Thms

@[expose] public section

/-! # Finite direct-recursive constructor signatures and their actual carriers

Each constructor has a dependent nonrecursive label telescope followed by a
fixed finite number of direct recursive children. Cumulative finite-height
tagged layers construct its carrier as an actual ZFSet. Function-valued
recursive fields and general indexed/mutual positivity require further work;
infinitely branching well-founded trees need not have finite height.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

def ValueTelescope.append : (T : ValueTelescope.{u}) → (T.Points → ValueTelescope.{u}) → ValueTelescope.{u}
  | .nil, U => U PUnit.unit
  | .bind A rest, U => .bind A (fun x => (rest x).append (fun xs => U ⟨x, xs⟩))

def ValueTelescope.appendPoint : (T : ValueTelescope.{u}) → (U : T.Points → ValueTelescope.{u}) →
    (xs : T.Points) → (U xs).Points → (T.append U).Points
  | .nil, _, _, ys => ys
  | .bind _ rest, U, ⟨x, xs⟩, ys => ⟨x, (rest x).appendPoint (fun xs => U ⟨x, xs⟩) xs ys⟩

def recursiveFields (D : Value.{u}) : ℕ → ValueTelescope.{u}
  | 0 => .nil
  | n + 1 => .bind D (fun _ => recursiveFields D n)

structure FinitarySignature where
  count : ℕ
  labels : Fin count → ValueTelescope.{u}
  arity : Fin count → ℕ

def FinitarySignature.telescopes (S : FinitarySignature.{u}) (D : Value.{u}) (index : Fin S.count) : ValueTelescope.{u} :=
  (S.labels index).append (fun _ => recursiveFields D (S.arity index))

noncomputable def FinitarySignature.layer (S : FinitarySignature.{u}) (parameters : LocalValues.{u}) (D : Value.{u}) : Value.{u} :=
  constructorLayer S.count (S.telescopes D) parameters

noncomputable def FinitarySignature.stage (S : FinitarySignature.{u}) (parameters : LocalValues.{u}) : ℕ → Value.{u}
  | 0 => ∅
  | n + 1 => S.stage parameters n ∪ S.layer parameters (S.stage parameters n)

noncomputable def FinitarySignature.carrier (S : FinitarySignature.{u}) (parameters : LocalValues.{u}) : Value.{u} :=
  ZFSet.iUnion (S.stage parameters)

/-- A genuine recursive schema with a nullary leaf and a binary node. -/
def binaryTreeSignature : FinitarySignature.{u} where
  count := 2
  labels _ := .nil
  arity index := if index.val = 0 then 0 else 2

def binaryTreeLeaf : Value.{u} := constructorValue 0 []

def binaryTreeNode (left right : Value.{u}) : Value.{u} := constructorValue 1 [left, right]

/-- A chain of binary nodes witnesses strict growth at every finite height. -/
def binaryTreeChain : ℕ → Value.{u}
  | 0 => binaryTreeLeaf
  | n + 1 => binaryTreeNode (binaryTreeChain n) binaryTreeLeaf

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
