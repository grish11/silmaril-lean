module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Operations.Thms

@[expose] public section

/-! # Set-valued W operations for the graph model of extensional MLTT

`node` and `wrec` are total operations on sets. On typed inputs they use the
actual W constructor and recursor on the carrier; off their domains they have
empty-set defaults. `stepType` is the interpretation of the object dependent
induction telescope, with graph-valued child functions and induction hypotheses.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

universe u

noncomputable section
open Classical

/-- The graph of a function whose argument is already restricted to a set. -/
def graph {D : ZFSet.{u}} (f : D → ZFSet.{u}) : ZFSet.{u} :=
  SetSem.lam D fun x => if hx : x ∈ D then f ⟨x, hx⟩ else ∅

/-- The graph of the children of a typed W-node. -/
def childGraph {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} {a : A}
    (f : B a.val → carrier A B) : ZFSet.{u} := graph fun b => (f b).val

/-- Read a graph-valued child function as a section into the W carrier. -/
def childSection {A a f : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hf : f ∈ SetSem.pi (B a) (fun _ => carrier A B)) : B a → carrier A B :=
  fun b => ⟨SetSem.app f b.val, SetSem.app_mem_of_mem_pi hf b.property⟩

/-- The W node constructor on raw set values, with an empty value off typed inputs. -/
def node (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) (a f : ZFSet.{u}) : ZFSet.{u} :=
  if ha : a ∈ A then
    if hf : f ∈ SetSem.pi (B a) (fun _ => carrier A B) then
      (sup ⟨a, ha⟩ (childSection hf)).val
    else ∅
  else ∅

/-- Apply a graph-valued step to a label, its children and the recursive results. -/
def graphStep {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (s : ZFSet.{u})
    (a : A) (f : B a.val → carrier A B) (ih : B a.val → ZFSet.{u}) : ZFSet.{u} :=
  SetSem.app (SetSem.app (SetSem.app s a.val) (childGraph f)) (graph ih)

/-- Dependent W recursion on set values, with empty value off the W carrier. -/
def wrec (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) (s t : ZFSet.{u}) : ZFSet.{u} :=
  if ht : t ∈ carrier A B then
    elim (fun _ => ZFSet.{u}) (graphStep s) ⟨t, ht⟩
  else ∅

/-- The graph interpretation of the dependent W-elimination step type. -/
def stepType (A : ZFSet.{u}) (B C : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  SetSem.pi A fun a =>
    SetSem.pi (SetSem.pi (B a) (fun _ => carrier A B)) fun f =>
      SetSem.pi (SetSem.pi (B a) (fun b => C (SetSem.app f b))) fun _ =>
        C (node A B a f)

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet
