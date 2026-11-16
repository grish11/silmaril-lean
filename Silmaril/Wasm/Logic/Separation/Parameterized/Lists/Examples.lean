module

public import Silmaril.Logic.Separation.Parameterized.Lists.Thms
public import Silmaril.Wasm.Logic.Separation.Wasm.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized.Lists.Examples
open Silmaril.Wasm.Logic.Sep
open Silmaril.Wasm.Execution.Core

def pointerValue : Option Nat → Val
  | none => .ref .null
  | some a => .ref (.struct a)

def headHeap (a : Nat) (next : Option Nat) : Heap :=
  Heap.single (.field a 0) (.fv (.val (pointerValue next)))

/-- Exact native Wasm partial heaps, not a finite resource approximation.
`none` is null and `some a` points at structure address a. -/
abbrev model : Model signature where
  Value := Option Nat
  resource := Separation.Wasm.resource
  operation op _ := match op with | .nil => none
  atom a args := match a with
    | .link => match args 0 with
      | none => ∅
      | some x => {h | h = headHeap x (args 1)}

theorem one_node (a : Nat) : Linked model (some a) (headHeap a none) := by
  apply Linked.cons (y := none) (a := headHeap a none) (b := Heap.empty)
  · intro h; cases h
  · rfl
  · exact ⟨Heap.disj_empty _, (Heap.union_empty _).symm⟩
  · exact Linked.nil

private theorem disjoint_heads : Heap.Disj (headHeap 0 (some 1)) (headHeap 1 none) := by
  intro l
  by_cases h : l = .field 0 0
  · right
    simp only [headHeap, Heap.single, h]
    decide
  · left
    simp only [headHeap, Heap.single, ite_eq_right h]

def twoNodes : Heap := (headHeap 0 (some 1)).union (headHeap 1 none)

theorem two_nodes : Linked model (some 0) twoNodes := by
  apply Linked.cons (y := some 1) (a := headHeap 0 (some 1)) (b := headHeap 1 none)
  · intro h; cases h
  · rfl
  · exact ⟨disjoint_heads,rfl⟩
  · exact one_node 1

/-- The checked source predicate actually follows 0 → 1 → null through owned
native fields, and separates the two distinct field heaps. -/
theorem source_two_nodes :
    ((fun _ : Fin 1 => some 0), twoNodes) ∈ list.denote model (fun i => i.elim0) :=
  (list_iff_linked model _ _).mpr two_nodes

theorem source_null_empty :
    ((fun _ : Fin 1 => none), Heap.empty) ∈ list.denote model (fun i => i.elim0) :=
  (list_iff_linked model _ _).mpr Linked.nil

private theorem linked_head {x h} (linked : Linked model x h) :
    ∀ a, x = some a → ∃ v, h (.field a 0) = some v := by
  induction linked with
  | nil => intro a he; cases he
  | @cons x y head tail heap hn hc hj ht ih =>
      intro a he
      rw [he] at hc
      change head = headHeap a y at hc
      refine ⟨.fv (.val (pointerValue y)), ?_⟩
      rw [hj.2,hc]
      simp [Heap.union,headHeap,Heap.single]

/-- Changing the pointer changes truth, even on the same empty heap. -/
theorem source_nonnull_empty_false :
    ((fun _ : Fin 1 => some 0), Heap.empty) ∉ list.denote model (fun i => i.elim0) := by
  intro hs
  have linked := (list_iff_linked model _ _).mp hs
  obtain ⟨v,hv⟩ := linked_head linked 0 rfl
  change none = some v at hv
  cases hv

end Silmaril.Logic.Separation.Parameterized.Lists.Examples
