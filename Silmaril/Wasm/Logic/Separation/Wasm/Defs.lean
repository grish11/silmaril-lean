module

public import Silmaril.Logic.Separation.Laws
public import Silmaril.Wasm.Logic.Sep.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Wasm
open Silmaril.Wasm.Logic.Sep

private theorem union_comm {a b : Heap} (h : Heap.Disj a b) : a.union b = b.union a := by
  funext l
  rcases h l with ha | hb
  · cases hb : b l <;> simp [Heap.union, ha, hb]
  · cases ha : a l <;> simp [Heap.union, ha, hb]

/-- Exactly the existing native heap, disjointness, union and empty heap. -/
abbrev resource : Resource where
  carrier := Heap
  unit := Heap.empty
  join a b c := Heap.Disj a b ∧ c = a.union b
  functional h k := h.2.trans k.2.symm
  unit_join a b := by
    constructor
    · intro h; exact h.2.symm
    · intro h; exact ⟨(fun _ => Or.inl rfl), h.symm⟩
  comm a b c := by
    constructor
    · intro h; exact ⟨h.1.symm, h.2.trans (union_comm h.1)⟩
    · intro h; exact ⟨h.1.symm, h.2.trans (union_comm h.1)⟩
  assoc a b c d := by
    constructor
    · rintro ⟨ab,hab,hd⟩
      have hbc : Heap.Disj b c := (Heap.disj_union_left.mp (hab.2 ▸ hd.1)).2
      have hac : Heap.Disj a c := (Heap.disj_union_left.mp (hab.2 ▸ hd.1)).1
      exact ⟨b.union c, ⟨hbc,rfl⟩,
        ⟨Heap.disj_union_right.mpr ⟨hab.1,hac⟩,
          hd.2.trans ((congrArg (fun h => h.union c) hab.2).trans (Heap.union_assoc a b c))⟩⟩
    · rintro ⟨bc,hbc,hd⟩
      have hab : Heap.Disj a b := (Heap.disj_union_right.mp (hbc.2 ▸ hd.1)).1
      have hac : Heap.Disj a c := (Heap.disj_union_right.mp (hbc.2 ▸ hd.1)).2
      exact ⟨a.union b, ⟨hab,rfl⟩,
        ⟨Heap.disj_union_left.mpr ⟨hac,hbc.1⟩,
          hd.2.trans ((congrArg (Heap.union a) hbc.2).trans (Heap.union_assoc a b c).symm)⟩⟩

abbrev signature : Signature := ⟨Assn⟩
abbrev model : Model signature where
  resource := Silmaril.Logic.Separation.Wasm.resource
  atom := fun (p : Assn) => {h | p h}

def singleCell : Assn := fun h => ∃ l c, h = Heap.single l c

/-- μX. emp ∨ (one native cell ∗ X), with an actual heap-set least fixed point. -/
def finiteHeap : Pattern signature 0 :=
  .mu (.disj (.base .emp) (.sep (.base (.atom singleCell)) (.var 0)))

abbrev finiteSet : Set Heap := finiteHeap.denote model (fun i => i.elim0)
abbrev finiteAssn : Assn := fun h => h ∈ finiteSet

inductive FiniteHeap : Heap → Prop where
  | empty : FiniteHeap Heap.empty
  | cell (l : Loc) (c : Cell) (tail : Heap) (disjoint : Heap.Disj (Heap.single l c) tail)
      (finite : FiniteHeap tail) : FiniteHeap ((Heap.single l c).union tail)

end Silmaril.Logic.Separation.Wasm
