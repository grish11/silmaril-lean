module

public import Silmaril.Wasm.Logic.Separation.Wasm.Defs
public import Silmaril.Logic.Separation.Matching.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Wasm
open Silmaril.Wasm.Logic.Sep
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

private theorem finite_unfold : finiteSet = {Heap.empty} ∪ resource.sep {h | singleCell h} finiteSet :=
  Pattern.mu_unfold model _ _

theorem finite_empty : finiteAssn Heap.empty := by
  change _ ∈ finiteSet
  rw [finite_unfold]
  exact Or.inl rfl

theorem finite_cell (l : Loc) (c : Cell) {tail : Heap} (hd : Heap.Disj (Heap.single l c) tail)
    (ht : finiteAssn tail) : finiteAssn ((Heap.single l c).union tail) := by
  change _ ∈ finiteSet
  rw [finite_unfold]
  exact Or.inr ⟨Heap.single l c,tail,⟨hd,rfl⟩,⟨l,c,rfl⟩,ht⟩

theorem finite_iff_inductive (h : Heap) : finiteAssn h ↔ FiniteHeap h := by
  have forward : finiteSet ⊆ {h | FiniteHeap h} := by
    apply Pattern.mu_induction model _ _ {h | FiniteHeap h}
    rintro h (he | ⟨a,b,⟨hd,he⟩,⟨l,c,ha⟩,hb⟩)
    · exact he ▸ FiniteHeap.empty
    · exact he ▸ (ha ▸ FiniteHeap.cell l c b (ha ▸ hd) hb)
  constructor
  · exact fun hh => forward hh
  · intro hh
    induction hh with
    | empty => exact finite_empty
    | cell l c tail hd _ ih => exact finite_cell l c hd ih

theorem sep_is_native (P Q : Assn) : (fun h => h ∈ resource.sep {h | P h} {h | Q h}) = (P ∗ Q) := by
  funext h
  apply propext
  constructor
  · rintro ⟨a,b,⟨hd,he⟩,hp,hq⟩; exact ⟨a,b,hd,he,hp,hq⟩
  · rintro ⟨a,b,hd,he,hp,hq⟩; exact ⟨a,b,⟨hd,he⟩,hp,hq⟩

/-- A real pinned GC field load preserves a nontrivial recursive tail predicate
using the already proved native every-run separation triple and frame rule. -/
theorem structGet_preserves_recursive_tail {H : Type} (P : Profile) (host : HostSemantics H)
    {us : List Val} {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx}
    {a : Nat} {fv : FieldVal} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType}
    (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu : unpackable (fieldStorage ft) sx fv) :
    STriple P host
      (fun f => (fun h => f.type? x = some d ∧ pointsTo (.field a i.toNat) (.fv fv) h) ∗ finiteAssn)
      (vals (us ++ [.ref (.struct a)]) ++ [.plain (.structGet sx x i)])
      (fun _ o => (fun h => o = .normal (us ++ [unpackField sx fv]) ∧
        pointsTo (.field a i.toNat) (.fv fv) h) ∗ finiteAssn) :=
  STriple.frame finiteAssn (STriple.structGet he hi hu)

/-- The exact recursive tail itself reaches the existing native matching μ syntax. -/
theorem finite_matching :
    (compilePattern finiteHeap).denote (matchingModel model) (fun i => i.elim0) (fun i => i.elim0) =
      finiteSet :=
  congrArg (fun F => F (fun i => i.elim0)) (compilePattern_denote model finiteHeap)

theorem recursive_frame_matching (head : Assn) :
    (compilePattern (.sep (.base (.atom head)) finiteHeap)).denote (matchingModel model)
        (fun i => i.elim0) (fun i => i.elim0) = {h | (head ∗ finiteAssn) h} := by
  rw [compilePattern_denote]
  ext h
  exact Iff.of_eq (congrFun (sep_is_native head finiteAssn) h)

end Silmaril.Logic.Separation.Wasm
