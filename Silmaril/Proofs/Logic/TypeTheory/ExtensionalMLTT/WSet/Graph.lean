module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Graph.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

universe u

noncomputable section
open Classical

@[simp]
theorem graph_app {D : ZFSet.{u}} (f : D → ZFSet.{u}) (x : D) :
    SetSem.app (graph f) x.val = f x := by
  simp only [graph, SetSem.app_lam _ x.property, dite_eq_left x.property]

/-- A pointwise typed section gives a member of the graph-valued product. -/
theorem graph_mem_pi {D : ZFSet.{u}} {E : ZFSet.{u} → ZFSet.{u}}
    {f : D → ZFSet.{u}} (hf : ∀ x, f x ∈ E x.val) : graph f ∈ SetSem.pi D E := by
  apply SetSem.lam_mem_pi
  intro x hx
  simpa only [dite_eq_left hx] using hf ⟨x, hx⟩

/-- Every typed child section is a graph from the branch fibre into the carrier. -/
theorem childGraph_mem {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} {a : A}
    (f : B a.val → carrier A B) :
    childGraph f ∈ SetSem.pi (B a.val) (fun _ => carrier A B) :=
  graph_mem_pi fun b => (f b).property

@[simp]
theorem childSection_childGraph {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} {a : A}
    (f : B a.val → carrier A B) : childSection (childGraph_mem f) = f := by
  funext b
  apply Subtype.ext
  exact graph_app (fun b => (f b).val) b

/-- Reading then rebuilding a typed graph preserves the graph itself. -/
theorem childGraph_childSection {A a f : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (ha : a ∈ A) (hf : f ∈ SetSem.pi (B a) (fun _ => carrier A B)) :
    childGraph (a := (⟨a, ha⟩ : A)) (childSection hf) = f := by
  calc
    childGraph (a := (⟨a, ha⟩ : A)) (childSection hf) = SetSem.lam (B a) (SetSem.app f) := by
      unfold childGraph graph
      apply SetSem.lam_congr
      intro b hb
      simp only [dite_eq_left hb, childSection]
    _ = f := SetSem.lam_app_of_mem_pi hf

/-- The raw constructor agrees with the actual W constructor on typed sections. -/
@[simp]
theorem node_childGraph {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (a : A) (f : B a.val → carrier A B) :
    node A B a.val (childGraph f) = (sup a f).val := by
  simp only [node, dite_eq_left a.property, dite_eq_left (childGraph_mem f), childSection_childGraph]

/-- Semantic W introduction: the node belongs to the whole W carrier. -/
theorem node_mem {A a f : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (ha : a ∈ A) (hf : f ∈ SetSem.pi (B a) (fun _ => carrier A B)) :
    node A B a f ∈ carrier A B := by
  simp only [node, dite_eq_left ha, dite_eq_left hf]
  exact (sup ⟨a, ha⟩ (childSection hf)).property

@[simp]
theorem wrec_typed {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (s : ZFSet.{u}) (t : carrier A B) :
    wrec A B s t.val = elim (fun _ => ZFSet.{u}) (graphStep s) t := by
  simp only [wrec, dite_eq_left t.property]

/-- Semantic recursion computes on every actual W constructor. -/
theorem wrec_sup {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (s : ZFSet.{u}) (a : A) (f : B a.val → carrier A B) :
    wrec A B s (sup a f).val =
      graphStep s a f (fun b => wrec A B s (f b).val) := by
  simp only [wrec_typed, elim_sup]

/-- Iota for raw set values, with graph-valued recursive calls exactly as in object syntax. -/
theorem wrec_node {A a f : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (s : ZFSet.{u}) (ha : a ∈ A)
    (hf : f ∈ SetSem.pi (B a) (fun _ => carrier A B)) :
    wrec A B s (node A B a f) =
      SetSem.app (SetSem.app (SetSem.app s a) f)
        (SetSem.lam (B a) (fun b => wrec A B s (SetSem.app f b))) := by
  have hchildren : childGraph (a := (⟨a, ha⟩ : A)) (childSection hf) = f :=
    childGraph_childSection ha hf
  have hresults : graph (fun b : B a => wrec A B s ((childSection hf) b).val) =
      SetSem.lam (B a) (fun b => wrec A B s (SetSem.app f b)) := by
    apply SetSem.lam_congr
    intro b hb
    simp only [dite_eq_left hb, childSection]
  simpa only [node, dite_eq_left ha, dite_eq_left hf, graphStep, hchildren, hresults] using
    wrec_sup s (⟨a, ha⟩ : A) (childSection hf)

/-- A step of the specified dependent telescope produces the correct motive fibre. -/
theorem graphStep_mem {A s : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (hs : s ∈ stepType A B C) (a : A) (f : B a.val → carrier A B)
    (ih : B a.val → ZFSet.{u}) (hih : ∀ b, ih b ∈ C (f b).val) :
    graphStep s a f ih ∈ C (sup a f).val := by
  have hlabel : SetSem.app s a.val ∈
      SetSem.pi (SetSem.pi (B a.val) (fun _ => carrier A B)) (fun g =>
        SetSem.pi (SetSem.pi (B a.val) (fun b => C (SetSem.app g b))) (fun _ =>
          C (node A B a.val g))) :=
    SetSem.app_mem_of_mem_pi hs a.property
  have hchildren : SetSem.app (SetSem.app s a.val) (childGraph f) ∈
      SetSem.pi (SetSem.pi (B a.val) (fun b => C (SetSem.app (childGraph f) b)))
        (fun _ => C (node A B a.val (childGraph f))) :=
    SetSem.app_mem_of_mem_pi hlabel (childGraph_mem f)
  have hinduction : graph ih ∈
      SetSem.pi (B a.val) (fun b => C (SetSem.app (childGraph f) b)) := by
    apply graph_mem_pi
    intro b
    simpa only [childGraph, graph_app] using hih b
  simpa only [graphStep, node_childGraph] using
    SetSem.app_mem_of_mem_pi hchildren hinduction

/-- Semantic dependent W elimination preserves membership in the motive. -/
theorem wrec_mem {A s t : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (hs : s ∈ stepType A B C) (ht : t ∈ carrier A B) : wrec A B s t ∈ C t := by
  apply elim (fun z : carrier A B => wrec A B s z.val ∈ C z.val) ?_ ⟨t, ht⟩
  intro a f ih
  rw [wrec_sup]
  exact graphStep_mem hs a f _ ih

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet
