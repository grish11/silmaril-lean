module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Defs
public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (Interface Arrow)

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop}
  {X Y Z W : Interface α σ atomType}

theorem arrow_ext {f g : Arrow X Y} (h : ∀ i a s, f.run i a s = g.run i a s) : f = g := by
  cases f
  cases g
  congr
  exact funext fun i => funext fun a => funext fun s => h i a s

theorem id_typed (i : Fin X.labels.length) (a : X.Payload i) (s : σ) :
    ReturnsTyped atomType (L := X.labels) (pureReturn i a.val s) := by
  intro j b t reached
  obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj (ordinary_return_iff.mp reached)
  exact a.property

theorem comp_typed (f : Arrow X Y) (g : Arrow Y Z) (i : Fin X.labels.length) (a : X.Payload i) (s : σ) :
    ReturnsTyped atomType (L := Z.labels) ((f.run i a s).bind g.total) := by
  intro j b t reached
  obtain ⟨k, c, u, exit, last⟩ := ((ordinary_bind reached.1 _).mp reached).resolve_left id
  have typed := f.returnsTyped i a s exit
  rw [g.total_typed k ⟨c, typed⟩ u] at last
  exact g.returnsTyped k ⟨c, typed⟩ u last

@[expose] noncomputable def identity (X : Interface α σ atomType) : Arrow X X :=
  ⟨fun i a s => pureReturn i a.val s, id_typed⟩

@[expose] noncomputable def compose (f : Arrow X Y) (g : Arrow Y Z) : Arrow X Z :=
  ⟨fun i a s => (f.run i a s).bind g.total, comp_typed f g⟩

theorem identity_compose (f : Arrow X Y) : compose (identity X) f = f := by
  apply arrow_ext
  intro i a s
  exact (return_bind i a.val s f.total).trans (f.total_typed i a s)

theorem compose_identity (f : Arrow X Y) : compose f (identity Y) = f := by
  apply arrow_ext
  intro i a s
  refine (bind_congr fun j b t reached => ?_).trans (bind_return (f.run i a s))
  exact (identity Y).total_typed j ⟨b, f.returnsTyped i a s reached⟩ t

theorem compose_assoc (f : Arrow X Y) (g : Arrow Y Z) (h : Arrow Z W) :
    compose (compose f g) h = compose f (compose g h) := by
  classical
  apply arrow_ext
  intro i a s
  change ((f.run i a s).bind g.total).bind h.total = (f.run i a s).bind (compose g h).total
  rw [bind_assoc]
  apply bind_congr
  intro j b t reached
  have typed := f.returnsTyped i a s reached
  rw [g.total_typed j ⟨b, typed⟩ t, (compose g h).total_typed j ⟨b, typed⟩ t]
  rfl

theorem repackage_typed {B C : Ty κ} {p : Behaviour 1 α σ} (shaped : ReturnsTyped atomType (L := [B]) p)
    (pack : Value α → Value α) (typed : ∀ b, ValueTyped atomType b B → ValueTyped atomType (pack b) C) :
    ReturnsTyped atomType (L := [C]) (p.bind fun _ b s => pureReturn 0 (pack b) s) := by
  intro j v t reached
  obtain ⟨i, b, s, head, tail⟩ :=
    ((ordinary_bind reached.1 _).mp reached).resolve_left id
  obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj
    (ordinary_return_iff.mp tail)
  have hi := Fin.eq_zero i
  subst i
  exact typed b (shaped head)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category
