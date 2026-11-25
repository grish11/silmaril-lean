module

public import Silmaril.Semantics.Calco2019.Examples.SetModels.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.SetModels.Proofs

open CategoryTheory
open scoped Silmaril.Elgot.Nondet

variable {X Y : Type u}

theorem trunc_nonempty_iff (X : Type u) : Nonempty (Trunc X) ↔ Nonempty X := by
  constructor
  · rintro ⟨q⟩
    obtain ⟨x, _⟩ := q.exists_rep
    exact ⟨x⟩
  · rintro ⟨x⟩
    exact ⟨Trunc.mk x⟩

private theorem trunc_hom_subsingleton {X Y : Kleisli (ofTypeMonad Trunc)} :
    Subsingleton (X ⟶ Y) := by
  constructor
  intro f g
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext x
  exact Trunc.eq _ _

theorem trunc_guarded_each :
    truncGuard.guarded (computation Trunc truncChoice) ∧
      truncGuard.left (computation Trunc truncChoice) := by
  exact ⟨⟨𝟙 _, trunc_hom_subsingleton.elim _ _⟩, ⟨𝟙 _, trunc_hom_subsingleton.elim _ _⟩⟩

theorem trunc_union_unguarded :
    ¬ truncGuard.guarded (computation Trunc
      (fun x : Unit => Trunc.map Sum.inr (truncChoice x) : Unit → Trunc (Empty ⊕ (Unit ⊕ Unit)))) := by
  rintro ⟨g, _⟩
  have q : Trunc Empty := g.of ()
  obtain ⟨x, _⟩ := q.exists_rep
  exact Empty.elim x

theorem powerset_least (f : X → SetM (Y ⊕ X)) (g : X → SetM Y)
    (hg : ∀ x, (f x >>= Sum.elim pure g).run ⊆ (g x).run) (x : X) :
    (Elgot.iter f x).run ⊆ (g x).run := by
  intro y hy
  have h := Elgot.Nondet.mem_iter_iff f x y |>.mp hy
  induction h with
  | @done x y edge =>
    apply hg x
    exact Elgot.Nondet.mem_bind_iff.mpr ⟨.inl y, edge, Elgot.Nondet.mem_pure y⟩
  | @more x x' _ edge tail ih =>
    apply hg x
    exact Elgot.Nondet.mem_bind_iff.mpr ⟨.inr x', edge, ih ((Elgot.Nondet.mem_iter_iff f x' _).mpr tail)⟩

theorem powerset_iter_nonempty {X Y : Type u} (f : X → SetM (Y ⊕ X))
    (hf : HasDirectReturn f) (x : X) : (Elgot.iter f x).run.Nonempty := by
  obtain ⟨y, hy⟩ := hf x
  exact ⟨y, (Elgot.Nondet.mem_iter_iff f x y).mpr (.done hy)⟩

end Silmaril.Calco2019.Examples.SetModels.Proofs
