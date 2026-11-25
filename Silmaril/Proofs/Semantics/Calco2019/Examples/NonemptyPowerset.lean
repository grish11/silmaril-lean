module

public import Silmaril.Semantics.Calco2019.Examples.SetModels.Nonempty.Defs
public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Thms

public section

universe u

namespace Silmaril.Calco2019.Examples.SetModels.NonemptyPowerset.Proofs

open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem lawful : LawfulMonad (NonemptyPowerset.{u}) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := fun p => Subtype.ext (bind_pure p.1))
  (pure_bind := fun x f => Subtype.ext (pure_bind x (fun x => (f x).1)))
  (bind_assoc := fun p f g => Subtype.ext (bind_assoc p.1 (fun x => (f x).1) (fun y => (g y).1)))

@[expose] noncomputable def guard : TypeKleisli.Guard (NonemptyPowerset.{u}) where
  holds := Guarded
  trivial f x := by
    obtain ⟨y, hy⟩ := (f x).2
    exact ⟨y, Nondet.mem_bind_iff.mpr ⟨y, hy, Nondet.mem_pure _⟩⟩
  parallel hf hg := by
    intro s
    cases s with
    | inl x => exact hf x
    | inr y => exact hg y
  compose _ hf hg x := by
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨v, hv⟩ := hg y
    exact ⟨v, Nondet.mem_bind_iff.mpr ⟨.inl y, hy, hv⟩⟩

variable {X Y Z : Type u}

private theorem val_mapReturn (f : X → NonemptyPowerset (Y ⊕ X)) (g : Y → NonemptyPowerset Z) :
    (fun x => (mapReturn f g x).1) = mapReturn (fun x => (f x).1) (fun y => (g y).1) := by
  funext x
  unfold mapReturn
  simp only [val_bind]
  congr 1
  funext s
  cases s <;> rfl

noncomputable def laws : TypeKleisli.Iteration (NonemptyPowerset.{u}) guard where
  run f hf := nonemptyIter f hf
  fixpoint f hf := by
    funext x
    apply Subtype.ext
    have h := congrFun (Nondet.fixpoint (fun x => (f x).1)).symm x
    change (f x >>= Sum.elim pure (nonemptyIter f hf)).1 = _
    rw [val_bind, nonemptyIter_val]
    refine (congrArg (fun k => (f x).1 >>= k) ?_).trans h
    funext s
    cases s with
    | inl y => rfl
    | inr z => exact nonemptyIter_val f hf z
  naturality f g hf hg := by
    funext x
    apply Subtype.ext
    change (nonemptyIter (mapReturn f g) hg x).1 = (nonemptyIter f hf x >>= g).1
    rw [nonemptyIter_val, val_bind, nonemptyIter_val, val_mapReturn]
    exact congrFun (Nondet.naturality (fun x => (f x).1) (fun y => (g y).1)).symm x
  codiagonal f _ hi ho hm := by
    funext x
    apply Subtype.ext
    have hf : (fun a => (flattenBody f a).1) = flattenBody (fun a => (f a).1) := rfl
    change (nonemptyIter (flattenBody f) hm x).1 = (nonemptyIter (nonemptyIter f hi) ho x).1
    simp only [nonemptyIter_val, hf]
    exact congrFun (Nondet.codiagonal (fun x => (f x).1)).symm x
  uniformity f g h hf hg comm := by
    funext z
    apply Subtype.ext
    have law := Nondet.uniformity (fun z => (g z).1) (fun x => (f x).1) h (by
      funext z
      have hz := congrArg Subtype.val (congrFun comm z)
      change ((g z).1 >>= liftPure (Sum.map id h)) = pure (h z) >>= fun x => (f x).1
      rw [pure_bind]
      exact hz.symm)
    have hz := congrFun law.symm z
    change pure (h z) >>= iter (fun x => (f x).1) = iter (fun z => (g z).1) z at hz
    rw [pure_bind] at hz
    change (nonemptyIter f hf (h z)).1 = (nonemptyIter g hg z).1
    simpa only [nonemptyIter_val] using hz

theorem laws_run (f : X → NonemptyPowerset (Y ⊕ X)) (hf : guard.holds f) :
    laws.run f hf = nonemptyIter f hf := by
  unfold laws
  rfl

end Silmaril.Calco2019.Examples.SetModels.NonemptyPowerset.Proofs
