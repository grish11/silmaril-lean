module

public import Silmaril.Logic.Institution.Structured.Constraints.Institution
public import Silmaril.Logic.Institution.Faithful

set_option backward.isDefEq.respectTransparency false

/-! Freeness and constraint satisfaction under actual model isomorphisms.
The base-room premise in sat_iso is necessary for arbitrary institutions and
is discharged by the equational application; no modelhood premise is omitted. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Institution.Structured.Constraints
open CategoryTheory Silmaril.Logic.Institution
universe u v w x s p q

private theorem freeAt_of_iso {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{x} D] (R : C ⥤ D) {M N : C}
    (e : M ≅ N) (h : FreeAt R M) : FreeAt R N := by
  intro X
  constructor
  · intro f g he
    have hh : e.hom ≫ f = e.hom ≫ g := by
      apply (h X).1
      simpa only [Functor.map_comp] using
        (congrArg (fun k => R.map e.hom ≫ k) he)
    have hb := congrArg (fun k => e.inv ≫ k) hh
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using hb
  · intro g
    obtain ⟨f, hf⟩ := (h X).2 (R.map e.hom ≫ g)
    change R.map f = R.map e.hom ≫ g at hf
    refine ⟨e.inv ≫ f, ?_⟩
    calc
      R.map (e.inv ≫ f) = R.map e.inv ≫ (R.map e.hom ≫ g) := by
        rw [R.map_comp, hf]
      _ = R.map (e.inv ≫ e.hom) ≫ g := by
        rw [R.map_comp, Category.assoc]
      _ = g := by rw [e.inv_hom_id, R.map_id, Category.id_comp]

/-- The full bijection of actual hom-sets is invariant under source-object iso. -/
theorem freeAt_iso {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{x} D] (R : C ⥤ D) {M N : C}
    (e : M ≅ N) : FreeAt R M ↔ FreeAt R N :=
  ⟨freeAt_of_iso R e, freeAt_of_iso R e.symm⟩

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{s,p,q})

private theorem sat_of_iso {S : Sign} {M N : (I.obj S).Mod}
    (e : M ≅ N) (c : Constraint I S)
    (hIso : (I.obj c.target.sig).IsoInvariant)
    (h : Sat I M c) : Sat I N c := by
  obtain ⟨hM, hfree⟩ := h
  let er := ((I.map c.context).mod).mapIso e
  have hN : Theory.modelsProperty c.target.axioms ((I.map c.context).mod.obj N) := by
    intro φ hφ
    exact (hIso _ _ ⟨er⟩ φ).mp (hM φ hφ)
  refine ⟨hN, ?_⟩
  let em : (⟨(I.map c.context).mod.obj M, hM⟩ : SemanticModels.Models I c.target) ≅
      ⟨(I.map c.context).mod.obj N, hN⟩ :=
    ObjectProperty.isoMk (Theory.modelsProperty c.target.axioms) er
  exact (freeAt_iso (SemanticModels.reduct I c.theoryMap) em).mp hfree

/-- Transport includes both target-modelhood and the entire free-extension
universal property, along the actual context reduct of the model iso. -/
theorem sat_iso {S : Sign} {M N : (I.obj S).Mod}
    (e : M ≅ N) (c : Constraint I S)
    (hIso : (I.obj c.target.sig).IsoInvariant) :
    Sat I M c ↔ Sat I N c :=
  ⟨sat_of_iso I e c hIso, sat_of_iso I e.symm c hIso⟩

end Silmaril.Logic.Institution.Structured.Constraints
