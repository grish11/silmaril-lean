module

public import Silmaril.Logic.Separation.FirstOrder.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples

variable {A : FOL.Signature} {M N P : FOL.Structure A}

def mapValue (g : FOL.Structure.Hom M N) : Value M → Value N :=
  fun ⟨s,x⟩ => ⟨s,g.map s x⟩

def mapStore (g : FOL.Structure.Hom M N) (h : ModelStore M) : ModelStore N :=
  fun n => (h n).map (mapValue g)

/-- Values may collapse, but ownership domains never do. -/
theorem mapStore_domain (g : FOL.Structure.Hom M N) (h : ModelStore M) (n : Nat) :
    mapStore g h n = none ↔ h n = none := by simp [mapStore]

theorem mapStore_empty (g : FOL.Structure.Hom M N) : mapStore g empty = empty := rfl

theorem mapStore_join (g : FOL.Structure.Hom M N) {a b c : ModelStore M}
    (h : Join a b c) : Join (mapStore g a) (mapStore g b) (mapStore g c) := by
  intro n
  rcases h n with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · exact Or.inl ⟨by simp [mapStore, ha], congrArg (Option.map (mapValue g)) hb⟩
  · exact Or.inr ⟨by simp [mapStore, hb], congrArg (Option.map (mapValue g)) ha⟩

theorem mapStore_singleton (g : FOL.Structure.Hom M N) (n : Nat) (x : Value M) :
    mapStore g (singleton n x) = singleton n (mapValue g x) := by
  funext m
  simp [mapStore, singleton]

theorem mapStore_encodes (g : FOL.Structure.Hom M N) {k} {Γ : Fin k → A.S}
    {ρ : ∀ i, M.carrier (Γ i)} {h : ModelStore M} (hh : Encodes M Γ ρ h) :
    Encodes N Γ (fun i => g.map (Γ i) (ρ i)) (mapStore g h) := by
  intro i
  simp [mapStore, hh i, mapValue]

theorem eval_hom (g : FOL.Structure.Hom M N) {k} {Γ : Fin k → A.S}
    {s} (t : EQ.Term A.toSignature Γ s) (ρ : ∀ i, M.carrier (Γ i)) :
    g.map s (t.eval M.toAlgebra ρ) =
      t.eval N.toAlgebra (fun i => g.map (Γ i) (ρ i)) := by
  induction t with
  | var i => rfl
  | app o args ih =>
      simp only [EQ.Term.eval]
      rw [g.map_op]
      exact congrArg (N.op o) (funext ih)

/-- Every actual FOL hom realizes a native resource-and-atom hom, without injectivity. -/
def nativeHom (g : FOL.Structure.Hom M N) : Separation.Model.Hom (native M) (native N) where
  map := mapStore g
  unit := mapStore_empty g
  join := mapStore_join g
  atom a := by
    cases a with
    | cell n s =>
        rintro h ⟨x,rfl⟩
        exact ⟨g.map s x, mapStore_singleton g n ⟨s,x⟩⟩
    | eq Γ t u =>
        rintro h ⟨ρ,hh,he⟩
        exact ⟨_, mapStore_encodes g hh,
          (eval_hom g t ρ).symm.trans ((congrArg (g.map _) he).trans (eval_hom g u ρ))⟩
    | rel Γ r args =>
        rintro h ⟨ρ,hh,hr⟩
        refine ⟨_, mapStore_encodes g hh, ?_⟩
        have h := g.map_rel r _ hr
        simpa only [eval_hom] using h

theorem mapStore_id (h : ModelStore M) : mapStore (𝟙 M) h = h := by
  funext n
  simp only [mapStore]
  cases h n with
  | none => rfl
  | some v => cases v; rfl

theorem mapStore_comp (f : M ⟶ N) (g : N ⟶ P) (h : ModelStore M) :
    mapStore (f ≫ g) h = mapStore g (mapStore f h) := by
  funext n
  simp only [mapStore]
  cases h n with
  | none => rfl
  | some v => cases v; rfl

def realization (A : FOL.Signature) : FOL.Structure A ⥤ Separation.Model (signature A) where
  obj := native
  map := nativeHom
  map_id _ := Separation.Model.Hom.ext _ _ (funext mapStore_id)
  map_comp f g := Separation.Model.Hom.ext _ _ (funext (mapStore_comp f g))

end Silmaril.Logic.Separation.FirstOrder
