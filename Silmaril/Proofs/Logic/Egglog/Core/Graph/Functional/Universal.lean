module

public import Silmaril.Logic.Egglog.Core.Graph.Functional.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Graph.Functional
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem folHom_ext {Sg : FOL.Signature} {M N : FOL.Structure Sg}
    {f g : M ⟶ N} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem fol_eqToHom_comp_map {Sg : FOL.Signature}
    {M M' N N' : FOL.Structure Sg} (e : M' = M) (f : M ⟶ N) (e' : N = N')
    (s : Sg.S) (x : M'.carrier s) :
    (eqToHom e ≫ f ≫ eqToHom e').map s x =
      cast (congrArg (fun K : FOL.Structure Sg => K.carrier s) e')
        (f.map s (cast (congrArg (fun K : FOL.Structure Sg => K.carrier s) e) x)) := by
  subst e e'
  rfl

private theorem independent_eqToHom_comp_map {S : Signature}
    {M M' N N' : IndependentModel S} (e : M' = M) (f : M ⟶ N) (e' : N = N')
    (s : S.S) (x : M'.obj.carrier s) :
    (eqToHom e ≫ f ≫ eqToHom e').hom.map s x =
      cast (congrArg (fun K : IndependentModel S => K.obj.carrier s) e')
        (f.hom.map s (cast (congrArg (fun K : IndependentModel S => K.obj.carrier s) e) x)) := by
  subst e e'
  rfl

private theorem core_eqToHom_comp_map {S : Signature}
    {M M' N N' : Core.Model S} (e : M' = M) (f : M ⟶ N) (e' : N = N')
    (s : S.S) (x : M'.carrier s) :
    (eqToHom e ≫ f ≫ eqToHom e').map s x =
      cast (congrArg (fun K : Core.Model S => K.carrier s) e')
        (f.map s (cast (congrArg (fun K : Core.Model S => K.carrier s) e) x)) := by
  subst e e'
  rfl

private theorem row_heq {S : Signature} {n : Nat} {w v : Fin (n+1) → S.S}
    (hw : w = v) (f : S.Function n (w ∘ Fin.succ) (w 0))
    (g : S.Function n (v ∘ Fin.succ) (v 0)) (hf : HEq f g) :
    HEq (Relation.row (w := w) f) (Relation.row (w := v) g) := by
  cases hw
  cases hf
  rfl

/-- Reconstruction retains the whole independently supplied FOL structure. -/
theorem graph_reconstruct {S : Signature} (M : IndependentModel S) :
    model (reconstruct M) = M.obj := by
  change FOL.Structure.mk _ _ = _
  rcases M with ⟨⟨A, rel⟩, h⟩
  congr 1
  funext n w r args
  cases r with
  | predicate p => rfl
  | @row n w f =>
    have hw : Fin.cases (w 0) (w ∘ Fin.succ) = w := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [reconstruct]
    congr 1
    · exact row_heq hw _ _ HEq.rfl
    · apply Function.hfunext rfl
      intro i j hij
      cases hij
      exact Fin.cases HEq.rfl (fun _ => HEq.rfl) i

/-- Conversely no original table model information is lost. -/
theorem reconstruct_graph {S : Signature} (M : Core.Model S) :
    reconstruct ((embed S).obj M) = M := by
  cases M
  rfl

/-- Actual homomorphisms can be lifted back along reconstruction. -/
def liftHom {S : Signature} {M N : IndependentModel S}
    (h : reconstruct M ⟶ reconstruct N) : M ⟶ N :=
  ⟨eqToHom (graph_reconstruct M).symm ≫ (graphs S).map h ≫
    eqToHom (graph_reconstruct N)⟩

theorem models_liftHom {S : Signature} {M N : IndependentModel S}
    (h : reconstruct M ⟶ reconstruct N) : (models S).map (liftHom h) = h := by
  apply Core.Model.Hom.ext
  funext s x
  exact fol_eqToHom_comp_map (graph_reconstruct M).symm ((graphs S).map h)
    (graph_reconstruct N) s x

instance models_full (S : Signature) : (models S).Full where
  map_surjective h := ⟨liftHom h, models_liftHom h⟩

instance models_faithful (S : Signature) : (models S).Faithful where
  map_injective := by
    intro M N f g h
    apply ObjectProperty.hom_ext
    apply folHom_ext
    exact congrArg Core.Model.Hom.map h

/-- Every Egglog model is literally a reconstruction, hence lies in the essential image. -/
theorem models_surjective (S : Signature) : Function.Surjective (models S).obj :=
  fun M => ⟨(embed S).obj M,reconstruct_graph M⟩

theorem reconstruct_reduct {S T : Signature} (f : S ⟶ T) (M : IndependentModel T) :
    reconstruct ((reduct f).obj M) = (Core.Model.reduct f).obj (reconstruct M) := by
  change Core.Model.mk _ _ _ = Core.Model.mk _ _ _
  congr 1
  funext n w s t args x
  have hw : Fin.cases (f.sorts s) (f.sorts ∘ w) = f.sorts ∘ Fin.cases s w := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change M.obj.rel (.row (w := f.sorts ∘ Fin.cases s w) (f.functions t))
    (Fin.cases x args) =
    M.obj.rel (.row (w := Fin.cases (f.sorts s) (f.sorts ∘ w)) (f.functions t))
      (Fin.cases x args)
  congr 1
  · exact hw.symm
  · exact row_heq hw.symm _ _ HEq.rfl
  · apply Function.hfunext rfl
    intro i j hij
    cases hij
    exact Fin.cases HEq.rfl (fun _ => HEq.rfl) i

/-- Reconstruction is natural on both objects and actual public FOL arrows. -/
theorem models_natural {S T : Signature} (f : S ⟶ T) :
    reduct f ⋙ models S = models T ⋙ Core.Model.reduct f := by
  refine Functor.ext (reconstruct_reduct f) (fun M N h => ?_)
  apply Core.Model.Hom.ext
  funext s x
  exact (core_eqToHom_comp_map (reconstruct_reduct f M)
    ((models T ⋙ Core.Model.reduct f).map h) (reconstruct_reduct f N).symm s x).symm

/-- Existing normalized sentences have their exact meaning in independent models. -/
theorem sentence_holds {S : Signature} (M : IndependentModel S) (s : Core.Sentence S) :
    (Graph.sentence s).Holds M.obj ↔ s.Holds (reconstruct M) := by
  rw [← graph_reconstruct M]
  exact Graph.sentence_holds (reconstruct M) s

private theorem reduct_id_obj (S : Signature) (M : IndependentModel S) :
    (reduct (𝟙 S)).obj M = M := by
  apply ObjectProperty.FullSubcategory.ext
  change (FOL.Structure.reduct (signatureMap (𝟙 S))).obj M.obj = M.obj
  rw [show signatureMap (𝟙 S) = 𝟙 (signature S) from signatures.map_id S]
  rfl

private theorem reduct_comp_obj {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (M : IndependentModel U) :
    (reduct (f ≫ g)).obj M = (reduct f).obj ((reduct g).obj M) := by
  apply ObjectProperty.FullSubcategory.ext
  change (FOL.Structure.reduct (signatureMap (f ≫ g))).obj M.obj =
    (FOL.Structure.reduct (signatureMap f)).obj
      ((FOL.Structure.reduct (signatureMap g)).obj M.obj)
  rw [show signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g from signatures.map_comp f g]
  rfl

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := reindex
  map_id S := by
    apply Room.hom_ext
    · funext p
      change p.map (signatures.map (𝟙 S)) = p
      rw [signatures.map_id]
      exact FOL.Sentence.map_id p
    · refine Functor.ext (reduct_id_obj S) (fun M N h => ?_)
      apply ObjectProperty.hom_ext
      apply folHom_ext
      funext s x
      exact (independent_eqToHom_comp_map (reduct_id_obj S M) h
        (reduct_id_obj S N).symm s x).symm
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      change p.map (signatures.map (f ≫ g)) =
        (p.map (signatures.map f)).map (signatures.map g)
      rw [signatures.map_comp]
      exact FOL.Sentence.map_comp _ _ p
    · refine Functor.ext (reduct_comp_obj f g) (fun M N h => ?_)
      apply ObjectProperty.hom_ext
      apply folHom_ext
      funext s x
      exact (independent_eqToHom_comp_map (reduct_comp_obj f g M)
        ((reduct g ⋙ reduct f).map h) (reduct_comp_obj f g N).symm s x).symm

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

/-- Sentence syntax is structural; the model reduct reconstructs an independently
supplied FOL structure. No target object is defined as an Egglog model. -/
def fromCore : Inst.CoHom Core.inst inst where
  Φ := 𝟭 Signature
  ρ :=
    { app := fun S => ⟨Graph.sentence, models S, sentence_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (Graph.sentence_map f)) (models_natural f).symm }

theorem fromCore_modelExpansive : fromCore.ModelExpansive :=
  fun S M => ⟨(embed S).obj M, reconstruct_graph M⟩

/-- Actual unrestricted public FOL pulled back along the structural graph signatures. -/
def publicInst : Inst.{1,0,0,0,1} := ⟨Signature, signatures ⋙ FOL.institution⟩

/-- Restrict models to FD without changing any FOL sentence. This direction does
not claim model expansion from an arbitrary unrestricted FOL structure. -/
def restriction : Inst.CoHom publicInst inst where
  Φ := 𝟭 Signature
  ρ :=
    { app := fun S => ⟨id,(FD S).ι,fun _ _ => Iff.rfl⟩
      naturality := by
        intro S T f
        exact Room.hom_ext rfl rfl }

/-- Every full graph-FOL theory has the same models after reconstruction. -/
theorem theory_holds_iff {S : Signature} (M : IndependentModel S)
    (H : Set (FOL.Sentence (signature S))) :
    (∀ p ∈ H, p.Holds M.obj) ↔ ∀ p ∈ H, p.Holds (model (reconstruct M)) := by
  rw [graph_reconstruct]

theorem sat_iff {S : Signature} (H : Set (FOL.Sentence (signature S))) :
    (∃ M : IndependentModel S, ∀ p ∈ H, p.Holds M.obj) ↔
      ∃ M : Core.Model S, ∀ p ∈ H, p.Holds (model M) := by
  constructor
  · rintro ⟨M,h⟩
    exact ⟨reconstruct M, (theory_holds_iff M H).mp h⟩
  · rintro ⟨M,h⟩
    exact ⟨(embed S).obj M,h⟩

theorem unsat_iff {S : Signature} (H : Set (FOL.Sentence (signature S))) :
    (¬ ∃ M : IndependentModel S, ∀ p ∈ H, p.Holds M.obj) ↔
      ¬ ∃ M : Core.Model S, ∀ p ∈ H, p.Holds (model M) := not_congr (sat_iff H)

theorem entails_iff {S : Signature} (H : Set (FOL.Sentence (signature S)))
    (p : FOL.Sentence (signature S)) :
    (∀ M : IndependentModel S, (∀ q ∈ H, q.Holds M.obj) → p.Holds M.obj) ↔
      ∀ M : Core.Model S, (∀ q ∈ H, q.Holds (model M)) → p.Holds (model M) := by
  constructor
  · intro h M
    exact h ((embed S).obj M)
  · intro h M hm
    rw [← graph_reconstruct M]
    exact h (reconstruct M) ((theory_holds_iff M H).mp hm)

end Silmaril.Logic.Egglog.Core.Graph.Functional
