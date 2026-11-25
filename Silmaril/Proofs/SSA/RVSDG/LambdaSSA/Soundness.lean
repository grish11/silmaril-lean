module

public import Silmaril.SSA.RVSDG.LambdaSSA.Categorical.Defs
public import Silmaril.SSA.RVSDG.Categorical.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst snd lift toUnit)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj lookup Denotes)

universe u v d h c k
variable {τ : Type u} {Φ : Type v} [HasTy Φ τ]
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
variable {root Γ : List τ} {past sigs : List (Ports (Ty τ))} {A : τ}

section Ports

variable (m : Categorical.Model (Opcode (τ := τ) Φ) D) {args out : Ports (Ty τ)} {t : Ty τ}

set_option backward.isDefEq.respectTransparency false in
private theorem project_prior (past : List (Ports (Ty τ))) (i : Fin past.length)
    (p : Port past[i] t) :
    Categorical.appendLocal m out past ≫
        Categorical.projectLocal m (past ++ [out]) (priorIndex out past i) ≫
          Categorical.project m (priorPort out past i p) =
      fst _ _ ≫ Categorical.projectLocal m past i ≫ Categorical.project m p := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    revert p
    refine Fin.cases ?_ (fun j => ?_) i
    · intro p
      simp [priorIndex, priorPort, Categorical.appendLocal, Categorical.projectLocal, Categorical.Model.locals]
    · intro p
      simp [priorIndex, priorPort, Categorical.appendLocal, Categorical.projectLocal, ih, Categorical.Model.locals]

set_option backward.isDefEq.respectTransparency false in
private theorem project_last (past : List (Ports (Ty τ))) (p : Port out t) :
    Categorical.appendLocal m out past ≫
        Categorical.projectLocal m (past ++ [out]) (lastIndex out past) ≫
          Categorical.project m (lastPort p past) =
      snd _ _ ≫ Categorical.project m p := by
  induction past with
  | nil =>
    simp [lastIndex, lastPort, Categorical.appendLocal, Categorical.projectLocal,
      CartesianMonoidalCategory.leftUnitor_hom, Categorical.Model.locals]
  | cons head tail ih =>
    simp [lastIndex, lastPort, Categorical.appendLocal, Categorical.projectLocal, ih, Categorical.Model.locals]

private theorem read_keep (out : Ports (Ty τ)) (o : Origin args past t) :
    Categorical.appendScope m out ≫ Categorical.readOrigin m (keepOrigin out o) =
      fst _ _ ≫ Categorical.readOrigin m o := by
  cases o with
  | arg p => simp [keepOrigin, Categorical.appendScope, Categorical.readOrigin]
  | output i p =>
    simp [keepOrigin, Categorical.appendScope, Categorical.readOrigin, project_prior, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem read_new (args : Ports (Ty τ)) (past : List (Ports (Ty τ))) (A : τ) :
    Categorical.appendScope m [.value A] ≫ Categorical.readOrigin m (newOrigin args past A) =
      snd _ _ ≫ (ρ_ (m.value A)).hom := by
  simp [newOrigin, Categorical.appendScope, Categorical.readOrigin, project_last,
    Categorical.project, Categorical.portsObj,
    CartesianMonoidalCategory.rightUnitor_hom, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem read_singleton (o : Origin args past t) :
    Categorical.readWires m (.cons o .nil) ≫ (ρ_ (m.port t)).hom =
      Categorical.readOrigin m o := by
  rw [CartesianMonoidalCategory.rightUnitor_hom]
  exact CartesianMonoidalCategory.lift_fst _ _

end Ports

variable [TypeFormers τ] [HasFiniteCoproducts D]
variable (M : TypeModel τ D) (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))

set_option backward.isDefEq.respectTransparency false in
private theorem gather_lookup {X : D} (p : Port Γ A)
    (projections : ∀ {B : τ}, Port Γ B → (X ⟶ M.obj B)) :
    gather M Γ projections ≫ lookup M (index p) (index_at p) = projections p := by
  induction p with
  | head =>
    change lift _ (projections .head) ≫ snd _ _ = _
    simp
  | tail p ih =>
    change lift (gather M _ (fun q => projections (.tail q))) _ ≫
      (fst _ _ ≫ lookup M (index p) (index_at p)) = _
    rw [CartesianMonoidalCategory.lift_fst_assoc]
    exact ih (fun q => projections (.tail q))

set_option backward.isDefEq.respectTransparency false in
private theorem comp_gather {X Y : D} (f : X ⟶ Y) (Γ : List τ)
    (projections : ∀ {B : τ}, Port Γ B → (Y ⟶ M.obj B)) :
    f ≫ gather M Γ projections = gather M Γ (fun p => f ≫ projections p) := by
  induction Γ with
  | nil => exact CartesianMonoidalCategory.toUnit_unique _ _
  | cons head tail ih =>
    change _ ≫ lift (gather M tail (fun p => projections (.tail p))) (projections .head) = _
    rw [CartesianMonoidalCategory.comp_lift, ih]
    rfl

theorem context_lookup (s : Scope root past Γ) (p : Port Γ A) :
    s.contextMap M sel prim ≫ lookup M (index p) (index_at p) =
      Categorical.readOrigin (valueModel M sel prim) (s.origin p) :=
  gather_lookup M p _

set_option backward.isDefEq.respectTransparency false in
theorem entry_lookup (p : Port Γ A) :
    entryMap M Γ sel prim ≫ lookup M (index p) (index_at p) =
      Categorical.project (valueModel M sel prim) (inputPort p) := by
  rw [entryMap, Category.assoc, context_lookup]
  simp [Scope.origin, Categorical.readOrigin, Categorical.Model.locals]

set_option backward.isDefEq.respectTransparency false in
private theorem context_step (s : Scope root past Γ) (B : τ) :
    Categorical.appendScope (valueModel M sel prim) [.value B] ≫ (s.bind B).contextMap M sel prim =
      lift (fst _ _ ≫ s.contextMap M sel prim) (snd _ _ ≫ (ρ_ (M.obj B)).hom) := by
  let m := valueModel M sel prim
  change Categorical.appendScope m (args := inputs root) (past := past) [.value B] ≫
    lift (gather M Γ (fun p => Categorical.readOrigin m (keepOrigin [.value B] (s.origin p))))
      (Categorical.readOrigin m (newOrigin _ _ B)) = _
  rw [CartesianMonoidalCategory.comp_lift, read_new, comp_gather]
  simp only [Scope.contextMap, comp_gather, read_keep]
  rfl

variable {C : Type c} [Category.{k} C] [SymmetricCategory D]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor D] [DistributivePremonoidalCategory C]
  (J : D ⥤ C) [DistributiveFreydCategory J] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem related_sound
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {s : Scope root past Γ} {t : Silmaril.Isotope.LambdaSSA.Tm Φ}
    {rv : Term (Opcode Φ) (inputs root) past sigs [.value A]} (h : Related s t rv) :
    ∃ f : ctxObj M Γ ⟶ M.obj A, Denotes J M h.typing (J.map f) ∧
      s.contextMap M sel prim ≫ f = rv.denoteOpen (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom := by
  induction h with
  | ret p =>
    refine ⟨lookup M (index p) (index_at p), .var _, ?_⟩
    exact (context_lookup M sel prim _ p).trans (read_singleton _ _).symm
  | @bind past Γ s sigs op p body rest rel ih =>
    obtain ⟨f, hf, hr⟩ := ih
    let a := lookup M (index p) (index_at p) ≫ prim op
    refine ⟨lift (𝟙 _) a ≫ f, ?_, ?_⟩
    · rw [← Categorical.freyd_bind_map]
      have d : Denotes J M (.op (f := op) (.var (index_at p))) (J.map a) := by
        dsimp only [a]
        rw [Functor.map_comp, ← agree op]
        exact .op (.var _)
      exact .let₁ d hf
    · let m := valueModel M sel prim
      let step := Categorical.readWires m (node s op p).inputs ≫
        Categorical.denoteShape m (node s op p).shape
          (fun j => j.elim0)
      have hstep : step = (s.contextMap M sel prim ≫ a) ≫ (ρ_ (M.obj (instrTrg op))).inv := by
        change Categorical.readWires m (.cons (s.origin p) .nil) ≫
          ((ρ_ (M.obj (instrSrc op))).hom ≫ prim op ≫ (ρ_ (M.obj (instrTrg op))).inv) = _
        have wire : Categorical.readWires m (.cons (s.origin p) .nil) ≫
            (ρ_ (M.obj (instrSrc op))).hom = Categorical.readOrigin m (s.origin p) :=
          read_singleton m (s.origin p)
        rw [← Category.assoc, wire]
        simp only [a, Category.assoc]
        rw [← Category.assoc (s.contextMap M sel prim)]
        exact (congrArg (fun read => read ≫ prim op ≫ (ρ_ _).inv)
          (context_lookup M sel prim s p)).symm
      change s.contextMap M sel prim ≫ (lift (𝟙 _) a ≫ f) =
        (Categorical.extendScope m step ≫ rest.denoteOpen m) ≫ (ρ_ (M.obj A)).hom
      have hlaw : Categorical.appendScope m [.value (instrTrg op)] ≫
          (s.bind (instrTrg op)).contextMap M sel prim = _ :=
        context_step M sel prim s (instrTrg op)
      have hc : Categorical.extendScope m step ≫ (s.bind (instrTrg op)).contextMap M sel prim =
          lift (s.contextMap M sel prim) (s.contextMap M sel prim ≫ a) := by
        unfold Categorical.extendScope
        rw [Category.assoc, hlaw]
        simp [hstep, Category.assoc]
      rw [Category.assoc, ← hr, ← Category.assoc (Categorical.extendScope m step), hc]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem graph_sound
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {t : Silmaril.Isotope.LambdaSSA.Tm Φ}
    {g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]} (rel : GraphRelated t g) :
    ∃ f : ctxObj M Γ ⟶ M.obj A, Denotes J M rel.typing (J.map f) ∧
      J.map (entryMap M Γ sel prim) ≫ J.map f =
        J.map (g.denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom) := by
  obtain ⟨f, hden, hscope⟩ := related_sound M sel prim J agree rel
  refine ⟨f, hden, ?_⟩
  rw [← J.map_comp]
  apply congrArg J.map
  rw [entryMap, Category.assoc, hscope, ← Category.assoc, ← Term.denote, Graph.denote_toTerm]

end Silmaril.SSA.RVSDG.LambdaSSA.Proofs
