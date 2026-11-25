module

public import Silmaril.SSA.MLIR.SCF.LetIter.Syntax
public import Silmaril.SSA.MLIR.SCF.LetIter.Operational

/-! # Observational institutions for the region view and native LetIter

The existing observational institution uses the discrete category of finite scopes.
Both presentations also admit context renamings as signature morphisms at fixed
instruction alphabet. Reduct precomposes the bound environment by the renaming.
-/

@[expose] public section

universe u v w

namespace Silmaril.MLIR.SCF.LetIter

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational (Sentence)
open Silmaril.Isotope.Institution.Observational (Behaviour Model Observation iterBeh letIter noFree)
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.Semantics (Eval Fault)

variable {Φ : Type u}

/-- Region programs with the independently defined boundary observations. -/
def regionBehaviour (Φ : Type u) : Behaviour.{u, v, w} Φ where
  Prog := RegionLoop Φ
  Out := Silmaril.Isotope.Value
  beh M p := p.observe M

/-- The comparison to the existing native observational institution over discrete scopes.
The model and answer translations are identities. -/
def lowerTranslation : Behaviour.Translation (regionBehaviour.{u, v, w} Φ) (letIter Φ) where
  prog := RegionLoop.lower
  out := id
  dom := Set.univ
  injOn := by intro α a ha b hb h; exact h
  beh_sub := by
    intro n M p o _
    cases o <;> trivial
  beh_prog := by
    intro n M p
    change iterBeh M p.lower = Observation.mapValue (id : Silmaril.Isotope.Value M.α → _) '' p.observe M
    rw [Observation.mapValue_id, Set.image_id]
    exact RegionLoop.observe_eq_iterBeh.symm

/-- The original discrete-scope institution comparison. -/
def lowerDiscrete : Inst.CoHom (regionBehaviour.{u, v, w} Φ).inst (letIter.{u, v, w} Φ).inst :=
  lowerTranslation.{u, v, w}.coHom

/-- Both renaming institutions use finite positional contexts as signatures. -/
structure Scope where
  arity : Nat

instance : Category Scope where
  Hom S T := Fin S.arity → Fin T.arity
  id _ := id
  comp f g := g ∘ f

/-- Reduct leaves the instruction and state model in place and reindexes the bound values. -/
def reduct {S T : Scope} (f : S ⟶ T) (M : Model.{u, v, w} Φ T.arity) : Model.{u, v, w} Φ S.arity where
  α := M.α
  σ := M.σ
  instr := M.instr
  faults := M.faults
  prim := M.prim
  bound i := M.bound (f i)

@[simp] theorem reduct_id {S : Scope} (M : Model.{u, v, w} Φ S.arity) : reduct (𝟙 S) M = M := rfl

theorem reduct_comp {S T U : Scope} (f : S ⟶ T) (g : T ⟶ U) (M : Model.{u, v, w} Φ U.arity) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

/-- The contravariant model action on a signature morphism, for both institutions. -/
def reductFunctor {S T : Scope} (f : S ⟶ T) :
    Discrete (Model.{u, v, w} Φ T.arity) ⥤ Discrete (Model.{u, v, w} Φ S.arity) :=
  Discrete.functor fun M => Discrete.mk (reduct f M)

theorem reductFunctor_id (S : Scope) : reductFunctor (Φ := Φ) (𝟙 S) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun M => by cases M; rfl)

theorem reductFunctor_comp {S T U : Scope} (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor (Φ := Φ) (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  CategoryTheory.Functor.ext (fun M => by cases M; rfl)

/-- Native LetIter answers commute with model reduct along every context renaming. -/
theorem iterBeh_rename {S T : Scope} (f : S ⟶ T) (M : Model.{u, v, w} Φ T.arity)
    (t : Tm Empty Φ S.arity) : iterBeh M (t.rename f) = iterBeh (reduct f M) t :=
  Observation.set_eq_iff.mpr ⟨fun _ _ _ => Eval.rename_iff (fun _ => rfl),
    fun _ _ => Fault.rename_iff (fun _ => rfl), fun _ => Silmaril.Isotope.LetIter.Semantics.External.Diverges.rename_iff (fun _ => rfl)⟩

/-- Region-view answers commute with the same model reduct. -/
theorem RegionLoop.observe_rename {S T : Scope} (f : S ⟶ T) (M : Model.{u, v, w} Φ T.arity)
    (p : RegionLoop Φ S.arity) : (p.rename f).observe M = p.observe (reduct f M) := by
  rw [observe_eq_iterBeh, lower_rename, iterBeh_rename, observe_eq_iterBeh]

/-- Construct an institution from a renaming action and its reduct law. -/
def ofRenaming
    (B : Behaviour.{u, v, w} Φ)
    (ren : {n m : Nat} → (Fin n → Fin m) → B.Prog n → B.Prog m)
    (ren_id : ∀ {n} (p : B.Prog n), ren id p = p)
    (ren_comp : ∀ {n m k} (f : Fin n → Fin m) (g : Fin m → Fin k) (p : B.Prog n),
      ren g (ren f p) = ren (g ∘ f) p)
    (beh_ren : ∀ {S T : Scope} (f : S ⟶ T) (M : Model.{u, v, w} Φ T.arity) (p : B.Prog S.arity),
      B.beh M (ren f p) = B.beh (reduct f M) p) :
    Inst.{0, 0, u, max u (v + 1) (w + 1), max u (v + 1) (w + 1)} where
  Sign := Scope
  I := {
    obj S := B.room S.arity
    map {S T} f := ⟨Sentence.map (ren f), reductFunctor f, fun M φ => by
      change (Sentence.map (ren f) φ).Holds (B.beh M.as) ↔ φ.Holds (B.beh (reduct f M.as))
      cases φ <;> simp only [Sentence.map, Sentence.Holds, beh_ren] <;> rfl⟩
    map_id S := Room.hom_ext (by
      change Sentence.map (ren (n := S.arity) id) = id
      rw [show ren (n := S.arity) id = id from funext ren_id, Sentence.map_id]) (reductFunctor_id S)
    map_comp f g := Room.hom_ext (by
      change Sentence.map (ren (g ∘ f)) = Sentence.map (ren g) ∘ Sentence.map (ren f)
      rw [Sentence.map_comp]
      exact congrArg Sentence.map (funext fun p => (ren_comp f g p).symm)) (reductFunctor_comp f g) }

set_option linter.checkUnivs false in
/-- Region-view institution. Sen translates by renaming both programs. Mod
is the discrete category of native models, with reduct as above. Sat compares
region answers by equality or inclusion. -/
def regionInstitution (Φ : Type u) :=
  ofRenaming (regionBehaviour.{u, v, w} Φ) RegionLoop.rename
    RegionLoop.rename_id (fun f g p => p.rename_comp f g) RegionLoop.observe_rename

set_option linter.checkUnivs false in
/-- Native observational LetIter with context renamings as signature morphisms.
Its rooms use the same Sen, Mod and Sat as the original native institution at each scope. -/
def nativeInstitution (Φ : Type u) :=
  ofRenaming (letIter.{u, v, w} Φ) Tm.rename Tm.rename_id
    (fun f g p => Tm.rename_comp f g p) iterBeh_rename

/-- The renaming-natural institution comorphism maps sentences by lowering
both programs. Its signature functor and model components are identities. -/
def lowerComorphism : Inst.CoHom (regionInstitution.{u, v, w} Φ) (nativeInstitution.{u, v, w} Φ) where
  Φ := 𝟭 Scope
  ρ := {
    app S := lowerTranslation.corridor S.arity
    naturality := by
      intro S T f
      apply Room.hom_ext
      · change Sentence.map RegionLoop.lower ∘ Sentence.map (RegionLoop.rename f) =
          Sentence.map (Tm.rename f) ∘ Sentence.map RegionLoop.lower
        simp only [Sentence.map_comp]
        exact congrArg Sentence.map (funext fun p => p.lower_rename f)
      · change (𝟭 _ ⋙ reductFunctor (Φ := Φ) f) = reductFunctor f ⋙ 𝟭 _
        rfl }

end Silmaril.MLIR.SCF.LetIter
