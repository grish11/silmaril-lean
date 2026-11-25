module

public import Silmaril.Semantics.Calco2019.Examples.Exceptions.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Exceptions.Proofs

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
  [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] {E F X Y : Type u}

omit [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] in
theorem adapt_pure (h : E → F) (x : X) :
    ExceptT.adapt h (pure x : ExceptT E m X) = pure x := by
  apply ExceptT.ext
  simp [Except.mapError]

omit [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] in
theorem adapt_bind (h : E → F) (p : ExceptT E m X) (k : X → ExceptT E m Y) :
    ExceptT.adapt h (p >>= k) = ExceptT.adapt h p >>= fun x => ExceptT.adapt h (k x) := by
  apply ExceptT.ext
  simp only [ExceptT.run_adapt, ExceptT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  intro r
  cases r with
  | error e => simp [Except.mapError]
  | ok x => rfl

theorem adapt_iter (h : E → F) (f : X → ExceptT E m (Y ⊕ X)) (x : X) :
    ExceptT.adapt h (Elgot.iter f x) = Elgot.iter (fun x => ExceptT.adapt h (f x)) x := by
  have hbody :
      Elgot.mapReturn (Elgot.ExceptT.body f) (Elgot.liftPure (Except.mapError h)) =
        Elgot.ExceptT.body (fun x => ExceptT.adapt h (f x)) := by
    funext x
    unfold Elgot.mapReturn Elgot.ExceptT.body Elgot.liftPure
    simp only [bind_assoc, Function.comp_apply, pure_bind, ExceptT.adapt, ExceptT.run_mk,
      bind_map_left]
    congr 1
    funext r
    cases r with
    | error e => rfl
    | ok r => cases r <;> rfl
  have hnat := congrFun
    (Elgot.LawfulElgotMonad.naturality (Elgot.ExceptT.body f)
      (Elgot.liftPure (Except.mapError h))) x
  rw [hbody] at hnat
  change Except.mapError h <$> Elgot.iter (Elgot.ExceptT.body f) x =
    Elgot.iter (Elgot.ExceptT.body (fun x => ExceptT.adapt h (f x))) x
  rw [map_eq_pure_bind]
  exact hnat

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

private def parameterMonadMap (h : E → F) :
    ofTypeMonad (ExceptT E m) ⟶ ofTypeMonad (ExceptT F m) where
  app _ := ↾(ExceptT.adapt h)
  naturality {A B} f := by
    ext p
    change ExceptT.adapt h (f <$> p) = f <$> ExceptT.adapt h p
    simp only [map_eq_pure_bind, adapt_bind, adapt_pure]
  app_η _ := by
    ext x
    exact adapt_pure h x
  app_μ _ := by
    ext p
    change ExceptT.adapt h (joinM p) = joinM (ExceptT.adapt h (ExceptT.adapt h <$> p))
    simp only [joinM, map_eq_pure_bind, adapt_bind, bind_assoc, adapt_pure, pure_bind, id_eq]

private noncomputable def parameterMap (h : E → F) : fibre m E ⟶ fibre m F where
  hom := parameterMonadMap h
  guarded _ _ := True.intro
  iteration f _ := by
    ext x
    exact adapt_iter h f x

/-- Functorial variation of the exception parameter in the total Elgot instance. -/
noncomputable def parametrized (m : Type u → Type u) [Monad m] [LawfulMonad m]
    [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] :
    ParametrizedGuardedElgotMonad typeCoproducts.{u} where
  obj := fibre m
  map f := parameterMap f
  map_id E := by
    apply GuardedElgotMonadHom.ext
    ext X p
    change ExceptT.adapt id p = p
    apply ExceptT.ext
    have h : Except.mapError (id : E → E) = (id : Except E X → Except E X) := by
      funext r
      cases r <;> rfl
    rw [ExceptT.run_adapt, h, id_map]
  map_comp {E F G} f g := by
    apply GuardedElgotMonadHom.ext
    ext X p
    change ExceptT.adapt (g ∘ f) p = ExceptT.adapt g (ExceptT.adapt f p)
    apply ExceptT.ext
    simp only [ExceptT.run_adapt, Functor.map_map]
    congr 1
    funext r
    cases r <;> rfl

theorem parametrized_obj (E : Type u) : (parametrized m).obj E = fibre m E := by
  unfold parametrized
  rfl

end Silmaril.Calco2019.Examples.Exceptions.Proofs
