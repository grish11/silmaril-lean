module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Iteration

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs

open Silmaril.Elgot
open Isotope.LambdaSSA (Tm Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics

universe u

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A : τ}

set_option backward.isDefEq.respectTransparency false

omit [Iterate m] [LawfulElgotMonad m] in
private theorem opDenotes (op : Φ) (A B : τ) (Γ : List τ)
    (src : instrSrc op = A) (dst : instrTrg op = B)
    (h : Tm.HasType (A :: Γ) (.op op (.var 0)) B) :
    Denotes (m := m) ε h (fun ρ =>
      InstructionModel.denote (m := m) (ε := ε) op (src.symm ▸ ρ.2) >>=
        fun y => pure (dst ▸ y)) := by
  subst A
  subst B
  have dh := Denotes.op (m := m) (ε := ε) (Denotes.var (Φ := Φ)
    (Γ := instrSrc op :: Γ) (i := 0) rfl)
  simpa [Env.get] using dh

omit [LawfulElgotMonad m] in
private theorem blockDenotes (s : Step Φ A) :
    RegionDenotes (m := m) ε (blockTyping s) (fun env =>
      stepMap (m := m) (ε := ε) s env.2 >>= fun result => pure (bodyTarget result)) := by
  have op := opDenotes (m := m) (ε := ε) s.op A (Silmaril.coprod A A) [A]
    s.input s.output (s.typing [A])
  have l : RegionDenotes (m := m) ε
      (.br (L := [A, A]) (ℓ := 1) rfl (.var (Φ := Φ) (Γ := [A, A, A]) (i := 0) rfl))
      (fun env => pure (Sum.inr (exit env.2))) := by
    have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,A] 1 A from rfl))
      (Denotes.var (Φ := Φ) (Γ := [A,A,A]) (i := 0) rfl)
    simpa [Env.get, exit, LabelValue.inject] using d
  have r : RegionDenotes (m := m) ε
      (.br (L := [A, A]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A, A, A]) (i := 0) rfl))
      (fun env => pure (Sum.inl env.2)) := by
    have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,A] 0 A from rfl))
      (Denotes.var (Φ := Φ) (Γ := [A,A,A]) (i := 0) rfl)
    simpa [Env.get, LabelValue.inject] using d
  have d := RegionDenotes.case op l r
  simp only [stepMap, bind_assoc, pure_bind]
  convert d using 1
  · rfl
  · funext env
    rw [bind_assoc]
    congr 1
    funext result
    simp only [pure_bind]
    cases TypeModel.coprodEquiv A A (s.output ▸ result) <;> rfl

theorem region_iterates_of_body {b : Region Φ} (typing : Region.HasType [A,A] b [A,A])
    (step : TyDen A → m (TyDen A ⊕ TyDen A))
    (body : RegionDenotes (m := m) ε typing
      (fun env => step env.2 >>= fun result => pure (bodyTarget result))) :
    RegionDenotes (m := m) ε (.cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (fun _ => typing))
      (fun env => iter step env.2 >>= fun a => pure (exit a)) := by
  let R : Fin 1 → τ := fun _ => A
  let entry : Env [A] → m (LabelDen [A,A]) := fun env => pure (Sum.inl env.2)
  have entryDen : RegionDenotes (m := m) ε
      (.br (L := [A,A]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)) entry := by
    have d := RegionDenotes.br (m := m) (ε := ε) (h := (show Isotope.SSA.At [A,A] 0 A from rfl))
      (Denotes.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)
    simpa [Env.get, entry, LabelValue.inject] using d
  let dispatcher : Env [A] × FiniteLabelDen R → m (LabelDen [A,A]) :=
    fun env => step env.2.2 >>= fun result => pure (bodyTarget result)
  have collective : CollectiveDenotes [A] R [A]
      (fun _ env => step env.2 >>= fun result => pure (bodyTarget result)) dispatcher :=
    ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ entryDen (fun _ => body) collective
  have eq : cfgDenotation (R := R) entry dispatcher =
      (fun env => iter step env.2 >>= fun a => pure (exit a)) := by
    funext env
    let g : LabelDen [A] → m (LabelDen [A] ⊕ LabelDen [A]) := fun current =>
      dispatcher (env, labelDenToFinite R current) >>= fun next =>
        pure (LabelValue.appendSplit [A] [A] next)
    have g_spec (a : TyDen A) :
        g (exit a) = step a >>= fun result => pure (Sum.map exit exit result) := by
      have route : labelDenToFinite R (exit a) = finiteLabelInject R 0 a := by
        exact labelDenToFinite_recursiveInject R 0 rfl a
      unfold g
      rw [route]
      simp only [dispatcher, finiteLabelInject, bind_assoc, pure_bind]
      congr 1
      funext result
      cases result <;> rfl
    have initial : LabelValue.appendSplit (List.ofFn R) [A]
        (Sum.inl env.2 : LabelDen (List.ofFn R ++ [A])) = Sum.inr (exit env.2) := rfl
    simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit, initial]
    change iter g (exit env.2) = _
    exact iter_boundary step g exit exit g_spec env.2
  rw [eq] at den
  exact den

theorem region_iterates (s : Step Φ A) :
    RegionDenotes (m := m) ε (regionTyping s)
      (fun env => iter (stepMap (m := m) (ε := ε) s) env.2 >>= fun a => pure (exit a)) :=
  region_iterates_of_body (blockTyping s) _ (blockDenotes s)

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs
