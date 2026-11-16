module

public import Silmaril.Proofs.Logic.Matching.GeneralFixedPoint.SetObjects.Renaming

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

theorem Pattern.denoteSetObjects_shiftObjects {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s b : S} (p : Pattern A P Γ s)
    (v : SetObjEnv M Γ) (η : SetEnv A M P) (x : M.carrier b) :
    (p.renameObjects (Ren.shift Γ b)).denoteSetObjects M (Fin.cases {x} v) η = p.denoteSetObjects M v η := by
  rw [Pattern.denoteSetObjects_renameObjects]
  rfl

theorem Pattern.denoteSetObjects_shiftSets {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s b : S} (p : Pattern A P Γ s)
    (v : SetObjEnv M Γ) (η : SetEnv A M P) (X : Set (M.carrier b)) :
    (p.renameSets (Ren.shift P b)).denoteSetObjects M v (Fin.cases X η) = p.denoteSetObjects M v η := by
  rw [Pattern.denoteSetObjects_renameSets]
  rfl

/-- Element-named formals may denote arbitrary sets.
No monotonicity or positivity hypothesis is needed for this semantic equality. -/
theorem substituteFirstOrderSets_denote {A : Signature S} (M : Model A) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ {r l : Nat} {Q : Fin r → S} {Δ : Fin l → S}
      (τ : ∀ i, Pattern A Q Δ (Γ i)) (v : SetObjEnv M Δ) (η : SetEnv A M Q)
      (w : SetObjEnv M Γ),
      (∀ i, (τ i).denoteSetObjects M v η = w i) →
      (substituteFirstOrder p τ).denoteSetObjects M v η = denoteFirstOrderSets M p w := by
  induction p with
  | var i => intro r l Q Δ τ v η w h; exact h i
  | app op args ih =>
      intro r l Q Δ τ v η w h
      change FixedPoint.application M op
        (fun i => (substituteFirstOrder (args i) τ).denoteSetObjects M v η) = _
      exact congrArg (FixedPoint.application M op)
        (funext (fun i => ih i τ v η w h))
  | neg p hp =>
      intro r l Q Δ τ v η w h
      exact congrArg (fun X => Xᶜ) (hp τ v η w h)
  | conj p q hp hq =>
      intro r l Q Δ τ v η w h
      exact congrArg₂ Set.inter (hp τ v η w h) (hq τ v η w h)
  | ex bound p hp =>
      intro r l Q Δ τ v η w h
      change {x | ∃ a : M.carrier bound, x ∈
        (substituteFirstOrder p (Fin.cases (.base (.var (Γ := Fin.cases bound Δ) 0))
          (fun i => (τ i).renameObjects (Ren.shift Δ bound)))).denoteSetObjects M (Fin.cases {a} v) η} = _
      have step (a : M.carrier bound) := hp
        (Fin.cases (.base (.var (Γ := Fin.cases bound Δ) 0)) (fun i => (τ i).renameObjects (Ren.shift Δ bound)))
        (Fin.cases {a} v) η (Fin.cases {a} w)
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denoteSetObjects_shiftObjects M (τ j) v η a).trans (h j)) i)
      simp only [step]
      rfl

/-- Full simultaneous substitution through both namespaces and all binders.
Set replacements denote arbitrary sets. Element replacements denote the
sets assigned by the source formal environment. -/
theorem Pattern.denoteSetObjects_substitute_env {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {Δ : Fin b → S}
      (σ : ∀ i, Pattern A Q Δ (P i)) (τ : ∀ i, Pattern A Q Δ (Γ i))
      (v : SetObjEnv M Δ) (η : SetEnv A M Q)
      (w : SetObjEnv M Γ) (θ : SetEnv A M P),
      (∀ i, (σ i).denoteSetObjects M v η = θ i) →
      (∀ i, (τ i).denoteSetObjects M v η = w i) →
      (p.substitute σ τ).denoteSetObjects M v η = p.denoteSetObjects M w θ := by
  induction p with
  | base p =>
      intro a b Q Δ σ τ v η w θ hs ht
      exact substituteFirstOrderSets_denote M p τ v η w ht
  | setvar i => intro a b Q Δ σ τ v η w θ hs ht; exact hs i
  | app op args ih =>
      intro a b Q Δ σ τ v η w θ hs ht
      change FixedPoint.application M op
        (fun i => ((args i).substitute σ τ).denoteSetObjects M v η) = _
      exact congrArg (FixedPoint.application M op)
        (funext (fun i => ih i σ τ v η w θ hs ht))
  | neg p hp =>
      intro a b Q Δ σ τ v η w θ hs ht
      exact congrArg (fun X => Xᶜ) (hp σ τ v η w θ hs ht)
  | conj p q hp hq =>
      intro a b Q Δ σ τ v η w θ hs ht
      exact congrArg₂ Set.inter (hp σ τ v η w θ hs ht) (hq σ τ v η w θ hs ht)
  | ex bound p hp =>
      intro a b Q Δ σ τ v η w θ hs ht
      change {x | ∃ z : M.carrier bound, x ∈
        (p.substitute (fun i => (σ i).renameObjects (Ren.shift Δ bound))
          (Fin.cases (.base (.var (Γ := Fin.cases bound Δ) 0))
            (fun i => (τ i).renameObjects (Ren.shift Δ bound)))).denoteSetObjects M (Fin.cases {z} v) η} = _
      have step (z : M.carrier bound) := hp
        (fun i => (σ i).renameObjects (Ren.shift Δ bound))
        (Fin.cases (.base (.var (Γ := Fin.cases bound Δ) 0)) (fun i => (τ i).renameObjects (Ren.shift Δ bound)))
        (Fin.cases {z} v) η (Fin.cases {z} w) θ
        (fun i => (Pattern.denoteSetObjects_shiftObjects M (σ i) v η z).trans (hs i))
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denoteSetObjects_shiftObjects M (τ j) v η z).trans (ht j)) i)
      simp only [step]
      rfl
  | @mu r k P' Γ p hp =>
      intro a b Q Δ σ τ v η w θ hs ht
      change sInf {X |
        (p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).denoteSetObjects M v (Fin.cases X η) ⊆ X} = _
      have step (X : Set (M.carrier (P' 0))) := hp
        (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
        (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))
        v (Fin.cases X η) w (Fin.cases X θ)
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denoteSetObjects_shiftSets M (σ j) v η X).trans (hs j)) i)
        (fun i => (Pattern.denoteSetObjects_shiftSets M (τ i) v η X).trans (ht i))
      simp only [step]
      rfl
  | @nu r k P' Γ p hp =>
      intro a b Q Δ σ τ v η w θ hs ht
      change sSup {X | X ⊆
        (p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).denoteSetObjects M v (Fin.cases X η)} = _
      have step (X : Set (M.carrier (P' 0))) := hp
        (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
        (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))
        v (Fin.cases X η) w (Fin.cases X θ)
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denoteSetObjects_shiftSets M (σ j) v η X).trans (hs j)) i)
        (fun i => (Pattern.denoteSetObjects_shiftSets M (τ i) v η X).trans (ht i))
      simp only [step]
      rfl

theorem Pattern.denoteSetObjects_substitute {A : Signature S} (M : Model A) {r k a b : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {Q : Fin a → S} {Δ : Fin b → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Δ (P i))
    (τ : ∀ i, Pattern A Q Δ (Γ i)) (v : SetObjEnv M Δ) (η : SetEnv A M Q)
    (w : SetObjEnv M Γ) (h : ∀ i, (τ i).denoteSetObjects M v η = w i) :
    (p.substitute σ τ).denoteSetObjects M v η =
      p.denoteSetObjects M w (fun i => (σ i).denoteSetObjects M v η) :=
  p.denoteSetObjects_substitute_env M σ τ v η w _ (fun _ => rfl) h

theorem Pattern.denoteSetObjects_substituteSets {A : Signature S} (M : Model A) {r k a : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {Q : Fin a → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Γ (P i))
    (v : SetObjEnv M Γ) (η : SetEnv A M Q) :
    (p.substituteSets σ).denoteSetObjects M v η =
      p.denoteSetObjects M v (fun i => (σ i).denoteSetObjects M v η) :=
  p.denoteSetObjects_substitute M σ (fun i => .base (.var i)) v η v (fun _ => rfl)

end Silmaril.Logic.Matching.GeneralFixedPoint
