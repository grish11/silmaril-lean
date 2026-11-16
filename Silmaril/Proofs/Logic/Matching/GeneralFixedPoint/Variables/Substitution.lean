module

public import Silmaril.Proofs.Logic.Matching.GeneralFixedPoint.Variables.Renaming

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

theorem Pattern.denote_shiftObjects {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s b : S} (p : Pattern A P Γ s)
    (v : ObjEnv A M Γ) (η : SetEnv A M P) (x : M.carrier b) :
    (p.renameObjects (Ren.shift Γ b)).denote M (Fin.cases x v) η = p.denote M v η := by
  rw [Pattern.denote_renameObjects]
  rfl

theorem Pattern.denote_shiftSets {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s b : S} (p : Pattern A P Γ s)
    (v : ObjEnv A M Γ) (η : SetEnv A M P) (X : Set (M.carrier b)) :
    (p.renameSets (Ren.shift P b)).denote M v (Fin.cases X η) = p.denote M v η := by
  rw [Pattern.denote_renameSets]
  rfl

/-- Element replacements need denote singletons only at the chosen valuation.
No monotonicity or positivity hypothesis is needed for this semantic equality. -/
theorem substituteFirstOrder_denote {A : Signature S} (M : Model A) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ {r l : Nat} {Q : Fin r → S} {Δ : Fin l → S}
      (τ : ∀ i, Pattern A Q Δ (Γ i)) (v : ObjEnv A M Δ) (η : SetEnv A M Q)
      (w : ObjEnv A M Γ),
      (∀ i, (τ i).denote M v η = {w i}) →
      (substituteFirstOrder p τ).denote M v η = M.denote w p := by
  induction p with
  | var i => intro r l Q Δ τ v η w h; exact h i
  | app op args ih =>
      intro r l Q Δ τ v η w h
      change FixedPoint.application M op
        (fun i => (substituteFirstOrder (args i) τ).denote M v η) = _
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
          (fun i => (τ i).renameObjects (Ren.shift Δ bound)))).denote M (Fin.cases a v) η} = _
      have step (a : M.carrier bound) := hp
        (Fin.cases (.base (.var (Γ := Fin.cases bound Δ) 0)) (fun i => (τ i).renameObjects (Ren.shift Δ bound)))
        (Fin.cases a v) η (Fin.cases a w)
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denote_shiftObjects M (τ j) v η a).trans (h j)) i)
      simp only [step]
      rfl

/-- Full simultaneous substitution through both namespaces and all binders.
Set replacements denote arbitrary sets. Element replacements must denote the
singletons assigned by the source element environment. -/
theorem Pattern.denote_substitute_env {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {Δ : Fin b → S}
      (σ : ∀ i, Pattern A Q Δ (P i)) (τ : ∀ i, Pattern A Q Δ (Γ i))
      (v : ObjEnv A M Δ) (η : SetEnv A M Q)
      (w : ObjEnv A M Γ) (θ : SetEnv A M P),
      (∀ i, (σ i).denote M v η = θ i) →
      (∀ i, (τ i).denote M v η = {w i}) →
      (p.substitute σ τ).denote M v η = p.denote M w θ := by
  induction p with
  | base p =>
      intro a b Q Δ σ τ v η w θ hs ht
      exact substituteFirstOrder_denote M p τ v η w ht
  | setvar i => intro a b Q Δ σ τ v η w θ hs ht; exact hs i
  | app op args ih =>
      intro a b Q Δ σ τ v η w θ hs ht
      change FixedPoint.application M op
        (fun i => ((args i).substitute σ τ).denote M v η) = _
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
            (fun i => (τ i).renameObjects (Ren.shift Δ bound)))).denote M (Fin.cases z v) η} = _
      have step (z : M.carrier bound) := hp
        (fun i => (σ i).renameObjects (Ren.shift Δ bound))
        (Fin.cases (.base (.var (Γ := Fin.cases bound Δ) 0)) (fun i => (τ i).renameObjects (Ren.shift Δ bound)))
        (Fin.cases z v) η (Fin.cases z w) θ
        (fun i => (Pattern.denote_shiftObjects M (σ i) v η z).trans (hs i))
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denote_shiftObjects M (τ j) v η z).trans (ht j)) i)
      simp only [step]
      rfl
  | @mu r k P' Γ p hp =>
      intro a b Q Δ σ τ v η w θ hs ht
      change sInf {X |
        (p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).denote M v (Fin.cases X η) ⊆ X} = _
      have step (X : Set (M.carrier (P' 0))) := hp
        (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
        (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))
        v (Fin.cases X η) w (Fin.cases X θ)
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denote_shiftSets M (σ j) v η X).trans (hs j)) i)
        (fun i => (Pattern.denote_shiftSets M (τ i) v η X).trans (ht i))
      simp only [step]
      rfl
  | @nu r k P' Γ p hp =>
      intro a b Q Δ σ τ v η w θ hs ht
      change sSup {X | X ⊆
        (p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).denote M v (Fin.cases X η)} = _
      have step (X : Set (M.carrier (P' 0))) := hp
        (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
        (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))
        v (Fin.cases X η) w (Fin.cases X θ)
        (fun i => Fin.cases rfl
          (fun j => (Pattern.denote_shiftSets M (σ j) v η X).trans (hs j)) i)
        (fun i => (Pattern.denote_shiftSets M (τ i) v η X).trans (ht i))
      simp only [step]
      rfl

theorem Pattern.denote_substitute {A : Signature S} (M : Model A) {r k a b : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {Q : Fin a → S} {Δ : Fin b → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Δ (P i))
    (τ : ∀ i, Pattern A Q Δ (Γ i)) (v : ObjEnv A M Δ) (η : SetEnv A M Q)
    (w : ObjEnv A M Γ) (h : ∀ i, (τ i).denote M v η = {w i}) :
    (p.substitute σ τ).denote M v η =
      p.denote M w (fun i => (σ i).denote M v η) :=
  p.denote_substitute_env M σ τ v η w _ (fun _ => rfl) h

theorem Pattern.denote_substituteSets {A : Signature S} (M : Model A) {r k a : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {Q : Fin a → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Γ (P i))
    (v : ObjEnv A M Γ) (η : SetEnv A M Q) :
    (p.substituteSets σ).denote M v η =
      p.denote M v (fun i => (σ i).denote M v η) :=
  p.denote_substitute M σ (fun i => .base (.var i)) v η v (fun _ => rfl)

end Silmaril.Logic.Matching.GeneralFixedPoint
