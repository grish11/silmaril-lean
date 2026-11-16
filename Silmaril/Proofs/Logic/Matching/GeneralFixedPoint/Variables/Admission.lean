module

public import Silmaril.Proofs.Logic.Matching.GeneralFixedPoint.Variables.Occurrence

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

theorem substituteFirstOrder_occurs_absent {A : Signature S} {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {Δ : Fin b → S}
      (τ : ∀ i, Pattern A Q Δ (Γ i)) (j : Fin a),
      (∀ i n, (τ i).occurs n j = false) → ∀ n,
      (substituteFirstOrder p τ).occurs n j = false := by
  induction p with
  | var i => intro a b Q Δ τ j h n; exact h i n
  | app op args ih =>
      intro a b Q Δ τ j h n
      change (List.finRange _).any (fun i => (substituteFirstOrder (args i) τ).occurs n j) = false
      simp only [fun x => ih x τ j h n]
      simp
  | neg p hp => intro a b Q Δ τ j h n; exact hp τ j h (!n)
  | conj p q hp hq =>
      intro a b Q Δ τ j h n
      change ((substituteFirstOrder p τ).occurs n j || (substituteFirstOrder q τ).occurs n j) = false
      rw [hp τ j h, hq τ j h]
      rfl
  | ex bound p hp =>
      intro a b Q Δ τ j h n
      apply hp _ j
      intro i z
      exact Fin.cases rfl
        (fun x => ((τ x).occurs_renameObjects _ z j).trans (h x z)) i

/-- Preserve one free set coordinate exactly when set replacements preserve
that coordinate and element replacements do not mention it. This is the
capture-avoidance invariant used at every fixed-point binder. -/
theorem Pattern.occurs_substitute_coordinate {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {Δ : Fin b → S}
      (σ : ∀ i, Pattern A Q Δ (P i)) (τ : ∀ i, Pattern A Q Δ (Γ i))
      (i : Fin r) (j : Fin a),
      (∀ x n, (σ x).occurs n j = (!n && i == x)) →
      (∀ x n, (τ x).occurs n j = false) → ∀ n,
      (p.substitute σ τ).occurs n j = p.occurs n i := by
  induction p with
  | base p =>
      intro a b Q Δ σ τ i j hs ht n
      exact substituteFirstOrder_occurs_absent p τ j ht n
  | setvar x => intro a b Q Δ σ τ i j hs ht n; exact hs x n
  | app op args ih =>
      intro a b Q Δ σ τ i j hs ht n
      change (List.finRange _).any (fun x => ((args x).substitute σ τ).occurs n j) = _
      simp only [fun x => ih x σ τ i j hs ht n]
      rfl
  | neg p hp => intro a b Q Δ σ τ i j hs ht n; exact hp σ τ i j hs ht (!n)
  | conj p q hp hq =>
      intro a b Q Δ σ τ i j hs ht n
      exact congrArg₂ Bool.or (hp σ τ i j hs ht n) (hq σ τ i j hs ht n)
  | ex bound p hp =>
      intro a b Q Δ σ τ i j hs ht n
      apply hp _ _ i j
      · intro x z
        exact ((σ x).occurs_renameObjects _ z j).trans (hs x z)
      · intro x z
        exact Fin.cases rfl
          (fun y => ((τ y).occurs_renameObjects _ z j).trans (ht y z)) x
  | mu p hp =>
      intro a b Q Δ σ τ i j hs ht n
      apply hp _ _ i.succ j.succ
      · intro x z
        refine Fin.cases ?_ (fun y => ?_) x
        · change (!z && j.succ == (0 : Fin (a+1))) = (!z && i.succ == (0 : Fin _))
          apply Bool.eq_iff_iff.mpr
          simp
        · change ((σ y).renameSets _).occurs z j.succ = (!z && i.succ == y.succ)
          have hb : (i.succ == y.succ) = (i == y) := by
            apply Bool.eq_iff_iff.mpr
            simp
          rw [hb]
          exact ((σ y).occurs_shiftSets_succ z j).trans (hs y z)
      · intro x z
        exact ((τ x).occurs_shiftSets_succ z j).trans (ht x z)
  | nu p hp =>
      intro a b Q Δ σ τ i j hs ht n
      apply hp _ _ i.succ j.succ
      · intro x z
        refine Fin.cases ?_ (fun y => ?_) x
        · change (!z && j.succ == (0 : Fin (a+1))) = (!z && i.succ == (0 : Fin _))
          apply Bool.eq_iff_iff.mpr
          simp
        · change ((σ y).renameSets _).occurs z j.succ = (!z && i.succ == y.succ)
          have hb : (i.succ == y.succ) = (i == y) := by
            apply Bool.eq_iff_iff.mpr
            simp
          rw [hb]
          exact ((σ y).occurs_shiftSets_succ z j).trans (hs y z)
      · intro x z
        exact ((τ x).occurs_shiftSets_succ z j).trans (ht x z)

theorem substituteFirstOrder_admissible {A : Signature S} {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {Δ : Fin b → S}
      (τ : ∀ i, Pattern A Q Δ (Γ i)),
      (∀ i, (τ i).admissible = true) →
      (substituteFirstOrder p τ).admissible = true := by
  induction p with
  | var i => intro a b Q Δ τ h; exact h i
  | app op args ih =>
      intro a b Q Δ τ h
      change (List.finRange _).all (fun i => (substituteFirstOrder (args i) τ).admissible) = true
      simp only [fun x => ih x τ h]
      simp
  | neg p hp => intro a b Q Δ τ h; exact hp τ h
  | conj p q hp hq =>
      intro a b Q Δ τ h
      change ((substituteFirstOrder p τ).admissible && (substituteFirstOrder q τ).admissible) = true
      rw [hp τ h, hq τ h]
      rfl
  | ex bound p hp =>
      intro a b Q Δ τ h
      apply hp
      intro i
      exact Fin.cases rfl
        (fun x => ((τ x).admissible_renameObjects _).trans (h x)) i

/-- Admitted replacements preserve local positivity under simultaneous
capture-avoiding substitution. Their free set polarity is unrestricted. -/
theorem Pattern.admissible_substitute {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {Δ : Fin b → S}
      (σ : ∀ i, Pattern A Q Δ (P i)) (τ : ∀ i, Pattern A Q Δ (Γ i)),
      p.admissible = true →
      (∀ i, (σ i).admissible = true) →
      (∀ i, (τ i).admissible = true) →
      (p.substitute σ τ).admissible = true := by
  induction p with
  | base p => intro a b Q Δ σ τ h hs ht; exact substituteFirstOrder_admissible p τ ht
  | setvar i => intro a b Q Δ σ τ h hs ht; exact hs i
  | app op args ih =>
      intro a b Q Δ σ τ h hs ht
      change (List.finRange _).all (fun i => ((args i).substitute σ τ).admissible) = true
      apply List.all_eq_true.mpr
      intro i hi
      exact ih i σ τ (List.all_eq_true.mp h i hi) hs ht
  | neg p hp => intro a b Q Δ σ τ h hs ht; exact hp σ τ h hs ht
  | conj p q hp hq =>
      intro a b Q Δ σ τ h hs ht
      change ((p.substitute σ τ).admissible && (q.substitute σ τ).admissible) = true
      exact Bool.and_eq_true_iff.mpr
        ⟨hp σ τ (Bool.and_eq_true_iff.mp h).1 hs ht,
          hq σ τ (Bool.and_eq_true_iff.mp h).2 hs ht⟩
  | ex bound p hp =>
      intro a b Q Δ σ τ h hs ht
      apply hp _ _ h
      · intro i
        exact ((σ i).admissible_renameObjects _).trans (hs i)
      · intro i
        exact Fin.cases rfl
          (fun x => ((τ x).admissible_renameObjects _).trans (ht x)) i
  | @mu r k P' Γ p hp =>
      intro a b Q Δ σ τ h hs ht
      change ((p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).admissible &&
        !(p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).occurs true 0) = true
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply hp _ _ (Bool.and_eq_true_iff.mp h).1
        · intro i
          exact Fin.cases rfl
            (fun x => ((σ x).admissible_renameSets _).trans (hs x)) i
        · intro i
          exact ((τ i).admissible_renameSets _).trans (ht i)
      · rw [p.occurs_substitute_coordinate _ _ 0 0
          (fun x z => Fin.cases rfl
            (fun y => by
              change ((σ y).renameSets _).occurs z 0 = (!z && 0 == y.succ)
              have hb : ((0 : Fin _) == y.succ) = false :=
                beq_eq_false_iff_ne.mpr (Ne.symm (Fin.succ_ne_zero y))
              rw [hb, Bool.and_false]
              exact (σ y).occurs_shiftSets_zero z) x)
          (fun x z => (τ x).occurs_shiftSets_zero z)]
        exact (Bool.and_eq_true_iff.mp h).2
  | @nu r k P' Γ p hp =>
      intro a b Q Δ σ τ h hs ht
      change ((p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).admissible &&
        !(p.substitute
          (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))))
          (fun i => (τ i).renameSets (Ren.shift Q (P' 0)))).occurs true 0) = true
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply hp _ _ (Bool.and_eq_true_iff.mp h).1
        · intro i
          exact Fin.cases rfl
            (fun x => ((σ x).admissible_renameSets _).trans (hs x)) i
        · intro i
          exact ((τ i).admissible_renameSets _).trans (ht i)
      · rw [p.occurs_substitute_coordinate _ _ 0 0
          (fun x z => Fin.cases rfl
            (fun y => by
              change ((σ y).renameSets _).occurs z 0 = (!z && 0 == y.succ)
              have hb : ((0 : Fin _) == y.succ) = false :=
                beq_eq_false_iff_ne.mpr (Ne.symm (Fin.succ_ne_zero y))
              rw [hb, Bool.and_false]
              exact (σ y).occurs_shiftSets_zero z) x)
          (fun x z => (τ x).occurs_shiftSets_zero z)]
        exact (Bool.and_eq_true_iff.mp h).2

end Silmaril.Logic.Matching.GeneralFixedPoint
