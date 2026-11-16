module

public import Silmaril.Logic.Matching.GeneralFixedPoint.SetObjects.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

/-- Singleton embedding recovers the existing first-order interpretation. -/
theorem denoteFirstOrderSets_singleton (M : Model A) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ (v : ObjEnv A M Γ),
      denoteFirstOrderSets M p (fun i => {v i}) = M.denote v p := by
  induction p with
  | var i => intro v; rfl
  | app op args ih =>
      intro v
      change FixedPoint.application M op
        (fun i => denoteFirstOrderSets M (args i) (fun j => {v j})) = _
      simp only [ih]
      rfl
  | neg p hp => intro v; exact congrArg (fun X => Xᶜ) (hp v)
  | conj p q hp hq => intro v; exact congrArg₂ Set.inter (hp v) (hq v)
  | @ex k Γ s bound p hp =>
      intro v
      have singleton (a : M.carrier bound) :
          (@Fin.cases k (fun i => Set (M.carrier (@Fin.cases k (fun _ => S) bound Γ i))) {a} (fun i => {v i})) =
            (fun i => {(@Fin.cases k (fun i => M.carrier (@Fin.cases k (fun _ => S) bound Γ i)) a v) i}) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      change {x | ∃ a : M.carrier bound,
        x ∈ denoteFirstOrderSets M p (Fin.cases {a} (fun i => {v i}))} = _
      simp only [singleton, hp]
      rfl

/-- The auxiliary alias-formal semantics agrees with ordinary element semantics
on singleton element environments, including both fixed-point constructors. -/
theorem Pattern.denoteSetObjects_singleton (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ (v : ObjEnv A M Γ) (η : SetEnv A M P),
      p.denoteSetObjects M (fun i => {v i}) η = p.denote M v η := by
  induction p with
  | base p => intro v η; exact denoteFirstOrderSets_singleton M p v
  | setvar i => intro v η; rfl
  | app op args ih =>
      intro v η
      change FixedPoint.application M op
        (fun i => (args i).denoteSetObjects M (fun j => {v j}) η) = _
      simp only [ih]
      rfl
  | neg p hp => intro v η; exact congrArg (fun X => Xᶜ) (hp v η)
  | conj p q hp hq => intro v η; exact congrArg₂ Set.inter (hp v η) (hq v η)
  | @ex r k P Γ s bound p hp =>
      intro v η
      have singleton (a : M.carrier bound) :
          (@Fin.cases k (fun i => Set (M.carrier (@Fin.cases k (fun _ => S) bound Γ i))) {a} (fun i => {v i})) =
            (fun i => {(@Fin.cases k (fun i => M.carrier (@Fin.cases k (fun _ => S) bound Γ i)) a v) i}) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      change {x | ∃ a : M.carrier bound,
        x ∈ p.denoteSetObjects M (Fin.cases {a} (fun i => {v i})) η} = _
      simp only [singleton, hp]
      rfl
  | mu p hp =>
      intro v η
      change sInf {X | p.denoteSetObjects M (fun i => {v i}) (Fin.cases X η) ⊆ X} = _
      simp only [hp]
      rfl
  | nu p hp =>
      intro v η
      change sSup {X | X ⊆ p.denoteSetObjects M (fun i => {v i}) (Fin.cases X η)} = _
      simp only [hp]
      rfl

end Silmaril.Logic.Matching.GeneralFixedPoint
