module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Thms

/-! Alias parameters are pattern placeholders. An element-named formal may be
instantiated by a pattern denoting an arbitrary set. This auxiliary semantics
interprets those placeholders by sets, while actual element quantifiers still
range over carrier elements and install singleton values. Ordinary element
valuations are recovered by singleton embedding; they are not redefined. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

abbrev SetObjEnv (M : Model A) {k : Nat} (Γ : Fin k → S) :=
  ∀ i, Set (M.carrier (Γ i))

def denoteFirstOrderSets (M : Model A) {k : Nat} {Γ : Fin k → S} {s : S}
    (p : FirstOrder.Pattern A Γ s) : SetObjEnv M Γ → Set (M.carrier s) := by
  induction p with
  | var i => exact fun ρ => ρ i
  | app op args ih => exact fun ρ => FixedPoint.application M op (fun i => ih i ρ)
  | neg p hp => exact fun ρ => (hp ρ)ᶜ
  | conj p q hp hq => exact fun ρ => hp ρ ∩ hq ρ
  | ex bound p hp => exact fun ρ => {x | ∃ a : M.carrier bound, x ∈ hp (Fin.cases {a} ρ)}

/-- Direct set-valued formal interpretation, not interpretation of an expanded
pattern. Both fixed points use their actual pre/postfixed-set definitions. -/
def Pattern.denoteSetObjects (M : Model A) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    SetObjEnv M Γ → SetEnv A M P → Set (M.carrier s) := by
  induction p with
  | base p => exact fun ρ _ => denoteFirstOrderSets M p ρ
  | setvar i => exact fun _ η => η i
  | app op args ih => exact fun ρ η => FixedPoint.application M op (fun i => ih i ρ η)
  | neg p hp => exact fun ρ η => (hp ρ η)ᶜ
  | conj p q hp hq => exact fun ρ η => hp ρ η ∩ hq ρ η
  | ex bound p hp => exact fun ρ η => {x | ∃ a : M.carrier bound, x ∈ hp (Fin.cases {a} ρ) η}
  | mu p hp => exact fun ρ η => sInf {X | hp ρ (Fin.cases X η) ⊆ X}
  | nu p hp => exact fun ρ η => sSup {X | X ⊆ hp ρ (Fin.cases X η)}

end Silmaril.Logic.Matching.GeneralFixedPoint
