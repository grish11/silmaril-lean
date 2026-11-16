module

public import Silmaril.Logic.Consequence.Structural.Witness.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Structural.Witness.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Structural.Witness

open Silmaril.Consequence.Structural

universe u v w x

variable {C : Type u} {rs : Rules C} {W : List C → C → Type v} {V : List C → C → Type w}
  {U : List C → C → Type x}

theorem erase {Γ : List C} {c : C} :
    WDerives rs W Γ c → Derives rs (fun Γ c => Nonempty (W Γ c)) Γ c
  | .base w => .base ⟨w⟩
  | .refl h hc => .refl h hc
  | .weak h d => .weak h (erase d)
  | .cut ps h ds d => .cut ps h (fun p hp => erase (ds p hp)) (erase d)

theorem unerase {Γ : List C} {c : C} (h : Derives rs (fun Γ c => Nonempty (W Γ c)) Γ c) :
    Nonempty (WDerives rs W Γ c) := by
  induction h with
  | base h => exact h.map .base
  | refl h hc => exact ⟨.refl h hc⟩
  | weak hw _ ih => exact ih.map (.weak hw)
  | cut ps h _ _ ihs ih =>
    exact ⟨.cut ps h (fun p hp => (ihs p hp).some) ih.some⟩

theorem bind_base_eq {Γ : List C} {c : C} (d : WDerives rs W Γ c) : d.bind .base = d := by
  induction d with
  | base => rfl
  | refl => rfl
  | weak _ _ ih => exact congrArg _ ih
  | cut ps h ds d ihs ih => simp only [WDerives.bind, ih, ihs]

theorem bind_bind (f : ∀ {Γ c}, W Γ c → WDerives rs V Γ c)
    (g : ∀ {Γ c}, V Γ c → WDerives rs U Γ c) {Γ : List C} {c : C} (d : WDerives rs W Γ c) :
    (d.bind f).bind g = d.bind fun w => (f w).bind g := by
  induction d with
  | base => rfl
  | refl => rfl
  | weak _ _ ih => exact congrArg _ ih
  | cut ps h ds d ihs ih => simp only [WDerives.bind, ih, ihs]

end Silmaril.Proofs.Logic.Consequence.Structural.Witness
