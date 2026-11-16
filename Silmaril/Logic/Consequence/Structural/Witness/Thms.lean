module

public import Silmaril.Logic.Consequence.Structural.Witness.Defs
import Silmaril.Proofs.Logic.Consequence.Structural.Witness

/-!
# Witness-carrying derivations: erasure and the substitution laws

* `erase`, `nonempty_iff`: a witness derivation exists iff the erased relation `Nonempty ∘ W`
  derives the sequent; `derives_iff_nonempty`: `Derives rs R` is inhabited derivations over the
  proof witnesses `PLift (R Γ c)`.
* Monad laws for `bind`/`base`: `bind_base`, `bind_base_eq`, `bind_bind`; and for `flatten`:
  `flatten_base`, `flatten_map_base`, `flatten_flatten`.
* `flatten_not_injective`: flattening is not an equivalence as soon as reflexivity is selected
  and some premise is available, so the closure is not idempotent proof-relevantly.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u v w x

variable {C : Type u} {rs : Rules C} {W : List C → C → Type v} {V : List C → C → Type w}
  {U : List C → C → Type x}

namespace WDerives

/-- Forget the tree, keeping only that each leaf is inhabited. -/
theorem erase {Γ : List C} {c : C} (d : WDerives rs W Γ c) :
    Derives rs (fun Γ c => Nonempty (W Γ c)) Γ c :=
  Proofs.Logic.Consequence.Structural.Witness.erase d

theorem nonempty_iff {Γ : List C} {c : C} :
    Nonempty (WDerives rs W Γ c) ↔ Derives rs (fun Γ c => Nonempty (W Γ c)) Γ c :=
  ⟨fun ⟨d⟩ => d.erase, Proofs.Logic.Consequence.Structural.Witness.unerase⟩

/-- Left unit (definitional). -/
theorem bind_base (f : ∀ {Γ c}, W Γ c → WDerives rs V Γ c) {Γ : List C} {c : C} (w : W Γ c) :
    (base w : WDerives rs W Γ c).bind f = f w := rfl

/-- Right unit. -/
theorem bind_base_eq {Γ : List C} {c : C} (d : WDerives rs W Γ c) : d.bind base = d :=
  Proofs.Logic.Consequence.Structural.Witness.bind_base_eq d

/-- Associativity of substitution. -/
theorem bind_bind (f : ∀ {Γ c}, W Γ c → WDerives rs V Γ c)
    (g : ∀ {Γ c}, V Γ c → WDerives rs U Γ c) {Γ : List C} {c : C} (d : WDerives rs W Γ c) :
    (d.bind f).bind g = d.bind fun w => (f w).bind g :=
  Proofs.Logic.Consequence.Structural.Witness.bind_bind f g d

theorem flatten_base {Γ : List C} {c : C} (d : WDerives rs W Γ c) : flatten (base d) = d := rfl

theorem flatten_map_base {Γ : List C} {c : C} (d : WDerives rs W Γ c) :
    flatten (d.map base) = d := by
  simp only [flatten, map, bind_bind]; exact bind_base_eq d

theorem flatten_flatten {Γ : List C} {c : C}
    (d : WDerives rs (WDerives rs (WDerives rs W)) Γ c) :
    flatten (flatten d) = flatten (d.map flatten) := by
  simp only [flatten, map, bind_bind]; rfl

/-- A `refl` node and a leaf holding a `refl` tree flatten to the same tree. -/
theorem flatten_not_injective (h : rs.refl) {Γ : List C} {c : C} (hc : c ∈ Γ) :
    ¬ Function.Injective (flatten : WDerives rs (WDerives rs W) Γ c → WDerives rs W Γ c) :=
  fun hi => nomatch @hi (base (refl h hc)) (refl h hc) rfl

end WDerives

/-- `Derives` is inhabitation of derivations whose leaves are proofs of `R`. -/
theorem derives_iff_nonempty {R : Rel C} {Γ : List C} {c : C} :
    Derives rs R Γ c ↔ Nonempty (WDerives rs (fun Γ c => PLift (R Γ c)) Γ c) := by
  rw [WDerives.nonempty_iff]
  exact Iff.of_eq (by congr; funext Γ c; exact propext ⟨fun h => ⟨⟨h⟩⟩, fun ⟨h⟩ => h.down⟩)

end Silmaril.Consequence.Structural
