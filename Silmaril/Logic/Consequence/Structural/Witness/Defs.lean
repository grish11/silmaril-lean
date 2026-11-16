module

public import Silmaril.Logic.Consequence.Structural.Defs

/-!
# Witness-carrying structural derivations

`W : List C → C → Type v` carries evidence for `Γ ⊢ c` (a certificate, a proof term, an
execution trace). `WDerives rs W Γ c` is the `Type` of derivation trees whose leaves are
witnesses `W Γ' c'` or the selected structural rules, constructor for constructor the same as
the proof-irrelevant `Derives rs` (`Silmaril.Logic.Consequence.Structural.Defs`).

* `erase`: forgetting the tree. `Nonempty (WDerives rs W Γ c) ↔ Derives rs (fun Γ c =>
  Nonempty (W Γ c)) Γ c` (`nonempty_iff`, in `Silmaril.Logic.Consequence.Structural.Witness.Thms`).
* `bind` (substitution of derivations for leaves), the unit `base` and `flatten := bind id`
  satisfy the monad laws (`…Witness.Thms`): `bind_base` (left unit, definitional),
  `bind_base_eq` (right unit), `bind_bind` (associativity), hence `flatten_base`,
  `flatten_map_base`, `flatten_flatten`.
* Proof-relevant idempotence is **not** claimed: `flatten : WDerives rs (WDerives rs W) →
  WDerives rs W` is a retraction of `base` but not an equivalence (a leaf holding a `refl` tree
  and a `refl` node flatten to the same tree: `flatten_not_injective`). Only the erased closure is idempotent
  (`derives_derives`).
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u v w x

variable {C : Type u}

/-- Derivation trees from witnesses `W` with the selected structural rules. -/
inductive WDerives (rs : Rules C) (W : List C → C → Type v) : List C → C → Type (max u v)
  | base {Γ c} : W Γ c → WDerives rs W Γ c
  | refl {Γ c} : rs.refl → c ∈ Γ → WDerives rs W Γ c
  | weak {Γ Δ c} : rs.weak Γ Δ → WDerives rs W Γ c → WDerives rs W Δ c
  | cut (ps : List (List C × C)) {c} : rs.cut → (∀ p ∈ ps, WDerives rs W p.1 p.2) →
      WDerives rs W (ps.map Prod.snd) c → WDerives rs W (ps.flatMap Prod.fst) c

namespace WDerives

variable {rs : Rules C} {W : List C → C → Type v} {V : List C → C → Type w}
  {U : List C → C → Type x}

/-- Substitute a derivation for every leaf. -/
def bind (f : ∀ {Γ c}, W Γ c → WDerives rs V Γ c) {Γ : List C} {c : C} :
    WDerives rs W Γ c → WDerives rs V Γ c
  | base w => f w
  | refl h hc => refl h hc
  | weak h d => weak h (d.bind f)
  | cut ps h ds d => cut ps h (fun p hp => (ds p hp).bind f) (d.bind f)

/-- Relabel the leaves. -/
def map (f : ∀ {Γ c}, W Γ c → V Γ c) {Γ : List C} {c : C} (d : WDerives rs W Γ c) :
    WDerives rs V Γ c :=
  d.bind fun w => base (f w)

/-- Graft derivations held at the leaves. -/
def flatten {Γ : List C} {c : C} (d : WDerives rs (WDerives rs W) Γ c) : WDerives rs W Γ c :=
  d.bind id

end WDerives

end Silmaril.Consequence.Structural
