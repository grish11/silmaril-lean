module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Examples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last


private theorem extend {Γ : Ctx} {x : String} {A : Tm 0}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) (hx : x ∉ Γ.dv) (hA : Γ.JEqB 1 ∅ (.univ 0) A A) :
    (Γ.cons x A).JEqB 1 ∅ .unit .star .star := .cons_ok (by decide) hΓ hx hA

/-- Formation is derivable in every well-formed context. -/
theorem leaf_formation {Γ : Ctx} (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ (.univ 0) Leaf Leaf := by
  apply Ctx.JEqB.wtype (L := Γ.dv) (by decide) (.unit (by decide) hΓ)
  intro x hx
  simpa only [Tm.open] using Ctx.JEqB.empty (n := 0) (by decide) (extend hΓ hx (.unit (by decide) hΓ))

private theorem unit_family {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) (hA : Γ.JEqB 1 ∅ (.univ 0) A A) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB 1 ∅ (.univ 0) .unit .unit :=
  fun _ hx => .unit (by decide) (extend hΓ hx hA)

private theorem empty_family {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) (hA : Γ.JEqB 1 ∅ (.univ 0) A A) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB 1 ∅ (.univ 0) .empty .empty :=
  fun _ hx => .empty (by decide) (extend hΓ hx hA)

private theorem leaf_family {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) (hA : Γ.JEqB 1 ∅ (.univ 0) A A) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB 1 ∅ (.univ 0) Leaf Leaf :=
  fun _ hx => leaf_formation (extend hΓ hx hA)

/-- The empty child map is typed using empty elimination into the W-type. -/
theorem noChildren_typing {Γ : Ctx} (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ (.arr .empty Leaf) noChildren noChildren := by
  apply Ctx.JEqB.abs (n := 0) (L := Γ.dv) (by decide) (.empty (by decide) hΓ) (by simpa [Leaf, Tm.wk0, Tm.wkn, Tm.open, lastCases_zero] using leaf_family hΓ (.empty (by decide) hΓ))
  intro x hx
  simpa [Leaf, Tm.wk0, Tm.wkn, Tm.open, lastCases_zero] using
    Ctx.JEqB.absurd (n := 0) (by decide) (leaf_formation (extend hΓ hx (.empty (by decide) hΓ)))
      (.var (extend hΓ hx (.empty (by decide) hΓ)) (.here Γ x .empty))

/-- The nullary constructor gives a closed inhabitant, so formation is nonvacuous. -/
theorem leaf_typing {Γ : Ctx} (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ Leaf leaf leaf :=
  .sup (n := 0) (by decide) (.unit (by decide) hΓ) (by simpa [Tm.open] using empty_family hΓ (.unit (by decide) hΓ)) hΓ
    (by simpa [Tm.lst, Leaf] using noChildren_typing hΓ)

/-- The one-universe proof budget admits an actual closed W constructor. -/
theorem leaf_closed : Ctx.JEqB 1 ∅ .nil Leaf leaf leaf := leaf_typing .nil_ok

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Examples
