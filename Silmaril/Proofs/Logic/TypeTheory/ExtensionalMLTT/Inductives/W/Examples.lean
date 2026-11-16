module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last


private theorem extend {Γ : Ctx} {x : String} {A : Tm 0}
    (hΓ : Γ.JEq .unit .star .star) (hx : x ∉ Γ.dv) (hA : Γ.JEq (.univ 0) A A) :
    (Γ.cons x A).JEq .unit .star .star := .cons_ok hΓ hx hA

/-- Formation is derivable in every well-formed context. -/
theorem leaf_formation {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.univ 0) Leaf Leaf := by
  apply Ctx.JEqH.wtype (L := Γ.dv) (.unit hΓ)
  intro x hx
  simpa only [Tm.open] using Ctx.JEqH.empty (n := 0) (extend hΓ hx (.unit hΓ))

private theorem unit_family {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEq .unit .star .star) (hA : Γ.JEq (.univ 0) A A) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEq (.univ 0) .unit .unit :=
  fun _ hx => .unit (extend hΓ hx hA)

private theorem empty_family {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEq .unit .star .star) (hA : Γ.JEq (.univ 0) A A) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEq (.univ 0) .empty .empty :=
  fun _ hx => .empty (extend hΓ hx hA)

private theorem leaf_family {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEq .unit .star .star) (hA : Γ.JEq (.univ 0) A A) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEq (.univ 0) Leaf Leaf :=
  fun _ hx => leaf_formation (extend hΓ hx hA)

/-- The empty child map is typed using empty elimination into the W-type. -/
theorem noChildren_typing {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.arr .empty Leaf) noChildren noChildren := by
  apply Ctx.JEqH.abs (L := Γ.dv) (.empty hΓ) (by simpa [Leaf, Tm.wk0, Tm.wkn, Tm.open, lastCases_zero] using leaf_family hΓ (.empty hΓ))
  intro x hx
  simpa [Leaf, Tm.wk0, Tm.wkn, Tm.open, lastCases_zero] using
    Ctx.JEqH.absurd (leaf_formation (extend hΓ hx (.empty hΓ)))
      (.var (extend hΓ hx (.empty hΓ)) (.here Γ x .empty))

/-- The nullary constructor gives a closed inhabitant, so formation is nonvacuous. -/
theorem leaf_typing {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq Leaf leaf leaf :=
  .sup (.unit hΓ) (by simpa [Tm.open] using empty_family hΓ (.unit hΓ)) hΓ
    (by simpa [Tm.lst, Leaf] using noChildren_typing hΓ)

private theorem child_type {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.univ 0) (.pi .empty Leaf) (.pi .empty Leaf) := by
  apply Ctx.JEqH.pi (L := Γ.dv) (.empty hΓ)
  intro x hx
  simpa [Leaf, Tm.open] using leaf_formation (extend hΓ hx (.empty hΓ))

private theorem results_type {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.univ 0) (.pi .empty .unit) (.pi .empty .unit) := by
  apply Ctx.JEqH.pi (L := Γ.dv) (.empty hΓ)
  intro x hx
  simpa only [Tm.open] using Ctx.JEqH.unit (n := 0) (extend hΓ hx (.empty hΓ))

private theorem inner_type {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.univ 0) (.pi (.pi .empty .unit) .unit) (.pi (.pi .empty .unit) .unit) := by
  apply Ctx.JEqH.pi (L := Γ.dv) (results_type hΓ)
  intro x hx
  simpa only [Tm.open] using Ctx.JEqH.unit (n := 0) (extend hΓ hx (results_type hΓ))

private theorem body_type {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.univ 0) (.pi (.pi .empty Leaf) (.pi (.pi .empty .unit) .unit))
      (.pi (.pi .empty Leaf) (.pi (.pi .empty .unit) .unit)) := by
  apply Ctx.JEqH.pi (L := Γ.dv) (child_type hΓ)
  intro x hx
  simpa only [Tm.open] using inner_type (extend hΓ hx (child_type hΓ))

private theorem inner_typing {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.pi (.pi .empty .unit) .unit) (.abs (.pi .empty .unit) .star)
      (.abs (.pi .empty .unit) .star) := by
  apply Ctx.JEqH.abs (L := Γ.dv) (results_type hΓ)
  · intro x hx
    simpa only [Tm.open] using Ctx.JEqH.unit (n := 0) (extend hΓ hx (results_type hΓ))
  · intro x hx
    simpa only [Tm.open] using extend hΓ hx (results_type hΓ)

private theorem body_typing {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (.pi (.pi .empty Leaf) (.pi (.pi .empty .unit) .unit))
      (.abs (.pi .empty Leaf) (.abs (.pi .empty .unit) .star))
      (.abs (.pi .empty Leaf) (.abs (.pi .empty .unit) .star)) := by
  apply Ctx.JEqH.abs (L := Γ.dv) (child_type hΓ)
  · intro x hx
    simpa only [Tm.open] using inner_type (extend hΓ hx (child_type hΓ))
  · intro x hx
    simpa only [Tm.open] using inner_typing (extend hΓ hx (child_type hΓ))

/-- The three-argument elimination step has the actual dependent step type. -/
theorem unitStep_typing {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq (Tm.wStepType .unit .empty .unit) unitStep unitStep := by
  simp only [Tm.wStepType, Tm.bsubst, Tm.castLE]
  apply Ctx.JEqH.abs (L := Γ.dv) (.unit hΓ)
  · intro x hx
    simpa only [Tm.open, Leaf] using body_type (extend hΓ hx (.unit hΓ))
  · intro x hx
    simpa only [Tm.open, Leaf] using body_typing (extend hΓ hx (.unit hΓ))

/-- Elimination is a derived typing judgment in the empty theory. -/
theorem leaf_elimination {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq .unit (.wrec .unit .empty .unit unitStep leaf)
      (.wrec .unit .empty .unit unitStep leaf) := by
  simpa only [Tm.lst] using Ctx.JEqH.wrec (L := Γ.dv) (.unit hΓ)
    (by simpa only [Tm.open] using empty_family hΓ (.unit hΓ))
    (by simpa only [Tm.open, Leaf] using unit_family hΓ (leaf_formation hΓ)) (unitStep_typing hΓ) (leaf_typing hΓ)

/-- The W iota rule is derivable for a real closed constructor and step. -/
theorem leaf_computation {Γ : Ctx} (hΓ : Γ.JEq .unit .star .star) :
    Γ.JEq .unit (.wrec .unit .empty .unit unitStep leaf)
      (.app (.app (.app unitStep .star) noChildren)
        (Tm.recChildren .unit .empty .unit unitStep .star noChildren)) := by
  simpa only [Tm.lst, leaf] using Ctx.JEqH.beta_wrec (L := Γ.dv) (.unit hΓ)
    (by simpa only [Tm.open] using empty_family hΓ (.unit hΓ))
    (by simpa only [Tm.open, Leaf] using unit_family hΓ (leaf_formation hΓ)) (unitStep_typing hΓ) hΓ
    (by simpa only [Tm.lst, Leaf] using noChildren_typing hΓ)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples
