module

public import Silmaril.Logic.Consequence.Gentzen.Core.Thms
public import Silmaril.Logic.Consequence.Translation.Defs

/-!
# Translations of Gentzen calculi along formula maps, and signed lifts

A formula map `f : C → D` acts on sequents by `List.map f` on both sides; the pullback of a
`T : Seq D` along it is core `System.pullback (List.map f) (List.map f) T` (for an embedding of
atoms into signed formulas this is core `MultiSystem.posPartAlong`).

* `Rules.Hom f rs rs'`: `f` respects the selected rules: each rule of `rs` is one of `rs'`, and
  `rs`-weakening is mapped by `List.map f` into `rs'`-weakening. Closedness pulls back along such
  maps and derivations map forward (`…Translate.Thms`). `Rules.Hom.default` (any `f`, ordinary
  `⊆`-weakening) and `Rules.Hom.sublist` (any `f`, ordered `Sublist`-weakening) are the instances
  available without hypotheses.
* `ofMap f h : Translation S T`, the core translation acting by `List.map f` on both sides.
* Signed lifts: `posAtoms Γ` and `negAtoms Γ` list the atoms of positive and negative members of
  `Γ`, in order and with multiplicity. `signedLift S` reads a signed sequent `Γ ⊢ Δ` as
  `posAtoms Γ ++ negAtoms Δ ⊢ posAtoms Δ ++ negAtoms Γ` (negative literals change sides).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u} {D : Type v}

/-- `f` maps the rules `rs` into `rs'`. -/
structure Rules.Hom (f : C → D) (rs : Rules C) (rs' : Rules D) : Prop where
  refl : rs.refl → rs'.refl
  weak : ∀ ⦃Γ Δ⦄, rs.weak Γ Δ → rs'.weak (Γ.map f) (Δ.map f)
  cut : rs.cut → rs'.cut

/-- The translation acting by `List.map f` on both sides. -/
def ofMap {S : Seq C} {T : Seq D} (f : C → D) (h : ∀ Γ Δ, S Γ Δ → T (Γ.map f) (Δ.map f)) :
    Translation S T :=
  ⟨List.map f, List.map f, h⟩

/-- Atoms of the positive members, in order. -/
def posAtoms {A : Type u} : List (Signed A) → List A :=
  List.filterMap fun | .pos a => some a | .neg _ => none

/-- Atoms of the negative members, in order. -/
def negAtoms {A : Type u} : List (Signed A) → List A :=
  List.filterMap fun | .pos _ => none | .neg a => some a

/-- A sequent relation on atoms, lifted to signed literals: negative literals change sides. -/
def signedLift {A : Type u} (S : Seq A) : Seq (Signed A) := fun Γ Δ =>
  S (posAtoms Γ ++ negAtoms Δ) (posAtoms Δ ++ negAtoms Γ)

end Silmaril.Consequence.Gentzen
