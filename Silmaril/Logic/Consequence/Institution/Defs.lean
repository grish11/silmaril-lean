module

public import Silmaril.Logic.Consequence.Semantic.Defs
public import Silmaril.Logic.Consequence.Multi.Defs
public import Silmaril.Logic.Consequence.Gentzen.Defs
public import Silmaril.Logic.Institution.Metatheory.Entailment

/-!
# Institutions and logics as list-premise consequence systems

`Silmaril.Logic.Consequence.Semantic` already reads a room `R` as `Set R.Sen ⊢ R.Sen`
(`roomSys`), and `Silmaril.Logic.Consequence.Multi` reads it as `R.Sen* ⊢ R.Sen*`
(`roomMulti`). This module adds the remaining views and keeps three semantics apart.

**Model-wise (institution) semantics.** A sentence holds in a *model*.

* `roomSeq R : System (List R.Sen) R.Sen`: `Γ ⊢ φ` iff every model of all of `Γ` satisfies `φ`
  (`Refutation.Entails R.Sat`). It is `roomSys` on the finite set of members of `Γ` (`Thms`).
* `roomMulti R` (existing): `Γ ⊢ Δ` iff every model of all of `Γ` satisfies **some** member of
  `Δ`. It is `Gentzen.Valid R.Sat` (`Thms`). The succedent is read disjunctively *over models*,
  not as a disjunction formula: a room has no connectives.
* `corridorSeq f`: a corridor translates `roomSeq` (`List.map f.sen`, `f.sen`).
  `institutionSeq I σ` is that translation for an institution `I : Sign ⥤ Room` and `σ : S ⟶ S'`.

**Point-wise (local) semantics.** When sentences are formulas with free variables, a
formula holds at a *point* of a model (a valuation), and `sat : (m : Mod) → Pt m → C → Prop`.

* `localSat sat`: satisfaction at the points `Σ m, Pt m`. `Refutation.Entails (localSat sat)` and
  `Gentzen.Valid (localSat sat)` are the local single- and multiple-conclusion systems: one
  valuation must satisfy every premise and some succedent.
* `validIn sat m c`: `c` holds at every point of `m`; its systems are the global ones.

Local single-conclusion consequence implies global (`Thms`), but not conversely, and the two
multiple-conclusion systems are incomparable in general: `⊢ x, ¬x` holds locally and fails
globally (`Examples`). Every system above is closed under the structural rules
`Structural.tarskiRules` (single conclusion) or `Gentzen.defaultRules` (multiple conclusions),
because each is `Refutation.Entails` or `Gentzen.Valid` of some satisfaction.

**Syntactic entailment.** A Tarskian entailment relation (`Metatheory.ER`, over sets) gives
`ER.listSys E : System (List E.Sen) E.Sen`, and a logic (`Metatheory.LogicalSystem`, an institution
with an entailment system) gives `LogicalSystem.listSys L S` at each signature, translated along
signature morphisms (`LogicalSystem.seqTranslation`). Soundness of the logic is
`listSys L S ≤ roomSeq (L.I.obj S)` (`Thms`).
-/

@[expose] public section

namespace Silmaril.Consequence

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution

universe u v w t m₁ m₂ u' v'

/-! ## Model-wise semantics of a room -/

/-- **A room as `Sen* ⊢ Sen`**: every model of all of `Γ` satisfies `φ`. -/
def roomSeq (R : Room.{w, m₁, m₂}) : System (List R.Sen) R.Sen := Refutation.Entails R.Sat

/-- A corridor translates `roomSeq`, mapping premises and conclusion by the sentence map. -/
def corridorSeq {R₁ R₂ : Room.{w, m₁, m₂}} (f : Corridor R₁ R₂) :
    Translation (roomSeq R₁) (roomSeq R₂) :=
  ⟨List.map f.sen, f.sen, fun _ φ h M hM => (f.sat M φ).2 (h (f.mod.obj M) fun c hc =>
    (f.sat M c).1 (hM _ (List.mem_map_of_mem hc)))⟩

/-- **An institution as `Sen* ⊢ Sen` per signature**, translated along signature morphisms. -/
def institutionSeq {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})
    {S S' : Sign} (σ : S ⟶ S') : Translation (roomSeq (I.obj S)) (roomSeq (I.obj S')) :=
  corridorSeq (I.map σ)

/-! ## Point-wise (local) semantics -/

section Local

variable {Mod : Type u} {Pt : Mod → Type v} {C : Type w}

/-- Satisfaction at the points (valuations) of models. -/
def localSat (sat : (m : Mod) → Pt m → C → Prop) : (Σ m, Pt m) → C → Prop :=
  fun x c => sat x.1 x.2 c

/-- Validity in a model: satisfaction at every point. -/
def validIn (sat : (m : Mod) → Pt m → C → Prop) : Mod → C → Prop :=
  fun m c => ∀ p, sat m p c

end Local

/-! ## Syntactic entailment -/

/-- A Tarskian entailment relation on lists of premises (their members as a set). -/
def ER.listSys (E : Metatheory.ER.{w}) : System (List E.Sen) E.Sen :=
  fun Γ φ => E.Derives {x | x ∈ Γ} φ

namespace LogicalSystem

variable {Sign : Type u} [Category.{v} Sign] (L : Metatheory.LogicalSystem.{u, v, w, m₁, m₂} Sign)

/-- **A logic's derivability as `Sen* ⊢ Sen`** at a signature. -/
def listSys (S : Sign) : System (List (L.I.obj S).Sen) (L.I.obj S).Sen := ER.listSys (L.er S)

/-- Derivability is translated along signature morphisms. -/
def seqTranslation {S S' : Sign} (σ : S ⟶ S') : Translation (listSys L S) (listSys L S') :=
  ⟨List.map (L.I.map σ).sen, (L.I.map σ).sen, fun _ _ h =>
    L.mono S' (Γ := (L.I.map σ).sen '' _) (fun _ ⟨_, hy, e⟩ => e ▸ List.mem_map_of_mem hy)
      (L.map_derives σ h)⟩

end LogicalSystem

end Silmaril.Consequence
