module

public import Silmaril.Logic.Consequence.Gentzen.Translate.Defs
import Silmaril.Proofs.Logic.Consequence.Gentzen.Translate

/-!
# Translations of Gentzen calculi: closure transport and signed lifts

* `Rules.Hom.default`, `Rules.Hom.sublist`: every formula map respects the default rules and the
  ordered (`Sublist`) policy. An arbitrary weakening policy needs its own `Rules.Hom` proof.
* `closed_pullback`: a calculus closed under `rs'` pulls back along a rule-respecting map to one
  closed under `rs` (for signed formulas: `closed_posPartAlong`, `closed_posPart`).
* `derives_map`, `ofMapDerives`: derivations map forward along a rule-respecting map, as a core
  `Translation` between the closures.
* `pullback_valid`: pulling semantic validity back along `f` is validity of the composite
  satisfaction.
* Signed lifts: `posPart_signedLift` (the positive part of the lift is the original relation,
  with order and multiplicity kept: `posAtoms_map_pos`, `negAtoms_map_pos`),
  `signedLift_valid` (the lift of validity is validity of signed literals, `signedSat`), and
  `closed_signedLift` (lifts of calculi closed under the default rules are closed).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v w

variable {C : Type u} {D : Type v}

theorem Rules.Hom.default (f : C → D) : Rules.Hom f defaultRules defaultRules :=
  ⟨id, fun _ _ h => List.map_subset f h, id⟩

theorem Rules.Hom.sublist (f : C → D) :
    Rules.Hom f (withWeakening List.Sublist) (withWeakening List.Sublist) :=
  ⟨id, fun _ _ h => h.map f, id⟩

theorem closed_pullback {f : C → D} {rs : Rules C} {rs' : Rules D} (h : rs.Hom f rs')
    {T : Seq D} (hT : Closed rs' T) :
    Closed rs (System.pullback (List.map f) (List.map f) T) :=
  Proofs.Logic.Consequence.Gentzen.Translate.closed_pullback h hT

theorem derives_map {f : C → D} {rs : Rules C} {rs' : Rules D} (h : rs.Hom f rs') {S : Seq C}
    {T : Seq D} (hST : S ≤ System.pullback (List.map f) (List.map f) T) :
    Derives rs S ≤ System.pullback (List.map f) (List.map f) (Derives rs' T) :=
  derives_le (hST.trans fun _ _ h => .base h) (closed_pullback h (derives_closed rs' T))

/-- A map of base relations extends to a translation of their closures. -/
def ofMapDerives {f : C → D} {rs : Rules C} {rs' : Rules D} (h : rs.Hom f rs') {S : Seq C}
    {T : Seq D} (hST : S ≤ System.pullback (List.map f) (List.map f) T) :
    Translation (Derives rs S) (Derives rs' T) :=
  ofMap f (derives_map h hST)

theorem pullback_valid {M : Type w} (f : C → D) (sat : M → D → Prop) :
    System.pullback (List.map f) (List.map f) (Valid sat) = Valid fun m c => sat m (f c) := by
  funext Γ Δ; simp [System.pullback, Valid, Refutation.SatAll]

/-! ## Signed formulas -/

variable {A : Type u}

theorem closed_posPartAlong {e : A → C} {T : Seq C} (hT : Closed defaultRules T) :
    Closed defaultRules (MultiSystem.posPartAlong e T) :=
  closed_pullback (Rules.Hom.default e) hT

theorem closed_posPart {T : Seq (Signed A)} (hT : Closed defaultRules T) :
    Closed defaultRules (MultiSystem.posPart T) :=
  closed_posPartAlong hT

theorem mem_posAtoms {a : A} {Γ : List (Signed A)} : a ∈ posAtoms Γ ↔ Signed.pos a ∈ Γ :=
  Proofs.Logic.Consequence.Gentzen.Translate.mem_posAtoms

theorem mem_negAtoms {a : A} {Γ : List (Signed A)} : a ∈ negAtoms Γ ↔ Signed.neg a ∈ Γ :=
  Proofs.Logic.Consequence.Gentzen.Translate.mem_negAtoms

theorem posAtoms_map_pos (Γ : List A) : posAtoms (Γ.map Signed.pos) = Γ :=
  Proofs.Logic.Consequence.Gentzen.Translate.posAtoms_map_pos Γ

theorem negAtoms_map_pos (Γ : List A) : negAtoms (Γ.map Signed.pos) = [] :=
  Proofs.Logic.Consequence.Gentzen.Translate.negAtoms_map_pos Γ

/-- The positive part of a signed lift is the original relation, exactly (no reordering). -/
theorem posPart_signedLift (S : Seq A) : MultiSystem.posPart (signedLift S) = S := by
  funext Γ Δ
  simp [MultiSystem.posPart, MultiSystem.posPartAlong, System.pullback, signedLift,
    posAtoms_map_pos, negAtoms_map_pos]

theorem signedLift_valid {M : Type w} (τ : M → A → Prop) :
    signedLift (Valid τ) = Valid (signedSat τ) :=
  Proofs.Logic.Consequence.Gentzen.Translate.signedLift_valid τ

theorem closed_signedLift {S : Seq A} (hS : Closed defaultRules S) :
    Closed defaultRules (signedLift S) :=
  Proofs.Logic.Consequence.Gentzen.Translate.closed_signedLift hS

end Silmaril.Consequence.Gentzen
