module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Defs
public import Silmaril.Logic.Consequence.Gentzen.Calculus.Thms
public import Silmaril.Logic.Consequence.Gentzen.Translate.Thms
public import Silmaril.Logic.Consequence.Gentzen.Core.Thms
import Silmaril.Proofs.Logic.Consequence.Gentzen.Clausal

/-!
# Clausal acceptors: closure laws, roundtrips and equivalences

Every equivalence is an order isomorphism between the *closed* acceptors of two kinds, with
the closure hypothesis on each side stated in the subtype. Without closure there is no
equivalence: an arbitrary acceptor is not the restriction of any calculus
(`…Clausal.Examples`).

**UNSAT ≃ Gentzen ≃ TAUTO** (explicit `neg : C → C`, no involution assumed):

* `unsatClosed_toUnsat`, `gentzenClosed_viaUnsat`: the existing restriction `toUnsat` and
  conversion `viaUnsat` exchange `GentzenClosed neg` calculi and `UnsatClosed neg` acceptors;
  roundtrips are the existing `toUnsat_viaUnsat` and `eq_viaUnsat_toUnsat`. `unsatEquiv neg`.
* `tautClosed_toTaut`, `gentzenClosed_viaTauto`, `tautEquiv neg`, likewise for TAUTO.
* `UnsatClosed.dne`: explosion and cut absorb a double negation (`g` may be replaced by
  `neg (neg g)`); this is what `NegR` of `viaUnsat` needs, and it is derived, not assumed.

**UNSAT ≃ CNF, two layers.**

* Representation: `cnfClosed_cnfOf` (`cnfOf U` is `CnfClosed` for every `U`),
  `unitsOf_cnfOf` (needs `U` `⊆`-up-closed), `cnfOf_unitsOf` (needs `CnfClosed A`: a closed
  CNF acceptor is determined by its unit restriction through hitting sets). `cnfEquiv`:
  `⊆`-up-closed UNSAT acceptors ≃ `CnfClosed` CNF acceptors.
* Logic: `cnfUnsatClosed_iff` (`CnfUnsatClosed neg A ↔ CnfClosed A ∧ UnsatClosed neg
  (unitsOf A)`), `cnfUnsatEquiv neg`: `UnsatClosed` ≃ `CnfUnsatClosed`. `CnfClosed` alone does
  not give the logical layer (`Examples.emptyClause`).
* Composites: `gentzenCnfEquiv neg` (Gentzen calculi with negation rules ≃ CNF-UNSAT
  acceptors over `C`), `cnfOf_toUnsat` (its forward map).

**Semantics** (over any `sat : M → C → Prop`):

* `cnfUnsat_closed`: `CnfUnsat sat` is `CnfClosed`, unconditionally;
  `cnfUnsat_unsatClosed`: it is `CnfUnsatClosed neg` given `NegSound` (complementary units) and
  `NegComplete` (unit resolution).
* `unitsOf_cnfUnsat`, `cnfOf_unsat`: the unit restriction of CNF unsatisfiability is
  `Refutation.Unsat sat`, and conversely; `cnfOf_toUnsat_valid`: the CNF image of the
  validity calculus `Valid sat` is `CnfUnsat sat`.
* Soundness transfers, separately from closure: `cnfSound_cnfOf`, `checkSound_unitsOf`,
  `viaUnsat_unitsOf_le_valid`.

**Signed formulas, over `Signed A` with the sign flip.** The Gentzen side is a calculus on the
atoms `A` (the existing positive embedding `Signed.pos`), not a decomposition derived from an
involution:

* `atomSeq_signedUnsat` (every `S`, no hypothesis), `signedUnsat_atomSeq` (`U` up-closed).
* `gentzenClosed_signedLift`: the signed lift of a calculus closed under the default rules has
  both negation rules for the sign flip; so `unsatClosed_signedUnsat`, `closed_atomSeq`, and
  `signedEquiv`: calculi on `A` ≃ `UnsatClosed (-·)` acceptors on `(Signed A)*`;
  `signedCnfEquiv`: ≃ `CnfUnsatClosed (-·)` acceptors on `(Signed A)**`.
* `signedUnsat_valid`, `cnfOf_signedUnsat_valid`: validity over a valuation of atoms becomes
  `Refutation.Unsat (signedSat τ)` and `CnfUnsat (signedSat τ)`.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Clausal

open Refutation (SatAll Unsat CheckSound)

universe u v

variable {C : Type u} {neg : C → C}

/-! ## UNSAT and TAUTO acceptors against Gentzen calculi -/

theorem unsatClosed_toUnsat {S : Seq C} (h : GentzenClosed neg S) : UnsatClosed neg (toUnsat S) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.unsatClosed_toUnsat h

theorem gentzenClosed_viaUnsat {U : List C → Prop} (h : UnsatClosed neg U) :
    GentzenClosed neg (viaUnsat U neg) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.gentzenClosed_viaUnsat h

theorem UnsatClosed.dne {U : List C → Prop} (h : UnsatClosed neg U) {g : C} {X : List C}
    (hg : U (g :: X)) : U (neg (neg g) :: X) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.unsatClosed_dne h hg

theorem tautClosed_toTaut {S : Seq C} (h : GentzenClosed neg S) : TautClosed neg (toTaut S) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.tautClosed_toTaut h

theorem gentzenClosed_viaTauto {T : List C → Prop} (h : TautClosed neg T) :
    GentzenClosed neg (viaTauto T neg) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.gentzenClosed_viaTauto h

/-- Gentzen calculi with both negation rules are their UNSAT restrictions. -/
def unsatEquiv (neg : C → C) :
    {S : Seq C // GentzenClosed neg S} ≃o {U : List C → Prop // UnsatClosed neg U} where
  toFun S := ⟨toUnsat S.1, unsatClosed_toUnsat S.2⟩
  invFun U := ⟨viaUnsat U.1 neg, gentzenClosed_viaUnsat U.2⟩
  left_inv S := Subtype.ext (eq_viaUnsat_toUnsat S.2.1 S.2.2.1 S.2.2.2).symm
  right_inv U := Subtype.ext (toUnsat_viaUnsat U.1 neg)
  map_rel_iff' {S T} :=
    ⟨fun h Γ Δ hS => (iff_toUnsat T.2.1 T.2.2.1 T.2.2.2 Γ Δ).2
        (h _ ((iff_toUnsat S.2.1 S.2.2.1 S.2.2.2 Γ Δ).1 hS)),
      fun h Γ hS => h Γ [] hS⟩

/-- Gentzen calculi with both negation rules are their TAUTO restrictions. -/
def tautEquiv (neg : C → C) :
    {S : Seq C // GentzenClosed neg S} ≃o {T : List C → Prop // TautClosed neg T} where
  toFun S := ⟨toTaut S.1, tautClosed_toTaut S.2⟩
  invFun T := ⟨viaTauto T.1 neg, gentzenClosed_viaTauto T.2⟩
  left_inv S := Subtype.ext (eq_viaTauto_toTaut S.2.1 S.2.2.1 S.2.2.2).symm
  right_inv T := Subtype.ext (toTaut_viaTauto T.1 neg)
  map_rel_iff' {S T} :=
    ⟨fun h Γ Δ hS => (iff_toTaut T.2.1 T.2.2.1 T.2.2.2 Γ Δ).2
        (h _ ((iff_toTaut S.2.1 S.2.2.1 S.2.2.2 Γ Δ).1 hS)),
      fun h Δ hS => h [] Δ hS⟩

/-! ## CNF acceptors: representation layer -/

section Cnf

variable {A : List (List C) → Prop} {U : List C → Prop}

theorem hits_units {Γ Γ' : List C} : Hits Γ' (units Γ) ↔ Γ ⊆ Γ' :=
  Proofs.Logic.Consequence.Gentzen.Clausal.hits_units

theorem unitsOf_up (hA : CnfClosed A) : ListPred.UpClosed (unitsOf A) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.unitsOf_up hA

theorem cnfClosed_cnfOf (U : List C → Prop) : CnfClosed (cnfOf U) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.cnfClosed_cnfOf U

theorem unitsOf_cnfOf (hU : ListPred.UpClosed U) : unitsOf (cnfOf U) = U :=
  Proofs.Logic.Consequence.Gentzen.Clausal.unitsOf_cnfOf hU

/-- A `CnfClosed` acceptor is determined by its unit restriction. -/
theorem cnfOf_unitsOf (hA : CnfClosed A) : cnfOf (unitsOf A) = A :=
  Proofs.Logic.Consequence.Gentzen.Clausal.cnfOf_unitsOf hA

theorem cnfOf_mono {U U' : List C → Prop} (h : U ≤ U') : cnfOf U ≤ cnfOf U' :=
  fun _ hF Γ hΓ => h Γ (hF Γ hΓ)

theorem unitsOf_mono {A A' : List (List C) → Prop} (h : A ≤ A') : unitsOf A ≤ unitsOf A' :=
  fun _ hA => h _ hA

/-- `⊆`-up-closed UNSAT acceptors are representation-closed CNF acceptors. -/
def cnfEquiv (C : Type u) :
    {U : List C → Prop // ListPred.UpClosed U} ≃o {A : List (List C) → Prop // CnfClosed A} where
  toFun U := ⟨cnfOf U.1, cnfClosed_cnfOf U.1⟩
  invFun A := ⟨unitsOf A.1, unitsOf_up A.2⟩
  left_inv U := Subtype.ext (unitsOf_cnfOf U.2)
  right_inv A := Subtype.ext (cnfOf_unitsOf A.2)
  map_rel_iff' {U U'} :=
    ⟨fun h => by
        have := unitsOf_mono (A := cnfOf U.1) (A' := cnfOf U'.1) h
        rwa [unitsOf_cnfOf U.2, unitsOf_cnfOf U'.2] at this,
      fun h => cnfOf_mono h⟩

/-! ## CNF acceptors: logical layer -/

theorem cnfUnsatClosed_iff :
    CnfUnsatClosed neg A ↔ CnfClosed A ∧ UnsatClosed neg (unitsOf A) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.cnfUnsatClosed_iff

theorem unsatClosed_unitsOf (h : CnfUnsatClosed neg A) : UnsatClosed neg (unitsOf A) :=
  (cnfUnsatClosed_iff.1 h).2

theorem cnfUnsatClosed_cnfOf (h : UnsatClosed neg U) : CnfUnsatClosed neg (cnfOf U) :=
  cnfUnsatClosed_iff.2 ⟨cnfClosed_cnfOf U, (unitsOf_cnfOf h.up).symm ▸ h⟩

/-- `UnsatClosed` acceptors are CNF-UNSAT-closed CNF acceptors. -/
def cnfUnsatEquiv (neg : C → C) :
    {U : List C → Prop // UnsatClosed neg U} ≃o
      {A : List (List C) → Prop // CnfUnsatClosed neg A} where
  toFun U := ⟨cnfOf U.1, cnfUnsatClosed_cnfOf U.2⟩
  invFun A := ⟨unitsOf A.1, unsatClosed_unitsOf A.2⟩
  left_inv U := Subtype.ext (unitsOf_cnfOf U.2.up)
  right_inv A := Subtype.ext (cnfOf_unitsOf A.2.toCnfClosed)
  map_rel_iff' {U U'} :=
    ⟨fun h => by
        have := unitsOf_mono (A := cnfOf U.1) (A' := cnfOf U'.1) h
        rwa [unitsOf_cnfOf U.2.up, unitsOf_cnfOf U'.2.up] at this,
      fun h => cnfOf_mono h⟩

/-- Gentzen calculi with both negation rules are CNF-UNSAT acceptors. -/
def gentzenCnfEquiv (neg : C → C) :
    {S : Seq C // GentzenClosed neg S} ≃o {A : List (List C) → Prop // CnfUnsatClosed neg A} :=
  (unsatEquiv neg).trans (cnfUnsatEquiv neg)

theorem gentzenCnfEquiv_apply (S : {S : Seq C // GentzenClosed neg S}) :
    (gentzenCnfEquiv neg S).1 = cnfOf (toUnsat S.1) := rfl

theorem gentzenCnfEquiv_symm_apply (A : {A : List (List C) → Prop // CnfUnsatClosed neg A}) :
    ((gentzenCnfEquiv neg).symm A).1 = viaUnsat (unitsOf A.1) neg := rfl

end Cnf

/-! ## Semantics -/

section Semantics

variable {M : Type v} {sat : M → C → Prop}

theorem cnfSat_units {m : M} {Γ : List C} : CnfSat sat m (units Γ) ↔ SatAll sat m Γ :=
  Proofs.Logic.Consequence.Gentzen.Clausal.cnfSat_units

theorem cnfUnsat_closed : CnfClosed (CnfUnsat sat) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.cnfUnsat_closed

theorem cnfUnsat_unsatClosed (hs : NegSound sat neg) (hc : NegComplete sat neg) :
    CnfUnsatClosed neg (CnfUnsat sat) :=
  { cnfUnsat_closed with
    complement := Proofs.Logic.Consequence.Gentzen.Clausal.cnfUnsat_complement hs
    unitCut := fun _ _ _ h₁ h₂ => Proofs.Logic.Consequence.Gentzen.Clausal.cnfUnsat_unitCut hc h₁ h₂ }

theorem unitsOf_cnfUnsat : unitsOf (CnfUnsat sat) = Unsat sat :=
  Proofs.Logic.Consequence.Gentzen.Clausal.unitsOf_cnfUnsat

theorem cnfOf_unsat : cnfOf (Unsat sat) = CnfUnsat sat := by
  rw [← unitsOf_cnfUnsat, cnfOf_unitsOf cnfUnsat_closed]

theorem toUnsat_valid : toUnsat (Valid sat) = Unsat sat := by
  funext Γ; exact propext unsat_iff_valid_nil.symm

/-- The CNF image of the validity calculus is CNF unsatisfiability. -/
theorem cnfOf_toUnsat_valid : cnfOf (toUnsat (Valid sat)) = CnfUnsat sat := by
  rw [toUnsat_valid, cnfOf_unsat]

theorem cnfSound_cnfOf {U : List C → Prop} (h : CheckSound sat U) : CnfSound sat (cnfOf U) :=
  fun F hF => cnfOf_unsat (sat := sat) ▸ cnfOf_mono (fun Γ hΓ => h Γ hΓ) F hF

theorem checkSound_unitsOf {A : List (List C) → Prop} (h : CnfSound sat A) :
    CheckSound sat (unitsOf A) :=
  fun _ hΓ => unitsOf_cnfUnsat (sat := sat) ▸ h _ hΓ

/-- A sound CNF acceptor, read through units and `neg`, only derives valid sequents. -/
theorem viaUnsat_unitsOf_le_valid {A : List (List C) → Prop} (h : CnfSound sat A)
    (hn : NegComplete sat neg) : viaUnsat (unitsOf A) neg ≤ Valid sat :=
  viaUnsat_le_valid (checkSound_unitsOf h) hn

end Semantics

/-! ## Signed formulas -/

section Signed

variable {A : Type u}

theorem signedUnsat_iff {S : Seq A} {Γ : List (Signed A)} :
    signedUnsat S Γ ↔ S (posAtoms Γ) (negAtoms Γ) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.signedUnsat_iff

theorem gentzenClosed_signedLift {S : Seq A} (hS : Closed defaultRules S) :
    GentzenClosed (fun x => -x) (signedLift S) :=
  Proofs.Logic.Consequence.Gentzen.Clausal.gentzenClosed_signedLift hS

theorem unsatClosed_signedUnsat {S : Seq A} (hS : Closed defaultRules S) :
    UnsatClosed (fun x => -x) (signedUnsat S) :=
  unsatClosed_toUnsat (gentzenClosed_signedLift hS)

theorem closed_atomSeq {U : List (Signed A) → Prop} (hU : UnsatClosed (fun x => -x) U) :
    Closed defaultRules (atomSeq U) :=
  closed_posPart (gentzenClosed_viaUnsat hU).1

/-- Reading a sequent relation on atoms as a signed UNSAT acceptor loses nothing. -/
theorem atomSeq_signedUnsat (S : Seq A) : atomSeq (signedUnsat S) = S :=
  Proofs.Logic.Consequence.Gentzen.Clausal.atomSeq_signedUnsat S

theorem signedUnsat_atomSeq {U : List (Signed A) → Prop} (hU : ListPred.UpClosed U) :
    signedUnsat (atomSeq U) = U :=
  Proofs.Logic.Consequence.Gentzen.Clausal.signedUnsat_atomSeq hU

/-- Calculi on atoms are `UnsatClosed` acceptors of signed lists. -/
def signedEquiv (A : Type u) :
    {S : Seq A // Closed defaultRules S} ≃o
      {U : List (Signed A) → Prop // UnsatClosed (fun x => -x) U} where
  toFun S := ⟨signedUnsat S.1, unsatClosed_signedUnsat S.2⟩
  invFun U := ⟨atomSeq U.1, closed_atomSeq U.2⟩
  left_inv S := Subtype.ext (atomSeq_signedUnsat S.1)
  right_inv U := Subtype.ext (signedUnsat_atomSeq U.2.up)
  map_rel_iff' {S T} :=
    ⟨fun h Γ Δ hS => by
        rw [← atomSeq_signedUnsat T.1]
        rw [← atomSeq_signedUnsat S.1] at hS
        exact h _ hS,
      fun h Γ hS => signedUnsat_iff.2 (h _ _ (signedUnsat_iff.1 hS))⟩

/-- Calculi on atoms are CNF-UNSAT acceptors of signed clauses. -/
def signedCnfEquiv (A : Type u) :
    {S : Seq A // Closed defaultRules S} ≃o
      {F : List (List (Signed A)) → Prop // CnfUnsatClosed (fun x => -x) F} :=
  (signedEquiv A).trans (cnfUnsatEquiv _)

theorem signedCnfEquiv_apply (S : {S : Seq A // Closed defaultRules S}) :
    (signedCnfEquiv A S).1 = cnfOf (signedUnsat S.1) := rfl

theorem signedUnsat_valid {M : Type v} (τ : M → A → Prop) :
    signedUnsat (Valid τ) = Unsat (signedSat τ) := by
  unfold signedUnsat; rw [signedLift_valid, toUnsat_valid]

theorem cnfOf_signedUnsat_valid {M : Type v} (τ : M → A → Prop) :
    cnfOf (signedUnsat (Valid τ)) = CnfUnsat (signedSat τ) := by
  rw [signedUnsat_valid, cnfOf_unsat]

end Signed

end Silmaril.Consequence.Gentzen.Clausal
