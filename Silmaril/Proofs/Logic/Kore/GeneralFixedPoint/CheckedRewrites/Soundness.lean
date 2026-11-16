module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.CheckedRewrites
open Silmaril.Logic Silmaril.Logic.Kore.GeneralFixedPoint
open Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites
open Predicates

variable {scope : Kore.Modules.Scope}

/-- Successful checking retains the raw source and its budget literally. -/
theorem checkValue_source {objects : Names} {sort : String} {fuel : Nat}
    {raw : RawPattern} {p : Value scope objects sort}
    (h : checkValue scope objects sort fuel raw = some p) :
    p.raw = raw ∧ p.fuel = fuel := by
  unfold checkValue at h
  split at h
  · contradiction
  · split at h
    · cases Option.some.inj h
      exact ⟨rfl, rfl⟩
    · contradiction

theorem checkValue_denote (M : Matching.GeneralFixedPoint.Model scope.signature)
    {objects : Names} {sort : String} {fuel : Nat} {raw : RawPattern}
    {p : Value scope objects sort}
    (h : checkValue scope objects sort fuel raw = some p) (a : Env M objects) :
    p.denote M a = rawValue M fuel objects a sort raw := by
  obtain ⟨source, budget⟩ := checkValue_source h
  simp only [Value.denote, rawValue, source, budget]

/-- Successful checking makes the original raw interpreter return `some`.
The empty fallback in `rawValue` cannot hide rejection on accepted operands. -/
theorem checkValue_raw_some (M : Matching.GeneralFixedPoint.Model scope.signature)
    {objects : Names} {sort : String} {fuel : Nat} {raw : RawPattern}
    {p : Value scope objects sort}
    (h : checkValue scope objects sort fuel raw = some p) (a : Env M objects) :
    Semantics.denote scope M fuel []
      (Semantics.interpret M objects (fun i => {a i})) sort raw =
        some (p.typed.denote M a (fun i => i.elim0)) := by
  obtain ⟨source, budget⟩ := checkValue_source h
  have result := Semantics.elaborate_sound M p.fuel [] objects sort p.raw p.typed
    a (fun i => i.elim0) p.accepted
  simpa only [source, budget, Semantics.interpret, Kore.FixedPoint.Semantics.interpret] using result

/-- Original raw guard truth agrees with the checked predicate, proved by
inverting actual successful checks, not assumed as a semantic certificate. -/
theorem checkPredicate_sound (M : Matching.GeneralFixedPoint.Model scope.signature)
    (fuel : Nat) (raw : BooleanTheory.RawPredicate) :
    ∀ (objects : Names) (p : Predicate scope objects),
      BooleanTheory.checkPredicate scope objects fuel raw = some p →
      ∀ a : Env M objects, rawPredicateTruth M fuel objects raw a ↔ p.truth M a := by
  induction raw with
  | top =>
      intro objects p h a
      cases Option.some.inj h
      rfl
  | bottom =>
      intro objects p h a
      cases Option.some.inj h
      rfl
  | equal sort left right =>
      intro objects p h a
      cases hl : checkValue scope objects sort fuel left with
      | none => simp [BooleanTheory.checkPredicate, hl] at h
      | some l =>
          cases hr : checkValue scope objects sort fuel right with
          | none => simp [BooleanTheory.checkPredicate, hl, hr] at h
          | some r =>
              simp only [BooleanTheory.checkPredicate, hl, hr] at h
              cases Option.some.inj h
              change _ ↔ l.denote M a = r.denote M a
              rw [checkValue_denote M hl, checkValue_denote M hr]
              rfl
  | member sort left right =>
      intro objects p h a
      cases hl : checkValue scope objects sort fuel left with
      | none => simp [BooleanTheory.checkPredicate, hl] at h
      | some l =>
          cases hr : checkValue scope objects sort fuel right with
          | none => simp [BooleanTheory.checkPredicate, hl, hr] at h
          | some r =>
              simp only [BooleanTheory.checkPredicate, hl, hr] at h
              cases Option.some.inj h
              change _ ↔ (l.denote M a ∩ r.denote M a).Nonempty
              rw [checkValue_denote M hl, checkValue_denote M hr]
              rfl
  | neg raw ih =>
      intro objects p h a
      cases hp : BooleanTheory.checkPredicate scope objects fuel raw with
      | none => simp [BooleanTheory.checkPredicate, hp] at h
      | some q =>
          simp only [BooleanTheory.checkPredicate, hp] at h
          cases Option.some.inj h
          exact not_congr (ih objects q hp a)
  | conj left right ihl ihr =>
      intro objects p h a
      cases hl : BooleanTheory.checkPredicate scope objects fuel left with
      | none => simp [BooleanTheory.checkPredicate, hl] at h
      | some l =>
          cases hr : BooleanTheory.checkPredicate scope objects fuel right with
          | none => simp [BooleanTheory.checkPredicate, hl, hr] at h
          | some r =>
              simp only [BooleanTheory.checkPredicate, hl, hr] at h
              cases Option.some.inj h
              exact and_congr (ihl objects l hl a) (ihr objects r hr a)
  | disj left right ihl ihr =>
      intro objects p h a
      cases hl : BooleanTheory.checkPredicate scope objects fuel left with
      | none => simp [BooleanTheory.checkPredicate, hl] at h
      | some l =>
          cases hr : BooleanTheory.checkPredicate scope objects fuel right with
          | none => simp [BooleanTheory.checkPredicate, hl, hr] at h
          | some r =>
              simp only [BooleanTheory.checkPredicate, hl, hr] at h
              cases Option.some.inj h
              exact or_congr (ihl objects l hl a) (ihr objects r hr a)
  | ex name bound raw ih =>
      intro objects p h a
      simp only [BooleanTheory.checkPredicate] at h
      split at h
      · cases hp : BooleanTheory.checkPredicate scope ((name, bound) :: objects) fuel raw with
        | none => simp [hp] at h
        | some q =>
            simp only [hp] at h
            cases Option.some.inj h
            exact exists_congr (fun x => ih ((name, bound) :: objects) q hp (Fin.cases x a))
      · contradiction

/-- The native LHS contains genuine conjunction and definedness-based predicate
syntax. Both equations below use raw interpreter adequacy. -/
theorem lowerLhs_iff (M : Matching.GeneralFixedPoint.Model scope.signature)
    {cfg : String} (r : CheckedRewrite scope cfg) (a : Env M r.objects) (w : M.carrier cfg) :
    w ∈ r.lowerLhs.denote (expand M) a (fun j => j.elim0) ↔
      w ∈ rawValue M r.fuel r.objects a cfg r.raw.lhs ∧
      rawPredicateTruth M r.fuel r.objects r.raw.guard a := by
  change (w ∈ r.lhs.lower.denote (expand M) a (fun j => j.elim0) ∧
    w ∈ (r.guard.lower cfg).denote (expand M) a (fun j => j.elim0)) ↔ _
  rw [Value.denote_lower, checkValue_denote M r.lhs_checked,
    Predicate.lower_adequate, ← checkPredicate_sound M r.fuel r.raw.guard r.objects r.guard r.guard_checked]
  rfl

theorem lowerRhs_iff (M : Matching.GeneralFixedPoint.Model scope.signature)
    {cfg : String} (r : CheckedRewrite scope cfg) (a : Env M r.objects) (w : M.carrier cfg) :
    w ∈ r.rhs.lower.denote (expand M) a (fun j => j.elim0) ↔
      w ∈ rawValue M r.fuel r.objects a cfg r.raw.rhs := by
  rw [Value.denote_lower, checkValue_denote M r.rhs_checked]
  rfl

/-- Exact raw/native step adequacy for every signature, admitted source model,
installed rule and rule valuation, preserving nondeterminism and overlap. -/
theorem induced_raw_iff_lowered {cfg : String} (sys : CheckedRewriteSystem scope cfg)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (w v : M.carrier cfg) :
    RawStep sys M w v ↔ Reachability.RuleSystem.Induced (lowerSchemes sys M) w v := by
  constructor
  · rintro ⟨i, a, lhs, guard, rhs⟩
    exact ⟨i, a, (lowerLhs_iff M _ a w).mpr ⟨lhs, guard⟩,
      (lowerRhs_iff M _ a v).mpr rhs⟩
  · rintro ⟨i, a, lhs, rhs⟩
    obtain ⟨left, guard⟩ := (lowerLhs_iff M _ a w).mp lhs
    exact ⟨i, a, left, guard, (lowerRhs_iff M _ a v).mp rhs⟩

theorem rawWellDefined_iff {cfg : String} (sys : CheckedRewriteSystem scope cfg)
    (M : Matching.GeneralFixedPoint.Model scope.signature) :
    RawWellDefined sys M ↔ Reachability.RuleSystem.WeaklyWellDefined (lowerSchemes sys M) := by
  constructor
  · intro h i a w lhs
    obtain ⟨left, guard⟩ := (lowerLhs_iff M _ a w).mp lhs
    obtain ⟨v, rhs⟩ := h i a w left guard
    exact ⟨v, (lowerRhs_iff M _ a v).mpr rhs⟩
  · intro h i a w left guard
    obtain ⟨v, rhs⟩ := h i a w ((lowerLhs_iff M _ a w).mpr ⟨left, guard⟩)
    exact ⟨v, (lowerRhs_iff M _ a v).mp rhs⟩

/-- The existing eight-rule semantic `Derives` calculus, instantiated with native
scheme semantics, proves finite-complete original raw paths. The claim is semantic;
this is not a parsed source-proof or `Native.Derives` correspondence. Claim captures
remain independent of each installed rule's finite environment. -/
theorem derivation_sound {cfg : String} (sys : CheckedRewriteSystem scope cfg)
    (M : Matching.GeneralFixedPoint.Model scope.signature)
    {J : Type} {D : J → Type}
    {c : Reachability.Derivation.Claim D (M.carrier cfg)}
    (d : Reachability.Derivation.Derives (lowerSchemes sys M) ∅ ∅ c)
    (wellDefined : RawWellDefined sys M) :
    ∀ a w, c.pre a w → Reachability.AllPartial (RawStep sys M) (c.post a) w := by
  have relation : RawStep sys M = Reachability.RuleSystem.Induced (lowerSchemes sys M) := by
    funext w v
    exact propext (induced_raw_iff_lowered sys M w v)
  rw [relation]
  exact d.sound ((rawWellDefined_iff sys M).mp wellDefined)

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.CheckedRewrites
