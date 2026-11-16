module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
open Predicates

theorem history_checked_owner {source ambient cfg fuel modules}
    (history : CheckedHistory source ambient cfg fuel modules) :
    ∀ (owner : CheckedModule ambient cfg), owner ∈ modules →
    ∃ earlier, owner.source ∈ source.modules ∧
      checkModule ambient cfg fuel earlier owner.source = some owner := by
  induction history with
  | empty => simp
  | @append earlier original checked history original_mem accepted ih =>
    intro owner member
    rcases List.mem_append.mp member with old | latest
    · exact ih owner old
    · have same : owner = checked := List.mem_singleton.mp latest
      subst checked
      have source_eq := (checkModule_source accepted).1
      refine ⟨earlier, ?_, ?_⟩
      · simpa only [source_eq] using original_mem
      · simpa only [source_eq] using accepted

theorem ClaimSelection.checked_owner {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p) :
    ∃ earlier, s.owner.source ∈ p.source.modules ∧
      checkModule p.definition.ambient cfg fuel earlier s.owner.source = some s.owner :=
  history_checked_owner (checkDefinition_history p.accepted) s.owner s.owner_mem

/-- Exact original parsed claim, with checker-computed kind, position, scope
and payload. None of this provenance is a caller-supplied invariant. -/
theorem ClaimSelection.source {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p) :
    s.owner.source ∈ p.source.modules ∧
    ∃ (d : Kore.Modules.LocatedDeclaration Raw) (i : Nat) (raw : Raw),
      (d, i) ∈ s.owner.source.declarations.zipIdx ∧ d.declaration = .claim raw ∧
      s.declaration.origin = ⟨s.owner.source.name, i⟩ ∧
      s.declaration.location = d.location ∧ s.declaration.isClaim = true ∧
      s.declaration.payload.source = raw ∧ s.declaration.payload.fuel = fuel ∧
      s.declaration.payload.declaringScope = s.owner.scope ∧
      checkPayload p.definition.ambient s.owner.scope cfg fuel raw =
        some s.declaration.payload ∧
      checkRewrite p.definition.ambient cfg fuel raw.rewrite =
        some s.declaration.payload.checked ∧
      visible s.owner.scope fuel raw = true := by
  obtain ⟨earlier, member, checked⟩ := s.checked_owner
  obtain ⟨d, i, raw, original, kind, origin, location, isClaim, rawSource,
    budget, scopeEq, payloadChecked⟩ := checkModule_local_claim_source checked s.claim_mem
  refine ⟨member, d, i, raw, original, kind, origin, location, isClaim,
    rawSource, budget, scopeEq, payloadChecked, ?_, ?_⟩
  · simpa only [rawSource, budget] using s.declaration.payload.accepted
  · simpa only [rawSource, budget, scopeEq] using s.declaration.payload.visible

/-- Successful smart construction preserves exact source operands and the
joint capture context; arbitrary CheckedRewrite records are not assumed to do so. -/
theorem checkRewrite_original {ambient cfg fuel raw} {r : CheckedRewrite ambient cfg}
    (h : checkRewrite ambient cfg fuel raw = some r) :
    r.raw = raw ∧ r.fuel = fuel ∧ r.objects = captures fuel raw := by
  unfold checkRewrite at h
  split at h
  · contradiction
  · split at h
    · dsimp only at h
      split at h
      · contradiction
      · split at h
        · cases Option.some.inj h
          exact ⟨rfl, rfl, rfl⟩
        · contradiction
    · contradiction

/-- The semantic claim really uses the retained original parsed operands. -/
theorem ClaimSelection.original_operands {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p) :
    s.declaration.payload.checked.raw = s.declaration.payload.source.rewrite ∧
    s.declaration.payload.checked.fuel = s.declaration.payload.fuel ∧
    s.declaration.payload.checked.objects =
      captures s.declaration.payload.fuel s.declaration.payload.source.rewrite :=
  checkRewrite_original s.declaration.payload.accepted

/-- Native endpoints execute checked lowerings. Both iff statements use
raw adequacy, including guard truth rather than a supplied endpoint equation. -/
theorem ClaimSelection.native_adequate {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p)
    (M : Matching.GeneralFixedPoint.Model p.definition.ambient.signature)
    (a : Env M s.declaration.payload.checked.objects) (w : M.carrier cfg) :
    (w ∈ s.declaration.payload.checked.lowerLhs.denote (expand M) a (fun j => j.elim0) ↔
      (s.meaning M).pre a w) ∧
    (w ∈ s.declaration.payload.checked.rhs.lower.denote (expand M) a (fun j => j.elim0) ↔
      (s.meaning M).post a w) :=
  ⟨lowerLhs_iff M _ a w, lowerRhs_iff M _ a w⟩

/-- Builds the existing real Step constructor, not a parallel calculus and
not a caller-supplied all-partial conclusion. -/
def ClaimSelection.step {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p)
    (M : Matching.GeneralFixedPoint.Model p.definition.ambient.signature)
    (h : s.StepObligations M) :
    Reachability.Derivation.Derives (lowerSchemes s.owner.system M) ∅ ∅ (s.meaning M) := by
  apply Reachability.Derivation.Derives.step
  · intro a w pre
    obtain ⟨i, b, lhs, guard⟩ := h.coverage a w pre
    exact ⟨i, b, (lowerLhs_iff M _ b w).mpr ⟨lhs, guard⟩⟩
  · intro a i b w v pre lhs rhs
    obtain ⟨rawLhs, guard⟩ := (lowerLhs_iff M _ b w).mp lhs
    exact h.closure a i b w v pre rawLhs guard ((lowerRhs_iff M _ b v).mp rhs)

theorem ClaimSelection.step_sound {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p)
    (M : Matching.GeneralFixedPoint.Model p.definition.ambient.signature)
    (h : s.StepObligations M) (total : RawWellDefined s.owner.system M) :
    ∀ a w, (s.meaning M).pre a w →
      Reachability.AllPartial (RawStep s.owner.system M) ((s.meaning M).post a) w :=
  derivation_sound s.owner.system M (s.step M h) total

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
