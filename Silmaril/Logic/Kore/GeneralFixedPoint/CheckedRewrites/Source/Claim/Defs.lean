module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
open Predicates

/-- Selection carries actual accepted-package and claim-list membership.
It neither installs the claim nor assumes its validity. -/
structure ClaimSelection {cfg fuel text} (p : Package cfg fuel text) where
  owner : CheckedModule p.definition.ambient cfg
  owner_mem : owner ∈ p.definition.modules
  declaration : LocatedRule p.definition.ambient cfg
  claim_mem : declaration ∈ owner.claims

/-- The context is jointly extracted by checkRewrite, including RHS-only and
 guard-only captures. The guard constrains the initial state only. -/
def ClaimSelection.meaning {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p)
    (M : Matching.GeneralFixedPoint.Model p.definition.ambient.signature) :
    Reachability.Derivation.Claim
      (fun i => M.carrier (context s.declaration.payload.checked.objects i)) (M.carrier cfg) :=
  let r := s.declaration.payload.checked
  ⟨(fun a w => w ∈ rawValue M r.fuel r.objects a cfg r.raw.lhs ∧
      rawPredicateTruth M r.fuel r.objects r.raw.guard a),
    (fun a w => w ∈ rawValue M r.fuel r.objects a cfg r.raw.rhs)⟩

/-- Actual Step-rule obligations in independent source semantics. Coverage
selects a source rule and its own assignment. Closure checks ALL installed
rule instances, with the SAME claim assignment at both endpoints. -/
structure ClaimSelection.StepObligations {cfg fuel text} {p : Package cfg fuel text}
    (s : ClaimSelection p)
    (M : Matching.GeneralFixedPoint.Model p.definition.ambient.signature) : Prop where
  coverage : ∀ a w, (s.meaning M).pre a w →
    ∃ i : Fin s.owner.system.rules.length,
    ∃ b : Env M s.owner.system.rules[i].checked.objects,
      w ∈ rawValue M s.owner.system.rules[i].checked.fuel
        s.owner.system.rules[i].checked.objects b cfg s.owner.system.rules[i].checked.raw.lhs ∧
      rawPredicateTruth M s.owner.system.rules[i].checked.fuel
        s.owner.system.rules[i].checked.objects s.owner.system.rules[i].checked.raw.guard b
  closure : ∀ a (i : Fin s.owner.system.rules.length)
      (b : Env M s.owner.system.rules[i].checked.objects) w v,
    (s.meaning M).pre a w →
    w ∈ rawValue M s.owner.system.rules[i].checked.fuel
      s.owner.system.rules[i].checked.objects b cfg s.owner.system.rules[i].checked.raw.lhs →
    rawPredicateTruth M s.owner.system.rules[i].checked.fuel
      s.owner.system.rules[i].checked.objects s.owner.system.rules[i].checked.raw.guard b →
    v ∈ rawValue M s.owner.system.rules[i].checked.fuel
      s.owner.system.rules[i].checked.objects b cfg s.owner.system.rules[i].checked.raw.rhs →
    (s.meaning M).post a v

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
