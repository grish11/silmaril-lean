module

public import Silmaril.Semantics.Naming.NegativeCache.Defs

public section

namespace Silmaril.Proofs.Semantics.Naming

open Silmaril.Semantics.Naming NegativeCache

variable {Name Wire Parsed Node : Type} {policy : Relation Name Wire}
variable {source : Source policy} {profile : Profile Wire Parsed Node} {name : Name}

theorem wire_rejection_iff {wire : Wire} : profile.inspect wire = .error .wire ↔ profile.parse? wire = none := by
  unfold Profile.inspect
  cases parsed : profile.parse? wire with
  | none => simp
  | some value => cases checked : profile.node? value <;> simp [checked]

theorem node_rejection_iff {wire : Wire} : profile.inspect wire = .error .node ↔
    ∃ parsed, profile.parse? wire = some parsed ∧ profile.node? parsed = none := by
  unfold Profile.inspect
  cases parsed : profile.parse? wire with
  | none => simp
  | some value => cases checked : profile.node? value <;> simp [checked]

theorem cache_step_found [DecidableEq Name] (cache : Cache source profile) {verified : Verified source name} {node : Node}
    (accepted : profile.inspect verified.val = .ok node) : cache.step name (.ok verified) = (.found node, cache) := by
  simp only [Cache.step]
  split
  · rename_i found checked
    cases Except.ok.inj (checked.symm.trans accepted)
    rfl
  · rename_i cause checked
    cases checked.symm.trans accepted

theorem cache_step_invalid_iff [DecidableEq Name] {cache : Cache source profile} {input : Input source name} {cause : Cause} :
    (cache.step name input).1 = .invalid cause ↔
      ∃ verified : Verified source name, input = .ok verified ∧ profile.inspect verified.val = .error cause := by
  cases input with
  | error _ => simp [Cache.step]
  | ok verified =>
    simp only [Cache.step, Except.ok.injEq, exists_eq_left']
    split <;> rename_i value checked <;> simp [checked]

theorem cache_step_invalid [DecidableEq Name] {cache : Cache source profile} {input : Input source name} {cause : Cause}
    (invalid : (cache.step name input).1 = .invalid cause) : (cache.step name input).2.lookup name = some cause := by
  cases input with
  | error issue => cases invalid
  | ok verified =>
    simp only [Cache.step] at invalid ⊢
    revert invalid
    split
    · intro invalid; cases invalid
    · intro invalid; cases invalid
      simp [Cache.lookup, Cache.insert]

end Silmaril.Proofs.Semantics.Naming
