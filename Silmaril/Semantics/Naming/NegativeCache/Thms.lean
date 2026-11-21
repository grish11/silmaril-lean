module

public import Silmaril.Semantics.Naming.NegativeCache.Defs
import Silmaril.Proofs.Semantics.Naming.NegativeCache

public section

namespace Silmaril.Semantics.Naming.NegativeCache

variable {Name Wire Parsed Node : Type} {policy : Relation Name Wire}
variable {source extended : Source policy} {profile : Profile Wire Parsed Node} {name : Name}

theorem Profile.wire_rejection_iff {wire : Wire} : profile.inspect wire = .error .wire ↔ profile.parse? wire = none :=
  Proofs.Semantics.Naming.wire_rejection_iff

theorem Profile.node_rejection_iff {wire : Wire} : profile.inspect wire = .error .node ↔
    ∃ parsed, profile.parse? wire = some parsed ∧ profile.node? parsed = none :=
  Proofs.Semantics.Naming.node_rejection_iff

theorem Cache.lookup_sound {cache : Cache source profile} {cause : Cause} (hit : cache.lookup name = some cause) :
    ∃ wire, source.bindings name wire ∧ policy name wire ∧ profile.inspect wire = .error cause := by
  obtain ⟨entry, _, rfl⟩ := Option.map_eq_some_iff.mp hit
  exact ⟨entry.verified.val, entry.verified.property, source.compatible entry.verified.property, entry.checked⟩

@[simp] theorem Cache.step_deferred [DecidableEq Name] (cache : Cache source profile) (name : Name) (issue : Deferred) :
    cache.step name (.error issue) = (.deferred issue, cache) := rfl

theorem Cache.step_found [DecidableEq Name] (cache : Cache source profile) {verified : Verified source name} {node : Node}
    (accepted : profile.inspect verified.val = .ok node) : cache.step name (.ok verified) = (.found node, cache) :=
  Proofs.Semantics.Naming.cache_step_found cache accepted

theorem Cache.step_invalid_iff [DecidableEq Name] {cache : Cache source profile} {input : Input source name} {cause : Cause} :
    (cache.step name input).1 = .invalid cause ↔
      ∃ verified : Verified source name, input = .ok verified ∧ profile.inspect verified.val = .error cause :=
  Proofs.Semantics.Naming.cache_step_invalid_iff

/-- Every fresh invalid outcome leaves a certificate for the requested key. -/
theorem Cache.step_invalid_sound [DecidableEq Name] {cache : Cache source profile} {input : Input source name} {cause : Cause}
    (invalid : (cache.step name input).1 = .invalid cause) : (cache.step name input).2.lookup name = some cause :=
  Proofs.Semantics.Naming.cache_step_invalid invalid

@[simp] theorem Cache.lookup_extend (cache : Cache source profile) (included : Subset source.bindings extended.bindings)
    (name : Name) : (cache.extend included).lookup name = cache.lookup name := by
  unfold Cache.lookup Cache.extend
  cases cache name <;> rfl

/-- An accepted wire at a rejected key must be different bytes. If it is
claimed to bind that key too, the combined source cannot be binding. -/
theorem Rejection.accepted_bytes_ne (entry : Rejection source profile name) {wire : Wire} {node : Node}
    (accepted : profile.inspect wire = .ok node) : wire ≠ entry.verified.val :=
  fun equal => by rw [equal, entry.checked] at accepted; cases accepted

theorem Rejection.no_accepted_in_extension (entry : Rejection source profile name)
    {candidate : Relation Name Wire} (included : Subset source.bindings candidate) (bound : Binding candidate)
    {wire : Wire} {node : Node} (hit : candidate name wire) : profile.inspect wire ≠ .ok node :=
  fun accepted => entry.accepted_bytes_ne accepted (bound hit (included entry.verified.property))

end Silmaril.Semantics.Naming.NegativeCache
