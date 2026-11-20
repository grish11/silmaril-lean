module

public import Silmaril.Semantics.Prolly.Bounds.Defs
import Silmaril.Proofs.Semantics.Prolly.Bounds

public section

namespace Silmaril.Semantics.Prolly

open scoped BigOperators

variable {Sample Key : Type}

/-- Each nonfinal cut either pays its width in consumed keys or pays one bucket
hit. Charging both kinds of cut cannot undercount the number of chunks. -/
theorem chunk_count (policy : Policy Key) (level : Nat) (keys : List Key) :
    policy.width * (chunk (policy.cut level) keys).length ≤
      keys.length + policy.width * (keys.countP (policy.bucket level)) + policy.width :=
  Proofs.Semantics.Prolly.Bounds.chunk_count policy level keys

/-- A scaled upper bound on expected one-level chunk count in a nonempty uniform
sample space. `cap / card Sample` is a per-key upper bound on hit probability
(interpreting division rationally). Does not apply to key lists selected from
the same sample without a new conditional marginal bound. -/
theorem uniform_chunk_bound [Fintype Sample] (model : UniformBuckets Sample Key) (level : Nat)
    (keys : List Key) (cap : Nat) (marginal : ∀ key ∈ keys, model.hits level key ≤ cap) :
    (∑ sample : Sample, model.width * model.chunks sample level keys) ≤
      Fintype.card Sample * (keys.length + model.width) + model.width * (keys.length * cap) :=
  Proofs.Semantics.Prolly.Bounds.uniform_chunk_bound model level keys cap marginal

end Silmaril.Semantics.Prolly
