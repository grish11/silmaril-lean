module

public import Silmaril.Semantics.Prolly.Bounds.Tree.Defs
import Silmaril.Proofs.Semantics.Prolly.TreeBounds

public section

namespace Silmaril.Semantics.Prolly

open scoped BigOperators

variable {Sample Key Payload Name : Type}

/-- Let `D = denominator * width` and `C = 2 * denominator + width * numerator`.
The stopped frontier has one-step contraction when `C < D`. -/
theorem uniform_frontier_mass_succ [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {keys : List Key} {numerator denominator : Nat} (cap : model.FrontierCap keys numerator denominator) (steps : Nat) :
    (denominator * model.width) * model.frontierMass keys (steps + 1) ≤
      (2 * denominator + model.width * numerator) * model.frontierMass keys steps :=
  Proofs.Semantics.Prolly.TreeBounds.mass_succ cap steps

/-- In a nonempty uniform sample space, the expected number of unfolded
non-root blocks is at most `C / (D - C)` times the number of input entries.
This counts occurrences, not distinct CAS names, serialized bytes, or updates. -/
theorem uniform_build_occurrences [Fintype Sample] [LinearOrder Key] {model : UniformBuckets Sample Key}
    {map : OrderedMap Key Payload} {numerator denominator : Nat}
    (cap : model.FrontierCap (map.entries.map Prod.fst) numerator denominator)
    (contract : 2 * denominator + model.width * numerator < denominator * model.width)
    (address : Sample → Block Name Key Payload → Name) :
    (denominator * model.width - (2 * denominator + model.width * numerator)) *
        (∑ sample : Sample, let tree := build (model.policy sample) map
                            (blockOccurrences (address sample) tree.level tree.root).length - 1) ≤
      (2 * denominator + model.width * numerator) * (Fintype.card Sample * map.entries.length) :=
  Proofs.Semantics.Prolly.TreeBounds.build_occurrences cap contract address

/-- Scaled tail bound for the actual builder depth. When `C < D` and the
sample space is nonempty, `Pr[depth > steps] ≤ n / (width + 1) * (C / D)^steps`,
with division interpreted rationally. No independence or real-hash assumption. -/
theorem uniform_build_depth_tail [Fintype Sample] [LinearOrder Key] {model : UniformBuckets Sample Key}
    {map : OrderedMap Key Payload} {numerator denominator : Nat}
    (cap : model.FrontierCap (map.entries.map Prod.fst) numerator denominator) (steps : Nat) :
    (denominator * model.width)^steps *
        ((model.width + 1) * (Finset.univ.filter fun sample : Sample => steps < (build (model.policy sample) map).level).card) ≤
      (2 * denominator + model.width * numerator)^steps * (Fintype.card Sample * map.entries.length) :=
  Proofs.Semantics.Prolly.TreeBounds.build_depth_tail cap steps

end Silmaril.Semantics.Prolly
