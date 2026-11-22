module

public import Silmaril.Formats.PER.Parent.Defs
public import Silmaril.Formats.PER.Partition.Thms
import Silmaril.Proofs.Formats.PER.Parent

public section

namespace Silmaril.Formats.PER.Parent

variable {Key : Type} {parent : Key → Option Key} {mode : Convention}

theorem roots_functional : (Roots mode parent).Functional :=
  fun _ _ _ first second => Proofs.Formats.PERParent.reaches_unique first.2 second.2

theorem root_terminal {key root : Key} (hit : Roots mode parent key root) : Terminal mode parent root :=
  Proofs.Formats.PERParent.reaches_terminal hit.2

theorem rel_iff (left right : Key) : (partition mode parent).rel left right ↔
    ∃ root, Roots mode parent left root ∧ Roots mode parent right root := by
  change (Roots mode parent).per left right ↔ _
  rw [roots_functional.per_eq_same]
  rfl

theorem dom_iff (key : Key) : (partition mode parent).Dom key ↔ ∃ root, Roots mode parent key root :=
  (rel_iff key key).trans ⟨fun ⟨root, h, _⟩ => ⟨root, h⟩, fun ⟨root, h⟩ => ⟨root, h, h⟩⟩

theorem fixed_dom (forest : FixedForest parent) (key : Key) : (partition .fixedPoint parent).Dom key ↔
    (parent key).isSome := (dom_iff key).trans ⟨fun ⟨_, h⟩ => h.1, Proofs.Formats.PERParent.fixed_cover forest key⟩

theorem missing_dom (forest : MissingForest parent) (key : Key) : (partition .terminalMissing parent).Dom key ↔
    (parent key).isSome := (dom_iff key).trans ⟨fun ⟨_, h⟩ => h.1, Proofs.Formats.PERParent.missing_cover forest key⟩

/-- Normalize the chosen path interpretation, not the immediate parent fibers.
The caller supplies a decision procedure for that relation. -/
theorem canonical_partition [LinearOrder Key] (labels : Silmaril.Semantics.OrderedMap Key Key)
    (convention : Convention) [DecidableRel (partition convention labels.lookup?).rel] :
    fibers (Partition.canonicalOn labels.keySet (partition convention labels.lookup?)).lookup? =
      partition convention labels.lookup? :=
  Partition.canonicalOn_partition _ _ fun key supported =>
    (labels.mem_keySet key).mpr (let ⟨_, hit⟩ := (dom_iff key).mp supported; hit.1)

theorem fixed_flat (rooted : Rooted parent) : partition .fixedPoint parent = fibers parent :=
  PER.ext fun left right => (rel_iff left right).trans (by simp only [Proofs.Formats.PERParent.flat_roots _ rooted]; rfl)

theorem connectivity_dom (key : Key) : (connectivity parent).Dom key ↔ incident parent key :=
  ⟨fun h => h.1, fun h => ⟨h, h, .refl key⟩⟩

theorem edge_connected {key next : Key} (hit : parent key = some next) : (connectivity parent).rel key next :=
  ⟨Or.inl (Option.isSome_iff_exists.mpr ⟨next, hit⟩), Or.inr ⟨key, hit⟩, .rel key next hit⟩

end Silmaril.Formats.PER.Parent
