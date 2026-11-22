module

public import Silmaril.Formats.PER.Dense.Parent.Defs

public section

namespace Silmaril.Proofs.Formats.PERDenseParent

open Silmaril.Formats PER Dense

variable {Row : Nat → Type} {Key : Type} {parent : Key → Option Key} {mode : Parent.Convention}

theorem valid_iff (raw : Pointers Row) : raw.Valid ↔
    ∀ row ∈ raw.table.rows, ∀ target, raw.address row = some target → target < raw.table.size := by
  rw [Pointers.Valid, List.all_eq_true]
  constructor
  · intro all row member target hit
    simpa [hit] using all row member
  · intro ranges row member
    cases hit : raw.address row with
    | none => rfl
    | some target => simpa [hit] using ranges row member target hit

theorem parent_none (checked : Pointers.Checked Row) (key : Fin checked.val.table.size) :
    checked.parent key = none ↔ checked.val.address (checked.val.table.at key) = none := by
  rw [Pointers.Checked.parent, Pointers.observe, checked.val.table.read_at key]
  cases hit : checked.val.address (checked.val.table.at key) with
  | none => simp [hit, Observation.target?]
  | some target =>
    have member : checked.val.table.at key ∈ checked.val.table.rows := List.get_mem _ _
    have bound := (valid_iff checked.val).mp checked.property _ member _ hit
    simp [hit, bound, Observation.target?]

theorem observe_invalid (raw : Pointers Row) (source target : Nat) : raw.observe source = .invalid target ↔
    ∃ row, raw.table.read? source = some row ∧ raw.address row = some target ∧ raw.table.size ≤ target := by
  cases read : raw.table.read? source with
  | none => simp [Pointers.observe, read]
  | some row =>
    cases address : raw.address row with
    | none => simp [Pointers.observe, read, address]
    | some found =>
      by_cases same : found = target
      · subst target
        by_cases bound : found < raw.table.size
        · simp [Pointers.observe, read, address, bound]
        · simp [Pointers.observe, read, address, bound, Nat.le_of_not_gt bound]
      · by_cases bound : found < raw.table.size <;> simp [Pointers.observe, read, address, bound, same]

theorem ofFin_valid (table : Table (fun size => Option (Fin size))) : (Pointers.ofFin table).Valid := by
  apply (valid_iff _).mpr
  intro row _ target read
  obtain ⟨index, _, found⟩ := Option.map_eq_some_iff.mp read
  exact found ▸ index.isLt

theorem observe_unknown (raw : Pointers Row) (key : Nat) : raw.observe key = .unknown ↔ raw.table.size ≤ key := by
  rw [← raw.table.read_none key]
  cases read : raw.table.read? key with
  | none => simp [Pointers.observe, read]
  | some row =>
    cases address : raw.address row with
    | none => simp [Pointers.observe, read, address]
    | some target =>
      by_cases bound : target < raw.table.size <;> simp [Pointers.observe, read, address, bound]

theorem observe_missing (raw : Pointers Row) (key : Fin raw.table.size) :
    raw.observe key.val = .missing ↔ raw.address (raw.table.at key) = none := by
  rw [Pointers.observe, raw.table.read_at key]
  cases address : raw.address (raw.table.at key) with
  | none => simp [address]
  | some target => by_cases bound : target < raw.table.size <;> simp [address, bound]

theorem observe_edge (raw : Pointers Row) (source target : Fin raw.table.size) :
    raw.observe source.val = .edge target ↔ raw.address (raw.table.at source) = some target.val := by
  rw [Pointers.observe, raw.table.read_at source]
  cases address : raw.address (raw.table.at source) with
  | none => simp [address]
  | some found =>
    by_cases same : found = target.val
    · subst found; simp [address, target.isLt]
    · by_cases bound : found < raw.table.size
      · simp [address, bound, Fin.ext_iff, same]
      · simp [address, bound, same]

theorem reaches_connected {source root : Key} (path : Parent.Reaches mode parent source root) :
    Relation.EqvGen (fun key next => parent key = some next) source root := by
  induction path with
  | stop => exact .refl _
  | next hit _ rest => exact .trans _ _ _ (.rel _ _ hit.1) rest

theorem edge_reaches {source child root : Key} (edge : parent source = some child) :
    Parent.Reaches mode parent source root ↔ Parent.Reaches mode parent child root := by
  by_cases same : source = child
  · subst child; rfl
  refine ⟨?_, Parent.Reaches.next ⟨edge, same⟩⟩
  intro path
  cases path with
  | stop terminal =>
    cases mode with
    | fixedPoint => exact (same (Option.some.inj (terminal.symm.trans edge))).elim
    | terminalMissing => cases (show none = some child from terminal.symm.trans edge)
  | next step rest => exact Option.some.inj (step.1.symm.trans edge) ▸ rest

theorem connected_reaches {first second root : Key}
    (related : Relation.EqvGen (fun key next => parent key = some next) first second) :
    Parent.Reaches mode parent first root ↔ Parent.Reaches mode parent second root := by
  induction related with
  | rel _ _ edge => exact edge_reaches edge
  | refl => rfl
  | symm _ _ _ rest => exact rest.symm
  | trans _ _ _ _ _ left right => exact left.trans right

theorem partition_le_connectivity : Parent.partition mode parent ≤ Parent.connectivity parent := by
  intro left right edge
  obtain ⟨root, first, second⟩ := (Parent.rel_iff left right).mp edge
  exact ⟨.inl first.1, .inl second.1, .trans _ _ _ (reaches_connected first.2) (.symm _ _ (reaches_connected second.2))⟩

theorem connectivity_eq_on_keys
    (covered : ∀ key, (parent key).isSome → (Parent.partition mode parent).Dom key) :
    (Parent.connectivity parent).restrict (fun key => (parent key).isSome) = Parent.partition mode parent := by
  apply PER.ext
  intro left right
  constructor
  · rintro ⟨leftKnown, rightKnown, _, _, edge⟩
    obtain ⟨root, hit⟩ := (Parent.dom_iff left).mp (covered left leftKnown)
    exact (Parent.rel_iff left right).mpr ⟨root, hit, rightKnown, (connected_reaches edge).mp hit.2⟩
  · intro edge
    obtain ⟨_, first, second⟩ := (Parent.rel_iff left right).mp edge
    exact ⟨first.1, second.1, partition_le_connectivity edge⟩

theorem connectivity_fixed (forest : Parent.FixedForest parent) :
    Parent.connectivity parent = Parent.partition .fixedPoint parent := by
  rw [← connectivity_eq_on_keys (fun key => (Parent.fixed_dom forest key).mpr)]
  apply PER.ext
  intro left right
  refine ⟨fun edge => ⟨?_, ?_, edge⟩, fun restricted => restricted.2.2⟩
  · exact edge.1.elim id (fun ⟨_, hit⟩ => forest.knownTarget hit)
  · exact edge.2.1.elim id (fun ⟨_, hit⟩ => forest.knownTarget hit)

end Silmaril.Proofs.Formats.PERDenseParent
